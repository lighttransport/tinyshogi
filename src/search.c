#define _POSIX_C_SOURCE 200809L

#include "search.h"
#include "thread.h"

#include <math.h>
#include <sched.h>
#include <stdatomic.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>
#include <unistd.h>

#define SEARCH_MAX_PATH 512
#define SEARCH_MAX_UNDO 2048
#define DEFAULT_MAX_TREE_NODES 1000000U
#define VALUE_SCALE UINT64_C(1000000)

typedef struct TreeNode TreeNode;

typedef struct {
    ShogiMove move;
    _Atomic(TreeNode *) node;
    atomic_uint_least64_t visits;
    atomic_uint_least64_t value;
    atomic_int virtual_loss;
} TreeChild;

struct TreeNode {
    uint64_t hash;
    atomic_bool expanded;
    atomic_flag expansion_lock;
    atomic_uint next_unexpanded;
    atomic_uint_least64_t visits;
    atomic_uint_least64_t value;
    unsigned move_count;
    ShogiMove *moves;
    TreeChild *children;
};

typedef struct {
    TreeNode *nodes;
    size_t node_count;
    size_t node_capacity;
    TsMutex expansion_mutex;
} SearchTree;

struct SearchJob {
    ShogiPosition root_position;
    SearchLimits limits;
    SearchOptions options;
    SearchTree tree;
    TreeNode *root;
    TsThread *workers;
    unsigned worker_count;
    atomic_bool stop;
    atomic_bool pondering;
    atomic_uint workers_done;
    atomic_uint_least64_t simulations;
    atomic_uint_least64_t deadline_ns;
    uint64_t start_ns;
    ShogiColor root_side;
    SearchResult result;
    bool joined;
};

typedef struct {
    SearchJob *job;
    unsigned id;
} WorkerArgument;

static uint64_t monotonic_ns(void) {
    struct timespec time;
    clock_gettime(CLOCK_MONOTONIC, &time);
    return (uint64_t)time.tv_sec * UINT64_C(1000000000) + (uint64_t)time.tv_nsec;
}

static uint64_t rng_next(uint64_t *state) {
    uint64_t value = (*state += UINT64_C(0x9e3779b97f4a7c15));
    value = (value ^ (value >> 30)) * UINT64_C(0xbf58476d1ce4e5b9);
    value = (value ^ (value >> 27)) * UINT64_C(0x94d049bb133111eb);
    return value ^ (value >> 31);
}

static bool same_search_move(ShogiMove left, ShogiMove right) {
    return left.from == right.from && left.to == right.to &&
           left.promote == right.promote && left.drop == right.drop;
}

static bool should_stop(const SearchJob *job) {
    if (atomic_load_explicit(&job->stop, memory_order_relaxed)) return true;
    uint64_t deadline = atomic_load_explicit(&job->deadline_ns, memory_order_acquire);
    if (deadline != 0 && monotonic_ns() >= deadline) return true;
    if (job->limits.nodes != 0 && atomic_load_explicit(&job->simulations, memory_order_relaxed) >= job->limits.nodes) return true;
    return false;
}

static void tree_free_node(TreeNode *node) {
    if (node == NULL) return;
    free(node->moves);
    free(node->children);
}

static void tree_destroy(SearchTree *tree) {
    if (tree == NULL) return;
    for (size_t index = 0; index < tree->node_count; ++index) tree_free_node(&tree->nodes[index]);
    free(tree->nodes);
    ts_mutex_destroy(&tree->expansion_mutex);
    memset(tree, 0, sizeof(*tree));
}

static TreeNode *tree_new_node(SearchTree *tree, uint64_t hash) {
    TreeNode *node = NULL;
    ts_mutex_lock(&tree->expansion_mutex);
    if (tree->node_count < tree->node_capacity) {
        node = &tree->nodes[tree->node_count++];
        memset(node, 0, sizeof(*node));
        node->hash = hash;
        atomic_init(&node->expanded, false);
        atomic_flag_clear(&node->expansion_lock);
        atomic_init(&node->next_unexpanded, 0);
        atomic_init(&node->visits, 0);
        atomic_init(&node->value, 0);
    }
    ts_mutex_unlock(&tree->expansion_mutex);
    return node;
}

static bool node_expand(SearchTree *tree, TreeNode *node, const ShogiPosition *position,
                        const ShogiMove *moves, size_t move_count) {
    if (atomic_load_explicit(&node->expanded, memory_order_acquire)) return true;
    bool success = true;
    while (atomic_flag_test_and_set_explicit(&node->expansion_lock, memory_order_acquire)) sched_yield();
    if (!atomic_load_explicit(&node->expanded, memory_order_relaxed)) {
        node->move_count = (unsigned)move_count;
        if (move_count != 0) {
            node->moves = malloc(move_count * sizeof(*node->moves));
            node->children = calloc(move_count, sizeof(*node->children));
            if (node->moves == NULL || node->children == NULL) {
                free(node->moves);
                free(node->children);
                node->moves = NULL;
                node->children = NULL;
                node->move_count = 0;
                success = false;
            } else {
                memcpy(node->moves, moves, move_count * sizeof(*moves));
                for (size_t index = 0; index < move_count; ++index) {
                    node->children[index].move = moves[index];
                    atomic_init(&node->children[index].node, NULL);
                    atomic_init(&node->children[index].visits, 0);
                    atomic_init(&node->children[index].value, 0);
                    atomic_init(&node->children[index].virtual_loss, 0);
                }
            }
        }
        (void)position;
        atomic_store_explicit(&node->expanded, true, memory_order_release);
    }
    atomic_flag_clear_explicit(&node->expansion_lock, memory_order_release);
    (void)tree;
    return success;
}

static double child_score(const SearchJob *job, const TreeNode *parent, const TreeChild *child, bool maximizing) {
    uint64_t parent_visits = atomic_load_explicit(&parent->visits, memory_order_relaxed);
    uint64_t visits = atomic_load_explicit(&child->visits, memory_order_relaxed);
    int virtual_loss = atomic_load_explicit(&child->virtual_loss, memory_order_relaxed);
    double effective_visits = (double)(visits + (uint64_t)(virtual_loss > 0 ? virtual_loss : 0));
    uint64_t value = atomic_load_explicit(&child->value, memory_order_relaxed);
    double mean = effective_visits > 0.0 ? (double)value / (effective_visits * (double)VALUE_SCALE) : 0.5;
    if (!maximizing) mean = 1.0 - mean;
    double exploration_constant = (double)job->options.exploration_milli / 1000.0;
    double exploration = exploration_constant * sqrt(log((double)parent_visits + 1.0) / (effective_visits + 1.0));
    return mean + exploration;
}

static TreeChild *select_child(const SearchJob *job, TreeNode *node, bool maximizing) {
    TreeChild *best = NULL;
    double best_score = -1.0;
    for (unsigned index = 0; index < node->move_count; ++index) {
        TreeChild *child = &node->children[index];
        if (atomic_load_explicit(&child->node, memory_order_acquire) == NULL) continue;
        double score = child_score(job, node, child, maximizing);
        if (best == NULL || score > best_score) {
            best = child;
            best_score = score;
        }
    }
    if (best != NULL) atomic_fetch_add_explicit(&best->virtual_loss, 1, memory_order_relaxed);
    return best;
}

static TreeChild *expand_one(SearchJob *job, TreeNode *node, ShogiPosition *position,
                             ShogiUndo *undo) {
    ts_mutex_lock(&job->tree.expansion_mutex);
    unsigned index = atomic_load_explicit(&node->next_unexpanded, memory_order_relaxed);
    if (index >= node->move_count) {
        ts_mutex_unlock(&job->tree.expansion_mutex);
        return NULL;
    }
    atomic_store_explicit(&node->next_unexpanded, index + 1, memory_order_relaxed);
    TreeChild *child = &node->children[index];
    TreeNode *child_node = atomic_load_explicit(&child->node, memory_order_relaxed);
    if (child_node == NULL) {
        if (job->tree.node_count < job->tree.node_capacity) {
            child_node = &job->tree.nodes[job->tree.node_count++];
            memset(child_node, 0, sizeof(*child_node));
            if (!shogi_make_move_undo(position, child->move, undo)) {
                --job->tree.node_count;
                child_node = NULL;
            }
            if (child_node != NULL) {
                child_node->hash = position->hash;
                atomic_init(&child_node->expanded, false);
                atomic_flag_clear(&child_node->expansion_lock);
                atomic_init(&child_node->next_unexpanded, 0);
                atomic_init(&child_node->visits, 0);
                atomic_init(&child_node->value, 0);
            }
        }
        atomic_store_explicit(&child->node, child_node, memory_order_release);
    }
    ts_mutex_unlock(&job->tree.expansion_mutex);
    return child_node == NULL ? NULL : child;
}

static int piece_value(ShogiPieceType type) {
    switch (type) {
    case SHOGI_PAWN: return 100;
    case SHOGI_LANCE: return 300;
    case SHOGI_KNIGHT: return 320;
    case SHOGI_SILVER: return 450;
    case SHOGI_GOLD: return 550;
    case SHOGI_BISHOP: return 800;
    case SHOGI_ROOK: return 1000;
    case SHOGI_PRO_PAWN:
    case SHOGI_PRO_LANCE:
    case SHOGI_PRO_KNIGHT:
    case SHOGI_PRO_SILVER: return 550;
    case SHOGI_HORSE: return 950;
    case SHOGI_DRAGON: return 1200;
    default: return 0;
    }
}

static int static_evaluation(const ShogiPosition *position, ShogiColor perspective) {
    int score = 0;
    for (size_t square = 0; square < SHOGI_SQUARES; ++square) {
        uint8_t piece = position->board[square];
        if (piece == SHOGI_EMPTY || shogi_piece_type(piece) == SHOGI_KING) continue;
        int value = piece_value(shogi_piece_type(piece));
        score += shogi_piece_color(piece) == perspective ? value : -value;
    }
    for (int hand = 0; hand < 7; ++hand) {
        ShogiPieceType type = (ShogiPieceType)(hand + 1);
        int value = piece_value(type);
        score += (int)position->hand[perspective][hand] * value;
        score -= (int)position->hand[perspective ^ 1][hand] * value;
    }
    ShogiMove moves[SHOGI_MAX_MOVES];
    ShogiPosition own = *position;
    own.side = perspective;
    size_t own_moves = shogi_generate_pseudo(&own, moves, SHOGI_MAX_MOVES);
    ShogiPosition other = *position;
    other.side = (ShogiColor)(perspective ^ 1);
    size_t opponent_moves = shogi_generate_pseudo(&other, moves, SHOGI_MAX_MOVES);
    score += (int)(own_moves * 5U);
    score -= (int)(opponent_moves * 5U);
    if (score > 1500) score = 1500;
    if (score < -1500) score = -1500;
    return score;
}

static unsigned rollout_move_weight(const ShogiPosition *position, ShogiMove move) {
    unsigned weight = 1;
    if (move.from == SHOGI_SQ_NONE) return 2;
    uint8_t captured = position->board[move.to];
    if (captured != SHOGI_EMPTY) {
        int value = piece_value(shogi_piece_type(captured));
        weight += 4U + (unsigned)(value > 0 ? value / 200 : 0);
    }
    if (move.promote) weight += 4;
    return weight;
}

typedef struct {
    TreeChild *edges[SEARCH_MAX_PATH];
    size_t length;
} SearchPath;

static void backpropagate(SearchJob *job, const SearchPath *path, double value);

static double rollout(SearchJob *job, ShogiPosition *position, ShogiUndo *undos,
                      size_t *undo_length, uint64_t *rng) {
    int rollout_depth = job->limits.depth > 0 ? job->limits.depth : (int)job->options.rollout_depth;
    for (int ply = 0; ply < rollout_depth; ++ply) {
        if (should_stop(job)) break;
        ShogiMove moves[SHOGI_MAX_MOVES];
        size_t count = 0;
        ShogiResult result = shogi_game_result_with_moves(position, moves, SHOGI_MAX_MOVES, &count);
        if (result != SHOGI_RESULT_ONGOING) {
            if (result == SHOGI_RESULT_DRAW) return 0.5;
            return result == (job->root_side == SHOGI_BLACK ? SHOGI_RESULT_BLACK_WIN : SHOGI_RESULT_WHITE_WIN) ? 1.0 : 0.0;
        }
        if (count == 0) break;
        unsigned total_weight = 0;
        for (size_t index = 0; index < count; ++index) total_weight += rollout_move_weight(position, moves[index]);
        unsigned selected_weight = (unsigned)(rng_next(rng) % total_weight);
        size_t choice = 0;
        for (; choice < count; ++choice) {
            unsigned weight = rollout_move_weight(position, moves[choice]);
            if (selected_weight < weight) break;
            selected_weight -= weight;
        }
        if (choice >= count) choice = count - 1;
        if (*undo_length >= SEARCH_MAX_UNDO ||
            !shogi_make_move_undo(position, moves[choice], &undos[*undo_length])) break;
        ++*undo_length;
    }
    int score = static_evaluation(position, job->root_side);
    return 0.5 + (double)score / 3000.0;
}

static double run_simulation(SearchJob *job, ShogiPosition *position,
                             ShogiUndo *undos, uint64_t *rng) {
    TreeNode *node = job->root;
    SearchPath path = {0};
    size_t undo_length = 0;

    double value = 0.5;
    bool terminal = false;
    for (int depth = 0; depth < SEARCH_MAX_PATH; ++depth) {
        if (should_stop(job)) break;
        ShogiMove moves[SHOGI_MAX_MOVES];
        size_t count = 0;
        ShogiResult result = shogi_game_result_with_moves(position, moves, SHOGI_MAX_MOVES, &count);
        if (result != SHOGI_RESULT_ONGOING) {
            if (result == SHOGI_RESULT_DRAW) value = 0.5;
            else value = result == (job->root_side == SHOGI_BLACK ? SHOGI_RESULT_BLACK_WIN : SHOGI_RESULT_WHITE_WIN) ? 1.0 : 0.0;
            terminal = true;
            break;
        }
        if (!node_expand(&job->tree, node, position, moves, count)) break;
        if (count == 0) break;

        TreeChild *expanded = expand_one(job, node, position, &undos[undo_length]);
        if (expanded != NULL) {
            ++undo_length;
            if (path.length >= SEARCH_MAX_PATH) break;
            atomic_fetch_add_explicit(&expanded->virtual_loss, 1, memory_order_relaxed);
            path.edges[path.length++] = expanded;
            TreeNode *next = atomic_load_explicit(&expanded->node, memory_order_acquire);
            if (next == NULL) break;
            node = next;
            break;
        }
        if (path.length >= SEARCH_MAX_PATH) break;
        TreeChild *selected = select_child(job, node, position->side == job->root_side);
        if (selected == NULL) break;
        path.edges[path.length++] = selected;
        if (undo_length >= SEARCH_MAX_UNDO ||
            !shogi_make_move_undo(position, selected->move, &undos[undo_length])) break;
        ++undo_length;
        TreeNode *next = atomic_load_explicit(&selected->node, memory_order_acquire);
        if (next == NULL) break;
        node = next;
    }

    if (!terminal) value = rollout(job, position, undos, &undo_length, rng);
    while (undo_length > 0) {
        --undo_length;
        (void)shogi_unmake_move(position, &undos[undo_length]);
    }
    backpropagate(job, &path, value);
    return value;
}

static void backpropagate(SearchJob *job, const SearchPath *path, double value) {
    uint64_t scaled = (uint64_t)(value * (double)VALUE_SCALE);
    atomic_fetch_add_explicit(&job->root->visits, 1, memory_order_relaxed);
    atomic_fetch_add_explicit(&job->root->value, scaled, memory_order_relaxed);
    for (size_t index = 0; index < path->length; ++index) {
        TreeChild *edge = path->edges[index];
        atomic_fetch_sub_explicit(&edge->virtual_loss, 1, memory_order_relaxed);
        atomic_fetch_add_explicit(&edge->visits, 1, memory_order_relaxed);
        atomic_fetch_add_explicit(&edge->value, scaled, memory_order_relaxed);
        TreeNode *node = atomic_load_explicit(&edge->node, memory_order_acquire);
        if (node != NULL) {
            atomic_fetch_add_explicit(&node->visits, 1, memory_order_relaxed);
            atomic_fetch_add_explicit(&node->value, scaled, memory_order_relaxed);
        }
    }
}

static void *worker_main(void *opaque) {
    WorkerArgument *argument = opaque;
    SearchJob *job = argument->job;
    uint64_t rng = job->options.seed_auto ? monotonic_ns() ^ ((uint64_t)argument->id * UINT64_C(0x9e3779b9))
                                          : job->options.seed + (uint64_t)argument->id * UINT64_C(0x9e3779b97f4a7c15);
    ShogiPosition position = job->root_position;
    ShogiUndo undos[SEARCH_MAX_UNDO];
    while (!should_stop(job)) {
        if (job->limits.nodes != 0) {
            uint64_t current = atomic_load_explicit(&job->simulations, memory_order_relaxed);
            bool claimed = false;
            while (current < job->limits.nodes) {
                if (atomic_compare_exchange_weak_explicit(&job->simulations, &current, current + 1,
                                                          memory_order_relaxed, memory_order_relaxed)) {
                    claimed = true;
                    break;
                }
            }
            if (!claimed) break;
        } else {
            atomic_fetch_add_explicit(&job->simulations, 1, memory_order_relaxed);
        }
        double value = run_simulation(job, &position, undos, &rng);
        (void)value;
    }
    atomic_fetch_add_explicit(&job->workers_done, 1, memory_order_release);
    free(argument);
    return NULL;
}

static TreeChild *best_root_child(const SearchJob *job, uint64_t *best_visits) {
    if (job == NULL || job->root == NULL) return NULL;
    TreeChild *best = NULL;
    uint64_t visits_for_best = 0;
    char best_text[16] = {0};
    for (unsigned index = 0; index < job->root->move_count; ++index) {
        TreeChild *child = &job->root->children[index];
        if (atomic_load_explicit(&child->node, memory_order_acquire) == NULL) continue;
        uint64_t visits = atomic_load_explicit(&child->visits, memory_order_relaxed);
        char text[16] = {0};
        (void)shogi_move_to_usi(child->move, text, sizeof(text));
        if (best == NULL || visits > visits_for_best ||
            (visits == visits_for_best && strcmp(text, best_text) < 0)) {
            best = child;
            visits_for_best = visits;
            memcpy(best_text, text, sizeof(best_text));
        }
    }
    if (best_visits != NULL) *best_visits = visits_for_best;
    return best;
}

static TreeChild *best_line_child(const TreeNode *node) {
    if (node == NULL) return NULL;
    TreeChild *best = NULL;
    uint64_t best_visits = 0;
    char best_text[16] = {0};
    for (unsigned index = 0; index < node->move_count; ++index) {
        TreeChild *child = &node->children[index];
        if (atomic_load_explicit(&child->node, memory_order_acquire) == NULL) continue;
        uint64_t visits = atomic_load_explicit(&child->visits, memory_order_relaxed);
        char text[16] = {0};
        (void)shogi_move_to_usi(child->move, text, sizeof(text));
        if (best == NULL || visits > best_visits ||
            (visits == best_visits && strcmp(text, best_text) < 0)) {
            best = child;
            best_visits = visits;
            memcpy(best_text, text, sizeof(best_text));
        }
    }
    return best;
}

static size_t line_principal_variation(TreeChild *child, ShogiMove *pv, size_t capacity) {
    size_t length = 0;
    while (child != NULL && length < capacity) {
        pv[length++] = child->move;
        TreeNode *node = atomic_load_explicit(&child->node, memory_order_acquire);
        child = best_line_child(node);
    }
    return length;
}

static int root_score_cp(const TreeChild *child) {
    uint64_t visits = atomic_load_explicit(&child->visits, memory_order_relaxed);
    if (visits == 0) return 0;
    uint64_t value = atomic_load_explicit(&child->value, memory_order_relaxed);
    double mean = (double)value / ((double)visits * (double)VALUE_SCALE);
    int score = (int)((mean * 2.0 - 1.0) * 1000.0);
    if (score > 1000) score = 1000;
    if (score < -1000) score = -1000;
    return score;
}

size_t search_get_root_lines(const SearchJob *job, SearchLine *lines, size_t capacity) {
    if (job == NULL || job->root == NULL || lines == NULL || capacity == 0) return 0;
    if (capacity > SEARCH_MAX_MULTIPV) capacity = SEARCH_MAX_MULTIPV;
    bool used[SHOGI_MAX_MOVES] = {false};
    size_t output = 0;
    while (output < capacity) {
        TreeChild *best = NULL;
        unsigned best_index = 0;
        uint64_t best_visits = 0;
        char best_text[16] = {0};
        for (unsigned index = 0; index < job->root->move_count; ++index) {
            if (used[index]) continue;
            TreeChild *child = &job->root->children[index];
            if (atomic_load_explicit(&child->node, memory_order_acquire) == NULL) continue;
            uint64_t visits = atomic_load_explicit(&child->visits, memory_order_relaxed);
            char text[16] = {0};
            (void)shogi_move_to_usi(child->move, text, sizeof(text));
            if (best == NULL || visits > best_visits ||
                (visits == best_visits && strcmp(text, best_text) < 0)) {
                best = child;
                best_index = index;
                best_visits = visits;
                memcpy(best_text, text, sizeof(best_text));
            }
        }
        if (best == NULL) break;
        used[best_index] = true;
        lines[output].move = best->move;
        lines[output].visits = best_visits;
        lines[output].score_cp = root_score_cp(best);
        lines[output].pv_length = line_principal_variation(best, lines[output].pv, SEARCH_MAX_PV);
        ++output;
    }
    if (output == 0 && job->root->move_count > 0) {
        lines[0].move = job->root->children[0].move;
        lines[0].visits = 0;
        lines[0].score_cp = 0;
        lines[0].pv_length = 1;
        lines[0].pv[0] = lines[0].move;
        output = 1;
    }
    return output;
}

size_t search_get_root_policy(const SearchJob *job, SearchPolicyEntry *entries, size_t capacity) {
    if (job == NULL || job->root == NULL || entries == NULL || capacity == 0) return 0;
    size_t count = job->root->move_count;
    if (count > capacity) count = capacity;
    bool used[SHOGI_MAX_MOVES] = {false};
    for (size_t output = 0; output < count; ++output) {
        unsigned best_index = 0;
        uint64_t best_visits = 0;
        char best_text[16] = {0};
        bool found = false;
        for (unsigned index = 0; index < job->root->move_count; ++index) {
            if (used[index]) continue;
            TreeChild *child = &job->root->children[index];
            uint64_t visits = atomic_load_explicit(&child->visits, memory_order_relaxed);
            char text[16] = {0};
            (void)shogi_move_to_usi(child->move, text, sizeof(text));
            if (!found || visits > best_visits ||
                (visits == best_visits && strcmp(text, best_text) < 0)) {
                found = true;
                best_index = index;
                best_visits = visits;
                memcpy(best_text, text, sizeof(best_text));
            }
        }
        if (!found) break;
        used[best_index] = true;
        entries[output].move = job->root->children[best_index].move;
        entries[output].visits = best_visits;
    }
    return count;
}

static unsigned default_threads(void) {
    long count = sysconf(_SC_NPROCESSORS_ONLN);
    if (count < 1) count = 1;
    if (count > 8) count = 8;
    return (unsigned)count;
}

static uint64_t search_deadline(const SearchLimits *limits, ShogiColor side) {
    if (limits->infinite || limits->ponder) return 0;
    if (limits->nodes != 0 && limits->movetime_ms <= 0 &&
        limits->btime_ms <= 0 && limits->wtime_ms <= 0) return 0;
    int budget = limits->movetime_ms;
    if (budget <= 0) {
        int remaining = side == SHOGI_BLACK ? limits->btime_ms : limits->wtime_ms;
        if (remaining > 0) {
            int increment = side == SHOGI_BLACK ? limits->binc_ms : limits->winc_ms;
            budget = remaining / 30 + increment + limits->byoyomi_ms;
            int safety = remaining / 20;
            if (safety < 50) safety = 50;
            if (budget > remaining - safety) budget = remaining - safety;
        }
    }
    if (budget <= 0) budget = 5000;
    if (budget < 10) budget = 10;
    return monotonic_ns() + (uint64_t)budget * UINT64_C(1000000);
}

static void choose_result(SearchJob *job) {
    job->result.simulations = atomic_load_explicit(&job->simulations, memory_order_relaxed);
    if (job->root == NULL) {
        job->result.resign = true;
        return;
    }
    if (shogi_is_declaration_win(&job->root_position, job->root_side)) {
        job->result.declaration_win = true;
        return;
    }
    TreeChild *best = best_root_child(job, NULL);
    if (best == NULL && job->root->move_count > 0) {
        best = &job->root->children[0];
    }
    if (best == NULL) {
        job->result.resign = true;
    } else {
        job->result.has_move = true;
        job->result.move = best->move;
    }
}

SearchJob *search_start(const ShogiPosition *position, const SearchLimits *limits,
                        const SearchOptions *options) {
    if (position == NULL || limits == NULL || options == NULL) return NULL;
    SearchJob *job = calloc(1, sizeof(*job));
    if (job == NULL) return NULL;
    job->root_position = *position;
    job->limits = *limits;
    job->options = *options;
    if (job->options.threads == 0) job->options.threads = default_threads();
    if (job->options.threads > 64) job->options.threads = 64;
    if (job->options.max_tree_nodes < 1000) job->options.max_tree_nodes = DEFAULT_MAX_TREE_NODES;
    job->root_side = position->side;
    if (job->options.rollout_depth == 0) job->options.rollout_depth = SEARCH_DEFAULT_ROLLOUT_DEPTH;
    if (job->options.exploration_milli == 0) job->options.exploration_milli = SEARCH_DEFAULT_EXPLORATION_MILLI;
    if (job->options.multi_pv == 0) job->options.multi_pv = SEARCH_DEFAULT_MULTIPV;
    if (job->options.multi_pv > SEARCH_MAX_MULTIPV) job->options.multi_pv = SEARCH_MAX_MULTIPV;
    atomic_init(&job->stop, false);
    atomic_init(&job->pondering, limits->ponder);
    atomic_init(&job->workers_done, 0);
    atomic_init(&job->simulations, 0);
    atomic_init(&job->deadline_ns, search_deadline(limits, position->side));
    job->start_ns = monotonic_ns();
    job->tree.node_capacity = job->options.max_tree_nodes;
    job->tree.nodes = calloc(job->tree.node_capacity, sizeof(*job->tree.nodes));
    if (job->tree.nodes == NULL || ts_mutex_init(&job->tree.expansion_mutex) != 0) {
        free(job->tree.nodes);
        free(job);
        return NULL;
    }
    job->root = tree_new_node(&job->tree, position->hash);
    ShogiMove moves[SHOGI_MAX_MOVES];
    size_t move_count = shogi_generate_legal(position, moves, SHOGI_MAX_MOVES);
    if (limits->has_searchmoves) {
        size_t filtered = 0;
        for (size_t index = 0; index < move_count; ++index) {
            for (size_t requested = 0; requested < limits->searchmove_count; ++requested) {
                if (same_search_move(moves[index], limits->searchmoves[requested])) {
                    moves[filtered++] = moves[index];
                    break;
                }
            }
        }
        move_count = filtered;
    }
    if (job->root == NULL || !node_expand(&job->tree, job->root, position, moves, move_count) || move_count == 0) {
        if (job->root != NULL) {
            ShogiResult result = shogi_game_result(position);
            if (result == (position->side == SHOGI_BLACK ? SHOGI_RESULT_BLACK_WIN : SHOGI_RESULT_WHITE_WIN)) job->result.declaration_win = true;
            else job->result.resign = true;
        }
        atomic_store(&job->workers_done, job->worker_count);
        return job;
    }

    job->worker_count = job->options.threads;
    job->workers = calloc(job->worker_count, sizeof(*job->workers));
    if (job->workers == NULL) {
        search_destroy(job);
        return NULL;
    }
    for (unsigned index = 0; index < job->worker_count; ++index) {
        WorkerArgument *argument = malloc(sizeof(*argument));
        if (argument == NULL) {
            atomic_store(&job->stop, true);
            job->worker_count = index;
            search_join(job, NULL);
            search_destroy(job);
            return NULL;
        }
        argument->job = job;
        argument->id = index;
        if (ts_thread_create(&job->workers[index], worker_main, argument) != 0) {
            free(argument);
            atomic_store(&job->stop, true);
            job->worker_count = index;
            search_join(job, NULL);
            search_destroy(job);
            return NULL;
        }
    }
    return job;
}

bool search_is_done(const SearchJob *job) {
    if (job == NULL) return true;
    return atomic_load_explicit(&job->workers_done, memory_order_acquire) >= job->worker_count;
}

bool search_is_infinite(const SearchJob *job) {
    return job != NULL && job->limits.infinite;
}

bool search_is_pondering(const SearchJob *job) {
    return job != NULL && atomic_load_explicit(&job->pondering, memory_order_acquire);
}

bool search_waits_for_stop(const SearchJob *job) {
    return job != NULL && (job->limits.infinite || search_is_pondering(job));
}

bool search_ponderhit(SearchJob *job) {
    if (job == NULL || !atomic_exchange_explicit(&job->pondering, false, memory_order_acq_rel)) return false;
    SearchLimits limits = job->limits;
    limits.ponder = false;
    uint64_t deadline = search_deadline(&limits, job->root_side);
    atomic_store_explicit(&job->deadline_ns, deadline, memory_order_release);
    return true;
}

bool search_get_progress(const SearchJob *job, SearchProgress *progress) {
    if (job == NULL || progress == NULL) return false;
    memset(progress, 0, sizeof(*progress));
    progress->nodes = atomic_load_explicit(&job->simulations, memory_order_relaxed);
    uint64_t now = monotonic_ns();
    uint64_t elapsed = now >= job->start_ns ? now - job->start_ns : 0;
    progress->time_ms = elapsed / UINT64_C(1000000);
    if (elapsed != 0) progress->nps = progress->nodes * UINT64_C(1000000000) / elapsed;
    TreeChild *best = best_root_child(job, NULL);
    if (best == NULL && job->root != NULL && job->root->move_count > 0) best = &job->root->children[0];
    if (best != NULL) {
        progress->has_move = true;
        progress->move = best->move;
        uint64_t visits = atomic_load_explicit(&best->visits, memory_order_relaxed);
        uint64_t value = atomic_load_explicit(&best->value, memory_order_relaxed);
        if (visits != 0) {
            double mean = (double)value / ((double)visits * (double)VALUE_SCALE);
            progress->score_cp = (int)((mean * 2.0 - 1.0) * 1000.0);
            if (progress->score_cp > 1000) progress->score_cp = 1000;
            if (progress->score_cp < -1000) progress->score_cp = -1000;
        }
    }
    return true;
}

void search_request_stop(SearchJob *job) {
    if (job != NULL) atomic_store_explicit(&job->stop, true, memory_order_release);
}

void search_join(SearchJob *job, SearchResult *result) {
    if (job == NULL || job->joined) {
        if (job != NULL && result != NULL) *result = job->result;
        return;
    }
    for (unsigned index = 0; index < job->worker_count; ++index) ts_thread_join(&job->workers[index]);
    choose_result(job);
    job->joined = true;
    if (result != NULL) *result = job->result;
}

void search_destroy(SearchJob *job) {
    if (job == NULL) return;
    if (!job->joined && job->worker_count != 0) {
        search_request_stop(job);
        search_join(job, NULL);
    }
    free(job->workers);
    tree_destroy(&job->tree);
    free(job);
}
