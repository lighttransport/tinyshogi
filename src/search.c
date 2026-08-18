#define _POSIX_C_SOURCE 200809L

#include "search.h"
#if defined(TINYSHOGI_A64FX_UCT)
#include "a64fx_uct.h"
#endif
#include "thread.h"

#include <math.h>
#include <limits.h>
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
#define WORKER_EVAL_CACHE_CAPACITY (1U << 14)
#define VALUE_SCALE UINT64_C(1000000)
#define SEARCH_NEURAL_MAX_BATCH 12U
#define SEARCH_NEURAL_MAX_DEPTH 8

typedef struct TreeNode TreeNode;

typedef struct TreeArenaChunk {
    struct TreeArenaChunk *next;
    size_t used;
    size_t capacity;
    unsigned char data[];
} TreeArenaChunk;

typedef struct {
    TreeArenaChunk *chunks;
    TreeArenaChunk *current;
} TreeArena;

typedef struct {
    uint64_t hash;
    TreeNode *node;
} TreeHashEntry;

typedef struct {
    uint64_t hash;
    int score;
    uint8_t perspective;
    bool valid;
} EvalCacheEntry;

typedef struct {
    uint64_t key;
    int16_t score;
    int8_t depth;
    uint8_t bound;
    ShogiMove move;
} AlphaBetaHashEntry;

typedef struct {
    ShogiMove move;
    TreeNode *node;
    uint64_t visits;
    uint64_t value;
    int virtual_loss;
} TreeChild;

struct TreeNode {
    uint64_t hash;
    bool expanded;
    unsigned next_unexpanded;
    unsigned selectable_count;
    uint64_t visits;
    uint64_t value;
    unsigned move_count;
    ShogiMove *moves;
    TreeChild *children;
    float *selection_mean;
    float *selection_inv_sqrt;
    bool terminal;
    double terminal_value;
};

typedef struct {
    TreeNode *nodes;
    size_t node_count;
    size_t node_capacity;
    TreeHashEntry *hash_table;
    size_t hash_capacity;
    TreeArena arena;
} SearchTree;

typedef struct {
    SearchTree tree;
    atomic_bool in_use;
} SearchContextWorker;

struct SearchContext {
    SearchContextWorker workers[64];
};

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
    bool neural_mcts;
    AlphaBetaHashEntry *ab_hash;
    size_t ab_hash_capacity;
    ShogiMove ab_best_move;
    int ab_best_score;
    int ab_completed_depth;
    bool ab_best_valid;
    int ab_history[2][SHOGI_SQUARES + 1][SHOGI_SQUARES];
    ShogiMove ab_killers[SEARCH_MAX_PV][2];
    float exploration_constant;
    SearchResult result;
    bool joined;
};

typedef struct {
    SearchJob *job;
    unsigned id;
    const ShogiEvaluator *evaluator;
    EvalCacheEntry *eval_cache;
    size_t eval_cache_capacity;
    void *eval_state;
    void *neural_eval_states[SEARCH_NEURAL_MAX_BATCH];
    bool neural_ready;
    SearchTree tree;
    TreeNode *root;
    SearchContextWorker *persistent_resource;
} WorkerContext;

static bool worker_make_move(WorkerContext *worker, ShogiPosition *position,
                             ShogiMove move, ShogiUndo *undo) {
    if (!shogi_make_move_undo_fast(position, move, undo)) return false;
    const ShogiEvaluator *evaluator = worker->evaluator;
    if (worker->eval_state != NULL &&
        !shogi_evaluator_state_make(evaluator, worker->eval_state, position, undo)) {
        (void)shogi_unmake_move(position, undo);
        return false;
    }
    return true;
}

static bool worker_unmake_move(WorkerContext *worker, ShogiPosition *position,
                               const ShogiUndo *undo) {
    if (!shogi_unmake_move(position, undo)) return false;
    return worker->eval_state == NULL ||
           shogi_evaluator_state_unmake(worker->evaluator,
                                        worker->eval_state, position, undo);
}

static bool state_make(const ShogiEvaluator *evaluator, void *state,
                       ShogiPosition *position, ShogiMove move, ShogiUndo *undo) {
    if (!shogi_make_move_undo_fast(position, move, undo)) return false;
    if (state != NULL && !shogi_evaluator_state_make(evaluator, state, position, undo)) {
        (void)shogi_unmake_move(position, undo);
        return false;
    }
    return true;
}

static bool state_unmake(const ShogiEvaluator *evaluator, void *state,
                         ShogiPosition *position, const ShogiUndo *undo) {
    if (!shogi_unmake_move(position, undo)) return false;
    return state == NULL || shogi_evaluator_state_unmake(evaluator, state, position, undo);
}

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
    if (atomic_load_explicit((atomic_bool *)&job->stop, memory_order_relaxed)) return true;
    uint64_t deadline = atomic_load_explicit(
        (atomic_uint_least64_t *)&job->deadline_ns, memory_order_acquire);
    if (deadline != 0 && monotonic_ns() >= deadline) return true;
    if (job->limits.nodes != 0 && atomic_load_explicit(
            (atomic_uint_least64_t *)&job->simulations,
            memory_order_relaxed) >= job->limits.nodes) return true;
    return false;
}

static void *tree_arena_alloc(SearchTree *tree, size_t size) {
    if (tree == NULL || size == 0) return NULL;
    const size_t alignment = 8U;
    TreeArenaChunk *chunk = tree->arena.current;
    size_t offset = 0;
    while (chunk != NULL) {
        offset = (chunk->used + alignment - 1U) & ~(alignment - 1U);
        if (offset <= chunk->capacity && size <= chunk->capacity - offset) break;
        chunk = chunk->next;
    }
    if (chunk == NULL) {
        size_t capacity = size > (1U << 20) ? size : (1U << 20);
        TreeArenaChunk *fresh = malloc(sizeof(*fresh) + capacity);
        if (fresh == NULL) return NULL;
        fresh->next = tree->arena.chunks;
        fresh->used = size;
        fresh->capacity = capacity;
        tree->arena.chunks = fresh;
        tree->arena.current = fresh;
        return fresh->data;
    }
    tree->arena.current = chunk;
    void *result = chunk->data + offset;
    chunk->used = offset + size;
    return result;
}

static void tree_arena_destroy(TreeArena *arena) {
    if (arena == NULL) return;
    TreeArenaChunk *chunk = arena->chunks;
    while (chunk != NULL) {
        TreeArenaChunk *next = chunk->next;
        free(chunk);
        chunk = next;
    }
    arena->chunks = NULL;
    arena->current = NULL;
}

static void tree_arena_reset(TreeArena *arena) {
    if (arena == NULL) return;
    for (TreeArenaChunk *chunk = arena->chunks; chunk != NULL; chunk = chunk->next)
        chunk->used = 0;
    arena->current = arena->chunks;
}

static void tree_free_node(TreeNode *node) {
    (void)node;
}

static void tree_destroy(SearchTree *tree) {
    if (tree == NULL) return;
    for (size_t index = 0; index < tree->node_count; ++index) tree_free_node(&tree->nodes[index]);
    tree_arena_destroy(&tree->arena);
    free(tree->nodes);
    free(tree->hash_table);
    memset(tree, 0, sizeof(*tree));
}

static bool tree_init(SearchTree *tree, size_t node_capacity) {
    if (tree == NULL || node_capacity == 0) return false;
    memset(tree, 0, sizeof(*tree));
    tree->node_capacity = node_capacity;
    tree->nodes = calloc(node_capacity, sizeof(*tree->nodes));
    tree->hash_capacity = 1;
    while (tree->hash_capacity < node_capacity * 2U &&
           tree->hash_capacity <= SIZE_MAX / 2U)
        tree->hash_capacity <<= 1;
    tree->hash_table = calloc(tree->hash_capacity, sizeof(*tree->hash_table));
    if (tree->nodes == NULL || tree->hash_table == NULL) {
        free(tree->nodes);
        free(tree->hash_table);
        memset(tree, 0, sizeof(*tree));
        return false;
    }
    return true;
}

static bool tree_prepare(SearchTree *tree, size_t node_capacity) {
    if (tree == NULL || node_capacity == 0) return false;
    if (tree->nodes == NULL || tree->hash_table == NULL ||
        tree->node_capacity < node_capacity) {
        tree_destroy(tree);
        return tree_init(tree, node_capacity);
    }
    tree->node_count = 0;
    memset(tree->hash_table, 0,
           tree->hash_capacity * sizeof(*tree->hash_table));
    tree_arena_reset(&tree->arena);
    return true;
}

SearchContext *search_context_create(void) {
    SearchContext *context = calloc(1, sizeof(*context));
    if (context == NULL) return NULL;
    for (unsigned index = 0; index < 64U; ++index)
        atomic_init(&context->workers[index].in_use, false);
    return context;
}

void search_context_destroy(SearchContext *context) {
    if (context == NULL) return;
    for (unsigned index = 0; index < 64U; ++index)
        tree_destroy(&context->workers[index].tree);
    free(context);
}

static bool worker_tree_prepare(WorkerContext *worker, size_t node_capacity) {
    if (worker->persistent_resource != NULL) {
        worker->tree = worker->persistent_resource->tree;
        memset(&worker->persistent_resource->tree, 0,
               sizeof(worker->persistent_resource->tree));
    }
    return tree_prepare(&worker->tree, node_capacity);
}

static void worker_tree_release(WorkerContext *worker) {
    if (worker->persistent_resource == NULL) {
        tree_destroy(&worker->tree);
        return;
    }
    worker->persistent_resource->tree = worker->tree;
    memset(&worker->tree, 0, sizeof(worker->tree));
    atomic_store_explicit(&worker->persistent_resource->in_use, false,
                          memory_order_release);
}

static size_t tree_hash_index(const SearchTree *tree, uint64_t hash) {
    hash ^= hash >> 30;
    hash *= UINT64_C(0xbf58476d1ce4e5b9);
    hash ^= hash >> 27;
    hash *= UINT64_C(0x94d049bb133111eb);
    hash ^= hash >> 31;
    return (size_t)hash & (tree->hash_capacity - 1);
}

static TreeNode *tree_find_hash(const SearchTree *tree, uint64_t hash) {
    if (tree->hash_table == NULL || tree->hash_capacity == 0) return NULL;
    size_t index = tree_hash_index(tree, hash);
    for (size_t probe = 0; probe < tree->hash_capacity; ++probe) {
        const TreeHashEntry *entry = &tree->hash_table[index];
        if (entry->node == NULL) return NULL;
        if (entry->hash == hash) return entry->node;
        index = (index + 1) & (tree->hash_capacity - 1);
    }
    return NULL;
}

static void tree_insert_hash(SearchTree *tree, uint64_t hash, TreeNode *node) {
    if (tree->hash_table == NULL || tree->hash_capacity == 0) return;
    size_t index = tree_hash_index(tree, hash);
    for (size_t probe = 0; probe < tree->hash_capacity; ++probe) {
        TreeHashEntry *entry = &tree->hash_table[index];
        if (entry->node == NULL || entry->hash == hash) {
            entry->hash = hash;
            entry->node = node;
            return;
        }
        index = (index + 1) & (tree->hash_capacity - 1);
    }
}

static TreeNode *tree_new_node(SearchTree *tree, uint64_t hash) {
    TreeNode *node = NULL;
    if (tree->node_count < tree->node_capacity) {
        node = &tree->nodes[tree->node_count++];
        memset(node, 0, sizeof(*node));
        node->hash = hash;
        node->expanded = false;
        node->next_unexpanded = 0;
        node->visits = 0;
        node->value = 0;
        tree_insert_hash(tree, hash, node);
    }
    return node;
}

static bool node_expand(SearchTree *tree, TreeNode *node, const ShogiPosition *position,
                        const ShogiMove *moves, size_t move_count) {
    if (node->expanded) return true;
    bool success = true;
    if (!node->expanded) {
        node->move_count = (unsigned)move_count;
        if (move_count != 0) {
            node->moves = tree_arena_alloc(tree, move_count * sizeof(*node->moves));
            node->children = tree_arena_alloc(tree, move_count * sizeof(*node->children));
            node->selection_mean = tree_arena_alloc(tree, move_count * sizeof(*node->selection_mean));
            node->selection_inv_sqrt = tree_arena_alloc(
                tree, move_count * sizeof(*node->selection_inv_sqrt));
            if (node->moves == NULL || node->children == NULL ||
                node->selection_mean == NULL || node->selection_inv_sqrt == NULL) {
                node->moves = NULL;
                node->children = NULL;
                node->selection_mean = NULL;
                node->selection_inv_sqrt = NULL;
                node->move_count = 0;
                success = false;
            } else {
                memcpy(node->moves, moves, move_count * sizeof(*moves));
                for (size_t index = 0; index < move_count; ++index) {
                    node->children[index].move = moves[index];
                    node->children[index].node = NULL;
                    node->children[index].visits = 0;
                    node->children[index].value = 0;
                    node->children[index].virtual_loss = 0;
                    node->selection_mean[index] = 0.5f;
                    node->selection_inv_sqrt[index] = 1.0f;
                }
            }
        }
        (void)position;
        node->expanded = true;
    }
    (void)tree;
    return success;
}

static void child_selection_update(TreeNode *node, unsigned index) {
    TreeChild *child = &node->children[index];
    uint64_t effective = child->visits +
        (uint64_t)(child->virtual_loss > 0 ? child->virtual_loss : 0);
    node->selection_mean[index] = effective == 0 ? 0.5f :
        (float)child->value / ((float)effective * (float)VALUE_SCALE);
    node->selection_inv_sqrt[index] = 1.0f / sqrtf((float)effective + 1.0f);
}

static TreeChild *select_child(const SearchJob *job, TreeNode *node, bool maximizing) {
    TreeChild *best = NULL;
    float best_score = -1.0f;
    float parent_sqrt = sqrtf(logf((float)node->visits + 1.0f));
    float exploration_scale = job->exploration_constant * parent_sqrt;
    /* Children are expanded in order.  The suffix has never been selectable,
     * so avoid rescanning it on every lane; expand_one() owns that suffix. */
    unsigned selectable_count = node->selectable_count;
    if (selectable_count > node->move_count) selectable_count = node->move_count;
    unsigned best_index = UINT_MAX;
#if defined(TINYSHOGI_A64FX_UCT)
    if (job->options.a64fx_uct && selectable_count >= 16U) {
        size_t selected = tinyshogi_a64fx_uct_argmax(
            node->selection_mean, node->selection_inv_sqrt, selectable_count,
            exploration_scale, maximizing);
        if (selected != SIZE_MAX) best_index = (unsigned)selected;
    }
#endif
    if (best_index == UINT_MAX) {
        for (unsigned index = 0; index < selectable_count; ++index) {
            float mean = node->selection_mean[index];
            if (!maximizing) mean = 1.0f - mean;
            float score = fmaf(exploration_scale, node->selection_inv_sqrt[index], mean);
            if (best == NULL || score > best_score) {
                best = &node->children[index];
                best_score = score;
                best_index = index;
            }
        }
    }
    if (best == NULL && best_index != UINT_MAX) best = &node->children[best_index];
    if (best != NULL) {
        ++best->virtual_loss;
        child_selection_update(node, (unsigned)(best - node->children));
    }
    return best;
}

static TreeChild *expand_one(SearchTree *tree, TreeNode *node, ShogiPosition *position,
                             ShogiUndo *undo) {
    unsigned index = node->next_unexpanded;
    if (index >= node->move_count) return NULL;
    node->next_unexpanded = index + 1;
    TreeChild *child = &node->children[index];
    TreeNode *child_node = child->node;
    if (child_node == NULL) {
        bool made = shogi_make_move_undo_fast(position, child->move, undo);
        if (!made) {
            child_node = NULL;
        } else {
            child_node = tree_find_hash(tree, position->hash);
            if (child_node == NULL && tree->node_count < tree->node_capacity) {
                child_node = &tree->nodes[tree->node_count++];
                memset(child_node, 0, sizeof(*child_node));
                child_node->hash = position->hash;
                child_node->expanded = false;
                child_node->next_unexpanded = 0;
                child_node->visits = 0;
                child_node->value = 0;
                tree_insert_hash(tree, position->hash, child_node);
            }
            if (child_node == NULL) (void)shogi_unmake_move(position, undo);
        }
        child->node = child_node;
        if (child_node != NULL) node->selectable_count = index + 1;
    }
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

static int static_evaluation(const WorkerContext *worker, const ShogiPosition *position,
                             ShogiColor perspective) {
    if (shogi_evaluator_active(worker->evaluator)) {
        int score;
        if (worker->eval_cache != NULL && worker->eval_cache_capacity != 0) {
            size_t index = (size_t)(position->hash ^ (uint64_t)perspective) &
                           (worker->eval_cache_capacity - 1);
            EvalCacheEntry *entry = &worker->eval_cache[index];
            if (entry->valid && entry->hash == position->hash &&
                entry->perspective == (uint8_t)perspective) {
                score = entry->score;
            } else {
                score = worker->eval_state != NULL ?
                    shogi_evaluator_state_score(worker->evaluator,
                                                worker->eval_state) :
                    shogi_evaluator_score(worker->evaluator, position, perspective);
                entry->hash = position->hash;
                entry->perspective = (uint8_t)perspective;
                entry->score = score;
                entry->valid = true;
            }
        } else {
            score = shogi_evaluator_score(worker->evaluator, position, perspective);
        }
        /* Preserve decisive NNUE differences for alpha-beta.  MCTS converts
         * scores to probabilities at its leaf boundary and clamps there. */
        if (score > 12000) return 12000;
        if (score < -12000) return -12000;
        return score;
    }
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
    size_t own_moves = shogi_generate_pseudo_for_color(
        position, perspective, moves, SHOGI_MAX_MOVES);
    size_t opponent_moves = shogi_generate_pseudo_for_color(
        position, (ShogiColor)(perspective ^ 1), moves, SHOGI_MAX_MOVES);
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
    ShogiMove move;
    int score;
    bool gives_check;
} TacticalMove;

static int tactical_move_score(ShogiPosition *position, ShogiMove move,
                               bool *gives_check) {
    int score = 0;
    if (move.from != SHOGI_SQ_NONE && position->board[move.to] != SHOGI_EMPTY) {
        score += 1000 + piece_value(shogi_piece_type(position->board[move.to]));
    }
    if (move.promote) score += 500;

    ShogiUndo undo;
    if (shogi_make_move_undo_fast(position, move, &undo)) {
        bool check = shogi_is_in_check(position, position->side);
        if (gives_check != NULL) *gives_check = check;
        if (check) score += 750;
        (void)shogi_unmake_move(position, &undo);
    }
    return score;
}

static int quiescence_search(WorkerContext *worker, ShogiPosition *position,
                             ShogiColor perspective, unsigned depth,
                             int alpha, int beta) {
    const SearchJob *job = worker->job;
    if (should_stop(job)) return static_evaluation(worker, position, perspective);

    ShogiMove moves[SHOGI_MAX_MOVES];
    size_t move_count = 0;
    ShogiResult result = shogi_game_result_with_moves_mut(position, moves,
                                                           SHOGI_MAX_MOVES, &move_count);
    if (result != SHOGI_RESULT_ONGOING) {
        if (result == SHOGI_RESULT_DRAW) return 0;
        ShogiResult win = perspective == SHOGI_BLACK ? SHOGI_RESULT_BLACK_WIN : SHOGI_RESULT_WHITE_WIN;
        return result == win ? 3000 : -3000;
    }

    int stand_pat = static_evaluation(worker, position, perspective);
    if (depth == 0) return stand_pat;
    bool in_check = shogi_is_in_check(position, position->side);
    bool maximizing = position->side == perspective;
    if (!in_check) {
        if (maximizing) {
            if (stand_pat >= beta) return stand_pat;
            if (stand_pat > alpha) alpha = stand_pat;
        } else {
            if (stand_pat <= alpha) return stand_pat;
            if (stand_pat < beta) beta = stand_pat;
        }
    }
    TacticalMove tactical[SHOGI_MAX_MOVES];
    size_t tactical_count = 0;
    for (size_t index = 0; index < move_count; ++index) {
        ShogiMove move = moves[index];
        bool gives_check = false;
        int score = tactical_move_score(position, move, &gives_check);
        bool is_tactical = in_check || score > 0;
        if (is_tactical && tactical_count < SHOGI_MAX_MOVES) {
            tactical[tactical_count++] = (TacticalMove){move, score, gives_check};
        }
    }
    if (tactical_count == 0) return stand_pat;

    /* A quiet position may stand pat.  Captures and promotions are optional;
     * treating one of them as forced makes the search prefer losing captures
     * whenever every tactical continuation is worse than the static score. */
    int best = in_check ? (maximizing ? -30000 : 30000) : stand_pat;
    for (size_t index = 0; index < tactical_count; ++index) {
        size_t best_index = index;
        for (size_t candidate = index + 1; candidate < tactical_count; ++candidate) {
            if (tactical[candidate].score > tactical[best_index].score) best_index = candidate;
        }
        if (best_index != index) {
            TacticalMove swap = tactical[index];
            tactical[index] = tactical[best_index];
            tactical[best_index] = swap;
        }

        ShogiUndo undo;
        if (!worker_make_move(worker, position, tactical[index].move, &undo)) continue;
        int score = quiescence_search(worker, position, perspective, depth - 1, alpha, beta);
        (void)worker_unmake_move(worker, position, &undo);
        if (maximizing) {
            if (score > best) best = score;
            if (best > alpha) alpha = best;
        } else {
            if (score < best) best = score;
            if (best < beta) beta = best;
        }
        if (alpha >= beta) break;
    }
    return best == (maximizing ? -30000 : 30000) ? stand_pat : best;
}

typedef struct {
    TreeNode *parents[SEARCH_MAX_PATH];
    unsigned child_indices[SEARCH_MAX_PATH];
    size_t length;
} SearchPath;

static bool path_push(SearchPath *path, TreeNode *parent, TreeChild *child) {
    if (path == NULL || parent == NULL || child == NULL ||
        path->length >= SEARCH_MAX_PATH) return false;
    ptrdiff_t index = child - parent->children;
    if (index < 0 || (unsigned)index >= parent->move_count) return false;
    path->parents[path->length] = parent;
    path->child_indices[path->length] = (unsigned)index;
    ++path->length;
    return true;
}

static void backpropagate(WorkerContext *worker, const SearchPath *path, double value,
                          uint64_t *root_visits, uint64_t *root_values);

static double rollout(WorkerContext *worker, ShogiPosition *position, ShogiUndo *undos,
                      size_t *undo_length, uint64_t *rng) {
    SearchJob *job = worker->job;
    int rollout_depth = job->limits.depth > 0 ? job->limits.depth : (int)job->options.rollout_depth;
    for (int ply = 0; ply < rollout_depth; ++ply) {
        if (should_stop(job)) break;
        ShogiMove moves[SHOGI_MAX_MOVES];
        size_t count = 0;
        ShogiResult result = shogi_game_result_with_moves_mut(position, moves, SHOGI_MAX_MOVES, &count);
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
            !worker_make_move(worker, position, moves[choice], &undos[*undo_length])) break;
        ++*undo_length;
    }
    int score = quiescence_search(worker, position, job->root_side,
                                  job->options.quiescence_depth,
                                  -3000, 3000);
    if (score > 1500) score = 1500;
    if (score < -1500) score = -1500;
    return 0.5 + (double)score / 3000.0;
}

static double run_simulation(WorkerContext *worker, ShogiPosition *position,
                             ShogiUndo *undos, uint64_t *rng) {
    SearchJob *job = worker->job;
    TreeNode *node = worker->root;
    SearchPath path = {0};
    size_t undo_length = 0;

    double value = 0.5;
    bool terminal = false;
    for (int depth = 0; depth < SEARCH_NEURAL_MAX_DEPTH; ++depth) {
        if (should_stop(job)) break;
        ShogiMove moves[SHOGI_MAX_MOVES];
        size_t count = 0;
        ShogiResult result = shogi_game_result_with_moves_mut(position, moves, SHOGI_MAX_MOVES, &count);
        if (result != SHOGI_RESULT_ONGOING) {
            if (result == SHOGI_RESULT_DRAW) value = 0.5;
            else value = result == (job->root_side == SHOGI_BLACK ? SHOGI_RESULT_BLACK_WIN : SHOGI_RESULT_WHITE_WIN) ? 1.0 : 0.0;
            terminal = true;
            break;
        }
        if (!node_expand(&worker->tree, node, position, moves, count)) break;
        if (count == 0) break;

        TreeChild *expanded = expand_one(&worker->tree, node, position,
                                         &undos[undo_length]);
        if (expanded != NULL) {
            if (worker->eval_state != NULL &&
                !shogi_evaluator_state_make(worker->evaluator,
                                            worker->eval_state, position,
                                            &undos[undo_length])) {
                (void)shogi_unmake_move(position, &undos[undo_length]);
                break;
            }
            ++undo_length;
            ++expanded->virtual_loss;
            child_selection_update(node, (unsigned)(expanded - node->children));
            if (!path_push(&path, node, expanded)) break;
            TreeNode *next = expanded->node;
            if (next == NULL) break;
            node = next;
            break;
        }
        TreeChild *selected = select_child(job, node, position->side == job->root_side);
        if (selected == NULL) break;
        if (!path_push(&path, node, selected)) break;
        if (undo_length >= SEARCH_MAX_UNDO ||
            !worker_make_move(worker, position, selected->move,
                              &undos[undo_length])) break;
        ++undo_length;
        TreeNode *next = selected->node;
        if (next == NULL) break;
        node = next;
    }

    if (!terminal) value = rollout(worker, position, undos, &undo_length, rng);
    while (undo_length > 0) {
        --undo_length;
        (void)worker_unmake_move(worker, position, &undos[undo_length]);
    }
    backpropagate(worker, &path, value, NULL, NULL);
    return value;
}

enum { AB_EXACT = 1, AB_LOWER = 2, AB_UPPER = 3 };
enum { AB_INFINITY = 30000, AB_MATE = 29000 };

static AlphaBetaHashEntry *ab_entry(SearchJob *job, uint64_t key) {
    if (job->ab_hash == NULL || job->ab_hash_capacity == 0) return NULL;
    return &job->ab_hash[key & (job->ab_hash_capacity - 1U)];
}

static void ab_store(SearchJob *job, uint64_t key, int score, int depth,
                     uint8_t bound, ShogiMove move) {
    AlphaBetaHashEntry *entry = ab_entry(job, key);
    if (entry == NULL) return;
    if (entry->key != 0 && entry->key != key && entry->depth > depth) return;
    *entry = (AlphaBetaHashEntry){key, (int16_t)score, (int8_t)depth, bound, move};
}

static int ab_move_order(const SearchJob *job, const ShogiPosition *position,
                         ShogiMove move, ShogiMove tt_move, unsigned ply) {
    int score = same_search_move(move, tt_move) ? 10000000 : 0;
    if (ply < SEARCH_MAX_PV) {
        if (same_search_move(move, job->ab_killers[ply][0])) score += 500000;
        else if (same_search_move(move, job->ab_killers[ply][1])) score += 400000;
    }
    unsigned from = move.from == SHOGI_SQ_NONE ? SHOGI_SQUARES : move.from;
    if (from <= SHOGI_SQUARES && move.to < SHOGI_SQUARES)
        score += job->ab_history[position->side][from][move.to] / 32;
    if (move.from != SHOGI_SQ_NONE && position->board[move.to] != SHOGI_EMPTY) {
        int victim = piece_value(shogi_piece_type(position->board[move.to]));
        int attacker = piece_value(shogi_piece_type(position->board[move.from]));
        score += 100000 + victim * 16 - attacker;
    }
    if (move.promote) score += 500;
    if (move.from == SHOGI_SQ_NONE) score += 100;
    return score;
}

static int ab_static_evaluation(WorkerContext *worker,
                                const ShogiPosition *position) {
    int score = static_evaluation(worker, position, worker->job->root_side);
    return position->side == worker->job->root_side ? score : -score;
}

static int ab_terminal_score(const SearchJob *job, const ShogiPosition *position,
                             ShogiResult result, unsigned ply) {
    if (result == SHOGI_RESULT_DRAW) return 0;
    ShogiResult side_win = position->side == SHOGI_BLACK ?
        SHOGI_RESULT_BLACK_WIN : SHOGI_RESULT_WHITE_WIN;
    int distance = ply < (unsigned)(AB_MATE - 1) ? (int)ply : AB_MATE - 1;
    (void)job;
    return result == side_win ? AB_MATE - distance : -AB_MATE + distance;
}

static bool ab_is_capture(const ShogiPosition *position, ShogiMove move) {
    return move.from != SHOGI_SQ_NONE && move.to < SHOGI_SQUARES &&
           position->board[move.to] != SHOGI_EMPTY;
}

static int ab_capture_gain(const ShogiPosition *position, ShogiMove move) {
    int gain = 0;
    if (ab_is_capture(position, move))
        gain += piece_value(shogi_piece_type(position->board[move.to]));
    if (move.promote && move.from != SHOGI_SQ_NONE)
        gain += piece_value(shogi_piece_type(position->board[move.from])) / 2;
    return gain;
}

static int ab_quiescence(WorkerContext *worker, ShogiPosition *position,
                         unsigned depth, int alpha, int beta, unsigned ply,
                         bool count_node) {
    SearchJob *job = worker->job;
    if (should_stop(job)) return ab_static_evaluation(worker, position);
    if (count_node)
        atomic_fetch_add_explicit(&job->simulations, 1, memory_order_relaxed);

    ShogiMove moves[SHOGI_MAX_MOVES];
    size_t count = 0;
    ShogiResult result = shogi_game_result_with_moves_mut(
        position, moves, SHOGI_MAX_MOVES, &count);
    if (result != SHOGI_RESULT_ONGOING)
        return ab_terminal_score(job, position, result, ply);

    bool in_check = shogi_is_in_check(position, position->side);
    int best = -AB_INFINITY;
    if (!in_check) {
        int stand_pat = ab_static_evaluation(worker, position);
        best = stand_pat;
        if (stand_pat >= beta) return stand_pat;
        if (stand_pat > alpha) alpha = stand_pat;
        if (depth == 0) return stand_pat;
    }

    TacticalMove tactical[SHOGI_MAX_MOVES];
    size_t tactical_count = 0;
    for (size_t index = 0; index < count; ++index) {
        ShogiMove move = moves[index];
        bool gives_check = false;
        int score = tactical_move_score(position, move, &gives_check);
        if (in_check || ab_is_capture(position, move) || move.promote || score >= 750)
            tactical[tactical_count++] = (TacticalMove){move, score, gives_check};
    }
    if (tactical_count == 0) return best == -AB_INFINITY ?
        ab_static_evaluation(worker, position) : best;

    for (size_t index = 0; index < tactical_count; ++index) {
        size_t selected = index;
        for (size_t candidate = index + 1; candidate < tactical_count; ++candidate) {
            if (tactical[candidate].score > tactical[selected].score)
                selected = candidate;
        }
        if (selected != index) {
            TacticalMove swap = tactical[index];
            tactical[index] = tactical[selected];
            tactical[selected] = swap;
        }
        /* If even the material swing cannot raise the stand-pat score, this
         * capture cannot affect alpha.  Keep checks and all evasions: the
         * tactical move score above deliberately marks those separately. */
        if (!in_check && depth != 0 && !tactical[index].gives_check &&
            ab_capture_gain(position, tactical[index].move) != 0 &&
            best + ab_capture_gain(position, tactical[index].move) +
                (int)job->options.quiescence_margin < alpha)
            continue;
        ShogiUndo undo;
        if (!worker_make_move(worker, position, tactical[index].move, &undo)) continue;
        unsigned next_depth = depth == 0 ? 0 : depth - 1;
        int score = -ab_quiescence(worker, position, next_depth,
                                   -beta, -alpha, ply + 1, true);
        (void)worker_unmake_move(worker, position, &undo);
        if (score > best) best = score;
        if (score > alpha) alpha = score;
        if (alpha >= beta || should_stop(job)) break;
    }
    return best == -AB_INFINITY ? ab_static_evaluation(worker, position) : best;
}

static int alpha_beta(WorkerContext *worker, ShogiPosition *position, int depth,
                      int alpha, int beta, unsigned ply, unsigned extensions) {
    SearchJob *job = worker->job;
    int alpha_original = alpha;
    int beta_original = beta;
    if (should_stop(job)) return ab_static_evaluation(worker, position);
    atomic_fetch_add_explicit(&job->simulations, 1, memory_order_relaxed);
    AlphaBetaHashEntry *entry = ab_entry(job, position->hash);
    ShogiMove tt_move = {SHOGI_SQ_NONE, SHOGI_SQ_NONE, 0, 0, 0};
    if (entry != NULL && entry->key == position->hash) {
        tt_move = entry->move;
        if (entry->depth >= depth) {
            if (entry->bound == AB_EXACT) return entry->score;
            if (entry->bound == AB_LOWER && entry->score > alpha) alpha = entry->score;
            if (entry->bound == AB_UPPER && entry->score < beta) beta = entry->score;
            if (alpha >= beta) return entry->score;
        }
    }
    ShogiMove moves[SHOGI_MAX_MOVES];
    size_t count = 0;
    ShogiResult result = shogi_game_result_with_moves_mut(position, moves,
                                                           SHOGI_MAX_MOVES, &count);
    if (result != SHOGI_RESULT_ONGOING)
        return ab_terminal_score(job, position, result, ply);
    if (depth <= 0)
        return ab_quiescence(worker, position, job->options.quiescence_depth,
                             alpha, beta, ply, false);

    bool in_check = shogi_is_in_check(position, position->side);
    if (in_check && extensions < 2U) {
        ++depth;
        ++extensions;
    }
    bool narrow_window = beta == alpha + 1;
    int static_score = 0;
    bool have_static_score = false;
    if (!in_check && narrow_window && depth <= 1 && beta < AB_MATE - 100) {
        static_score = ab_static_evaluation(worker, position);
        have_static_score = true;
        int margin = 120 * depth;
        if (static_score - margin >= beta) return static_score;
    }
    for (size_t i = 0; i < count; ++i) {
        size_t best = i;
        int best_order = ab_move_order(job, position, moves[i], tt_move, ply);
        for (size_t j = i + 1; j < count; ++j) {
            int order = ab_move_order(job, position, moves[j], tt_move, ply);
            if (order > best_order) { best = j; best_order = order; }
        }
        if (best != i) { ShogiMove swap = moves[i]; moves[i] = moves[best]; moves[best] = swap; }
    }
    int best = -AB_INFINITY;
    ShogiMove best_move = moves[0];
    for (size_t i = 0; i < count; ++i) {
        if (should_stop(job)) break;
        bool capture = ab_is_capture(position, moves[i]);
        bool quiet = !capture && !moves[i].promote;
        ShogiUndo undo;
        if (!worker_make_move(worker, position, moves[i], &undo)) continue;
        bool gives_check = shogi_is_in_check(position, position->side);
        int child_depth = depth - 1;
        if (i > 0 && depth <= 1 && narrow_window && quiet && !in_check &&
            !gives_check) {
            if (!have_static_score) {
                static_score = ab_static_evaluation(worker, position);
                have_static_score = true;
            }
            int futility_margin = depth == 1 ? 140 : 280;
            if (static_score + futility_margin <= alpha) {
                (void)worker_unmake_move(worker, position, &undo);
                continue;
            }
        }
        int reduction = 0;
        if (depth >= 3 && i >= 4 && quiet && !in_check && !gives_check)
            reduction = depth >= 5 && i >= 10 ? 2 : 1;
        int score;
        if (i == 0) {
            score = -alpha_beta(worker, position, child_depth,
                                -beta, -alpha, ply + 1, extensions);
        } else {
            score = -alpha_beta(worker, position, child_depth - reduction,
                                -alpha - 1, -alpha, ply + 1, extensions);
            if (reduction != 0 && score > alpha)
                score = -alpha_beta(worker, position, child_depth,
                                    -alpha - 1, -alpha, ply + 1, extensions);
            if (score > alpha && score < beta)
                score = -alpha_beta(worker, position, child_depth,
                                    -beta, -alpha, ply + 1, extensions);
        }
        (void)worker_unmake_move(worker, position, &undo);
        if (score > best) { best = score; best_move = moves[i]; }
        if (score > alpha) alpha = score;
        if (alpha >= beta) {
            ShogiMove cutoff_move = moves[i];
            if (quiet && ply < SEARCH_MAX_PV) {
                if (!same_search_move(job->ab_killers[ply][0], cutoff_move)) {
                    job->ab_killers[ply][1] = job->ab_killers[ply][0];
                    job->ab_killers[ply][0] = cutoff_move;
                }
                unsigned from = cutoff_move.from == SHOGI_SQ_NONE ?
                    SHOGI_SQUARES : cutoff_move.from;
                int *history = &job->ab_history[position->side][from][cutoff_move.to];
                int bonus = depth * depth * 16;
                *history = *history > 1000000 - bonus ? 1000000 : *history + bonus;
            }
            break;
        }
    }
    if (best == -AB_INFINITY) best = ab_static_evaluation(worker, position);
    uint8_t bound = best <= alpha_original ? AB_UPPER :
                    best >= beta_original ? AB_LOWER : AB_EXACT;
    ab_store(job, position->hash, best, depth, bound, best_move);
    return best;
}

typedef struct {
    TreeChild child;
    int score;
} AlphaBetaRootCandidate;

static void alpha_beta_root_prepass(WorkerContext *worker) {
    SearchJob *job = worker->job;
    AlphaBetaRootCandidate candidates[SHOGI_MAX_MOVES];
    unsigned total = job->root->move_count;
    for (unsigned index = 0; index < total; ++index) {
        candidates[index].child = job->root->children[index];
        candidates[index].score = -AB_INFINITY +
            ab_move_order(job, &job->root_position,
                          candidates[index].child.move,
                          (ShogiMove){SHOGI_SQ_NONE, SHOGI_SQ_NONE, 0, 0, 0},
                          0) / 100000;
    }
    unsigned evaluated = 0;
    for (unsigned index = 0; index < total; ++index) {
        if (should_stop(job)) break;
        TreeChild child = job->root->children[index];
        ShogiPosition next = job->root_position;
        ShogiUndo undo;
        if (!worker_make_move(worker, &next, child.move, &undo)) continue;
        atomic_fetch_add_explicit(&job->simulations, 1, memory_order_relaxed);
        ShogiMove result_moves[SHOGI_MAX_MOVES];
        ShogiResult result = shogi_game_result_with_moves_mut(&next, result_moves,
                                                              SHOGI_MAX_MOVES, NULL);
        int score = result == SHOGI_RESULT_ONGOING ?
            -ab_static_evaluation(worker, &next) :
            -ab_terminal_score(job, &next, result, 1);
        (void)worker_unmake_move(worker, &next, &undo);
        candidates[index].score = score;
        ++evaluated;
    }
    if (evaluated == 0) return;
    for (unsigned index = 1; index < total; ++index) {
        AlphaBetaRootCandidate saved = candidates[index];
        unsigned insertion = index;
        while (insertion > 0 && candidates[insertion - 1].score < saved.score) {
            candidates[insertion] = candidates[insertion - 1];
            --insertion;
        }
        candidates[insertion] = saved;
    }
    for (unsigned index = 0; index < total; ++index) {
        int bounded = candidates[index].score;
        if (bounded > 1000) bounded = 1000;
        if (bounded < -1000) bounded = -1000;
        candidates[index].child.visits = 1;
        candidates[index].child.value =
            (uint64_t)(bounded + 1000) * VALUE_SCALE / 2000U;
        job->root->children[index] = candidates[index].child;
    }
    job->ab_best_move = candidates[0].child.move;
    job->ab_best_score = candidates[0].score;
    job->ab_best_valid = true;
    if (evaluated == total) job->ab_completed_depth = 1;
}

static bool alpha_beta_root_depth(WorkerContext *worker, int depth,
                                  int alpha, int beta, int *root_scores,
                                  ShogiMove *best_move, int *best_score) {
    SearchJob *job = worker->job;
    int local_best = -AB_INFINITY;
    ShogiMove local_move = job->root->children[0].move;
    /* A narrow root search may stop after a fail-high, and a node limit may
     * stop an otherwise successful iteration before every child is visited.
     * Keep the previous iteration's ordering score for those children.  The
     * old uninitialized values made low-budget move ordering depend on stack
     * contents and could discard promising root moves on the next iteration. */
    for (unsigned i = 0; i < job->root->move_count; ++i) {
        uint64_t value = __atomic_load_n(&job->root->children[i].value,
                                         __ATOMIC_RELAXED);
        if (value > VALUE_SCALE) value = VALUE_SCALE;
        root_scores[i] = (int)((value * 2000U) / VALUE_SCALE) - 1000;
    }
    for (unsigned i = 0; i < job->root->move_count; ++i) {
        if (should_stop(job)) return false;
        ShogiMove root_move = job->root->children[i].move;
        ShogiPosition next = job->root_position;
        ShogiUndo undo;
        if (!worker_make_move(worker, &next, root_move, &undo))
            continue;
        int score;
        if (i == 0) {
            score = -alpha_beta(worker, &next, depth - 1,
                                -beta, -alpha, 1, 0);
        } else {
            score = -alpha_beta(worker, &next, depth - 1,
                                -alpha - 1, -alpha, 1, 0);
            if (score > alpha && score < beta)
                score = -alpha_beta(worker, &next, depth - 1,
                                    -beta, -alpha, 1, 0);
        }
        (void)worker_unmake_move(worker, &next, &undo);
        if (should_stop(job)) return false;
        root_scores[i] = score;
        if (score > local_best) {
            local_best = score;
            local_move = root_move;
        }
        if (score > alpha) alpha = score;
        if (alpha >= beta) break;
    }
    if (should_stop(job)) return false;
    *best_move = local_move;
    *best_score = local_best;
    return true;
}

static void run_alpha_beta(WorkerContext *worker) {
    SearchJob *job = worker->job;
    int max_depth = job->limits.depth > 0 ? job->limits.depth : 64;
    alpha_beta_root_prepass(worker);
    /* The prepass orders every legal move and guarantees a valid fallback,
     * but it cannot replace depth one: quiescence must reject superficially
     * good captures whose recapture is just beyond the root move. */
    for (int depth = 1; depth <= max_depth && !should_stop(job); ++depth) {
        for (unsigned i = 1; i < job->root->move_count; ++i) {
            TreeChild saved = job->root->children[i];
            unsigned j = i;
            while (j > 0 && job->root->children[j - 1].value < saved.value) {
                job->root->children[j] = job->root->children[j - 1];
                --j;
            }
            job->root->children[j] = saved;
        }
        int previous_score = job->ab_best_score;
        int best_score = -AB_INFINITY;
        ShogiMove best_move = job->root->children[0].move;
        int root_scores[SHOGI_MAX_MOVES];
        unsigned aspiration = job->options.aspiration_window;
        if (aspiration == 0) aspiration = SEARCH_DEFAULT_ASPIRATION_WINDOW;
        int window_alpha = previous_score - (int)aspiration;
        int window_beta = previous_score + (int)aspiration;
        if (window_alpha < -AB_INFINITY) window_alpha = -AB_INFINITY;
        if (window_beta > AB_INFINITY) window_beta = AB_INFINITY;
        if (!alpha_beta_root_depth(worker, depth, window_alpha, window_beta,
                                   root_scores, &best_move, &best_score)) break;
        if (best_score <= window_alpha || best_score >= window_beta) {
            if (!alpha_beta_root_depth(worker, depth, -AB_INFINITY, AB_INFINITY,
                                       root_scores, &best_move,
                                       &best_score)) break;
        }
        for (unsigned i = 0; i < job->root->move_count; ++i) {
            int bounded = root_scores[i];
            if (bounded > 1000) bounded = 1000;
            if (bounded < -1000) bounded = -1000;
            job->root->children[i].visits = 1;
            job->root->children[i].value =
                (uint64_t)(bounded + 1000) * VALUE_SCALE / 2000U;
        }
        job->ab_best_move = best_move;
        job->ab_best_score = best_score;
        job->ab_completed_depth = depth;
        job->ab_best_valid = true;
    }
    /* Extremely small limits may stop before depth one is complete.  In that
     * case the best move from the searched root prefix is still preferable to
     * the generic lexical fallback. */
    if (!job->ab_best_valid &&
        atomic_load_explicit(&job->simulations, memory_order_relaxed) != 0)
        job->ab_best_valid = true;
}

static void backpropagate(WorkerContext *worker, const SearchPath *path, double value,
                          uint64_t *root_visits, uint64_t *root_values) {
    SearchJob *job = worker->job;
    uint64_t scaled = (uint64_t)(value * (double)VALUE_SCALE);
    ++worker->root->visits;
    worker->root->value += scaled;
    /* Worker trees own selection statistics.  The shared root's aggregate
     * visits/value are not consumed by selection or reporting; updating them
     * here only creates a cross-core cache-line hotspot.  Root-child stats
     * below remain shared because they determine the final move. */
    for (size_t index = 0; index < path->length; ++index) {
        TreeNode *parent = path->parents[index];
        unsigned child_index = path->child_indices[index];
        TreeChild *edge = &parent->children[child_index];
        --edge->virtual_loss;
        ++edge->visits;
        edge->value += scaled;
        child_selection_update(parent, child_index);
        TreeNode *node = edge->node;
        if (node != NULL) {
            ++node->visits;
            node->value += scaled;
        }
    }
    if (path->length != 0) {
        unsigned root_index = path->child_indices[0];
        if (root_index < job->root->move_count) {
            if (root_visits != NULL) {
                ++root_visits[root_index];
                root_values[root_index] += scaled;
            } else {
                TreeChild *published = &job->root->children[root_index];
                __atomic_fetch_add(&published->visits, 1, __ATOMIC_RELAXED);
                __atomic_fetch_add(&published->value, scaled, __ATOMIC_RELAXED);
            }
        }
    }
}

typedef struct {
    ShogiPosition position;
    ShogiUndo undos[SEARCH_MAX_PATH];
    size_t undo_length;
    SearchPath path;
    void *eval_state;
    double value;
    bool terminal;
} NeuralLane;

/* ShogiPosition reserves enough repetition history for an entire game.  A
 * neural lane only needs the live prefix: make/unmake never observes entries
 * beyond history_length.  Avoid clearing and copying roughly 40 KiB of dead
 * history for every leaf in every batch. */
static void position_copy_active(ShogiPosition *destination,
                                 const ShogiPosition *source) {
    memcpy(destination->board, source->board, sizeof(destination->board));
    memcpy(destination->hand, source->hand, sizeof(destination->hand));
    destination->side = source->side;
    destination->move_number = source->move_number;
    destination->hash = source->hash;
    destination->king_square[SHOGI_BLACK] = source->king_square[SHOGI_BLACK];
    destination->king_square[SHOGI_WHITE] = source->king_square[SHOGI_WHITE];
    destination->history_length = source->history_length;
    memcpy(destination->history, source->history,
           source->history_length * sizeof(destination->history[0]));
    memcpy(destination->history_mover, source->history_mover,
           source->history_length * sizeof(destination->history_mover[0]));
    memcpy(destination->history_check, source->history_check,
           source->history_length * sizeof(destination->history_check[0]));
}

static bool prepare_neural_lane(WorkerContext *worker, NeuralLane *lane) {
    SearchJob *job = worker->job;
    TreeNode *node = worker->root;
    lane->value = 0.5;
    lane->terminal = false;
    lane->undo_length = 0;
    lane->path.length = 0;
    for (int depth = 0; depth < SEARCH_NEURAL_MAX_DEPTH; ++depth) {
        size_t count = 0;
        if (node->expanded) {
            if (node->terminal) {
                lane->value = node->terminal_value;
                lane->terminal = true;
                return true;
            }
            count = node->move_count;
        } else {
            ShogiMove moves[SHOGI_MAX_MOVES];
            ShogiResult result = shogi_game_result_with_moves_mut(
                &lane->position, moves, SHOGI_MAX_MOVES, &count);
            if (result != SHOGI_RESULT_ONGOING) {
                if (result == SHOGI_RESULT_DRAW) lane->value = 0.5;
                else lane->value = result ==
                    (job->root_side == SHOGI_BLACK ? SHOGI_RESULT_BLACK_WIN : SHOGI_RESULT_WHITE_WIN)
                    ? 1.0 : 0.0;
                if (!node_expand(&worker->tree, node, &lane->position, NULL, 0)) return false;
                node->terminal = true;
                node->terminal_value = lane->value;
                lane->terminal = true;
                return true;
            }
            if (!node_expand(&worker->tree, node, &lane->position, moves, count) || count == 0)
                break;
        }
        TreeChild *expanded = expand_one(&worker->tree, node, &lane->position,
                                         &lane->undos[lane->undo_length]);
        if (expanded != NULL) {
            if (lane->eval_state != NULL &&
                !shogi_evaluator_state_make(worker->evaluator,
                                            lane->eval_state, &lane->position,
                                            &lane->undos[lane->undo_length])) {
                (void)shogi_unmake_move(&lane->position, &lane->undos[lane->undo_length]);
                return false;
            }
            ++lane->undo_length;
            ++expanded->virtual_loss;
            child_selection_update(node, (unsigned)(expanded - node->children));
            if (!path_push(&lane->path, node, expanded)) return false;
            return true;
        }
        if (lane->path.length >= SEARCH_MAX_PATH || lane->undo_length >= SEARCH_MAX_PATH)
            break;
        TreeChild *selected = select_child(job, node, lane->position.side == job->root_side);
        if (selected == NULL) break;
        if (!path_push(&lane->path, node, selected)) break;
        if (!state_make(worker->evaluator, lane->eval_state, &lane->position,
                        selected->move, &lane->undos[lane->undo_length])) break;
        ++lane->undo_length;
        TreeNode *next = selected->node;
        if (next == NULL) break;
        node = next;
    }
    return true;
}

static void finish_neural_lane(WorkerContext *worker, NeuralLane *lane,
                               uint64_t *root_visits, uint64_t *root_values) {
    if (worker->evaluator->state_rewind != NULL) {
        while (lane->undo_length > 0) {
            --lane->undo_length;
            (void)shogi_unmake_move(&lane->position,
                                    &lane->undos[lane->undo_length]);
        }
        (void)shogi_evaluator_state_rewind(worker->evaluator, lane->eval_state,
                                           &worker->job->root_position);
    } else {
        while (lane->undo_length > 0) {
            --lane->undo_length;
            (void)state_unmake(worker->evaluator, lane->eval_state,
                               &lane->position, &lane->undos[lane->undo_length]);
        }
    }
    backpropagate(worker, &lane->path, lane->value, root_visits, root_values);
}

static void run_neural_batch(WorkerContext *worker, size_t lane_count) {
    NeuralLane lanes[SEARCH_NEURAL_MAX_BATCH];
    const void *states[SEARCH_NEURAL_MAX_BATCH];
    int scores[SEARCH_NEURAL_MAX_BATCH];
    uint64_t root_visits[SHOGI_MAX_MOVES] = {0};
    uint64_t root_values[SHOGI_MAX_MOVES] = {0};
    size_t score_count = 0;
    for (size_t index = 0; index < lane_count; ++index) {
        position_copy_active(&lanes[index].position, &worker->job->root_position);
        lanes[index].eval_state = worker->neural_eval_states[index];
        lanes[index].undo_length = 0;
        lanes[index].path.length = 0;
        lanes[index].value = 0.5;
        lanes[index].terminal = false;
        if (!prepare_neural_lane(worker, &lanes[index])) {
            lanes[index].terminal = true;
            lanes[index].value = 0.5;
        }
        if (!lanes[index].terminal) states[score_count++] = lanes[index].eval_state;
    }
    if (score_count != 0) {
        if (!shogi_evaluator_state_score_batch(worker->evaluator,
                                               states, score_count, scores)) {
            for (size_t index = 0; index < score_count; ++index) scores[index] = 0;
        }
        size_t score_index = 0;
        for (size_t index = 0; index < lane_count; ++index) {
            if (lanes[index].terminal) continue;
            int score = scores[score_index++];
            if (score > 1500) score = 1500;
            if (score < -1500) score = -1500;
            lanes[index].value = 0.5 + (double)score / 3000.0;
        }
    }
    for (size_t index = 0; index < lane_count; ++index)
        finish_neural_lane(worker, &lanes[index], root_visits, root_values);
    for (unsigned index = 0; index < worker->job->root->move_count; ++index) {
        if (root_visits[index] == 0) continue;
        TreeChild *published = &worker->job->root->children[index];
        __atomic_fetch_add(&published->visits, root_visits[index], __ATOMIC_RELAXED);
        __atomic_fetch_add(&published->value, root_values[index], __ATOMIC_RELAXED);
    }
}

static size_t claim_simulation_batch(SearchJob *job, size_t capacity) {
    if (job->limits.nodes == 0) {
        if (should_stop(job)) return 0;
        atomic_fetch_add_explicit(&job->simulations, capacity, memory_order_relaxed);
        return capacity;
    }
    size_t claimed = 0;
    while (claimed < capacity && !should_stop(job)) {
        uint64_t current = atomic_load_explicit(&job->simulations, memory_order_relaxed);
        bool success = false;
        while (current < job->limits.nodes) {
            if (atomic_compare_exchange_weak_explicit(&job->simulations, &current,
                                                      current + 1, memory_order_relaxed,
                                                      memory_order_relaxed)) {
                success = true;
                break;
            }
        }
        if (!success) break;
        ++claimed;
    }
    return claimed;
}

static void *worker_main(void *opaque) {
    WorkerContext *worker = opaque;
    SearchJob *job = worker->job;
    (void)ts_thread_pin_allowed(worker->id);
    shogi_set_fast_check_bookkeeping(job->options.perpetual_check);
    worker->eval_cache_capacity = WORKER_EVAL_CACHE_CAPACITY;
    worker->eval_cache = calloc(worker->eval_cache_capacity, sizeof(*worker->eval_cache));
    if (worker->eval_cache == NULL) worker->eval_cache_capacity = 0;
    uint64_t rng = job->options.seed_auto ? monotonic_ns() ^ ((uint64_t)worker->id * UINT64_C(0x9e3779b9))
                                          : job->options.seed + (uint64_t)worker->id * UINT64_C(0x9e3779b97f4a7c15);
    ShogiPosition position = job->root_position;
    if (job->neural_mcts) {
        worker->neural_ready = true;
        unsigned batch = job->options.leaf_batch_size;
        if (batch == 0 || batch > SEARCH_NEURAL_MAX_BATCH) batch = SEARCH_NEURAL_MAX_BATCH;
        for (unsigned index = 0; index < batch; ++index) {
            worker->neural_eval_states[index] =
                shogi_evaluator_state_create(worker->evaluator, &position, job->root_side);
            if (worker->neural_eval_states[index] == NULL) worker->neural_ready = false;
        }
        if (!worker->neural_ready) {
            for (unsigned index = 0; index < batch; ++index)
                shogi_evaluator_state_destroy(worker->evaluator,
                                              worker->neural_eval_states[index]);
            worker->eval_state = shogi_evaluator_state_create(worker->evaluator,
                                                               &position, job->root_side);
        }
    } else {
        worker->eval_state = shogi_evaluator_state_create(worker->evaluator,
                                                           &position, job->root_side);
    }
    ShogiUndo undos[SEARCH_MAX_UNDO];
    if (job->options.mode == SEARCH_MODE_ALPHABETA) {
        if (worker->id == 0) run_alpha_beta(worker);
        atomic_fetch_add_explicit(&job->workers_done, 1, memory_order_release);
        shogi_evaluator_state_destroy(worker->evaluator, worker->eval_state);
        free(worker->eval_cache);
        free(worker);
        return NULL;
    }
    size_t local_capacity = (job->options.max_tree_nodes + job->worker_count - 1U) /
                            job->worker_count;
    if (local_capacity < 64U) local_capacity = 64U;
    if (!worker_tree_prepare(worker, local_capacity)) {
        atomic_fetch_add_explicit(&job->workers_done, 1, memory_order_release);
        shogi_evaluator_state_destroy(worker->evaluator, worker->eval_state);
        free(worker->eval_cache);
        free(worker);
        return NULL;
    }
    worker->root = tree_new_node(&worker->tree, position.hash);
    if (worker->root == NULL ||
        !node_expand(&worker->tree, worker->root, &position,
                     job->root->moves, job->root->move_count)) {
        atomic_fetch_add_explicit(&job->workers_done, 1, memory_order_release);
        worker_tree_release(worker);
        shogi_evaluator_state_destroy(worker->evaluator, worker->eval_state);
        free(worker->eval_cache);
        free(worker);
        return NULL;
    }
    while (!should_stop(job)) {
        if (job->neural_mcts && worker->neural_ready) {
            size_t batch = job->options.leaf_batch_size;
            if (batch == 0 || batch > SEARCH_NEURAL_MAX_BATCH) batch = SEARCH_NEURAL_MAX_BATCH;
            size_t claimed = claim_simulation_batch(job, batch);
            if (claimed == 0) break;
            run_neural_batch(worker, claimed);
            continue;
        }
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
        double value = run_simulation(worker, &position, undos, &rng);
        (void)value;
    }
    atomic_fetch_add_explicit(&job->workers_done, 1, memory_order_release);
    worker_tree_release(worker);
    shogi_evaluator_state_destroy(worker->evaluator, worker->eval_state);
    if (job->neural_mcts && worker->neural_ready) {
        unsigned batch = job->options.leaf_batch_size;
        if (batch == 0 || batch > SEARCH_NEURAL_MAX_BATCH) batch = SEARCH_NEURAL_MAX_BATCH;
        for (unsigned index = 0; index < batch; ++index)
            shogi_evaluator_state_destroy(worker->evaluator,
                                          worker->neural_eval_states[index]);
    }
    free(worker->eval_cache);
    free(worker);
    return NULL;
}

static TreeChild *best_root_child(const SearchJob *job, uint64_t *best_visits) {
    if (job == NULL || job->root == NULL) return NULL;
    if (job->options.mode == SEARCH_MODE_ALPHABETA && job->ab_best_valid) {
        for (unsigned index = 0; index < job->root->move_count; ++index) {
            if (same_search_move(job->root->children[index].move,
                                 job->ab_best_move)) {
                if (best_visits != NULL)
                    *best_visits = __atomic_load_n(&job->root->children[index].visits,
                                                   __ATOMIC_RELAXED);
                return &job->root->children[index];
            }
        }
    }
    TreeChild *best = NULL;
    uint64_t visits_for_best = 0;
    char best_text[16] = {0};
    for (unsigned index = 0; index < job->root->move_count; ++index) {
        TreeChild *child = &job->root->children[index];
        uint64_t visits = __atomic_load_n(&child->visits, __ATOMIC_RELAXED);
        if (visits == 0 && child->node == NULL) continue;
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
        if (child->node == NULL) continue;
        uint64_t visits = child->visits;
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
        TreeNode *node = child->node;
        child = best_line_child(node);
    }
    return length;
}

static int root_score_cp(const TreeChild *child) {
    uint64_t visits = __atomic_load_n(&child->visits, __ATOMIC_RELAXED);
    if (visits == 0) return 0;
    uint64_t value = __atomic_load_n(&child->value, __ATOMIC_RELAXED);
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
    if (job->options.mode == SEARCH_MODE_ALPHABETA && job->ab_best_valid) {
        for (unsigned index = 0; index < job->root->move_count; ++index) {
            TreeChild *child = &job->root->children[index];
            if (!same_search_move(child->move, job->ab_best_move)) continue;
            used[index] = true;
            lines[0].move = child->move;
            lines[0].visits = __atomic_load_n(&child->visits, __ATOMIC_RELAXED);
            lines[0].score_cp = root_score_cp(child);
            lines[0].pv_length = line_principal_variation(
                child, lines[0].pv, SEARCH_MAX_PV);
            output = 1;
            break;
        }
    }
    while (output < capacity) {
        TreeChild *best = NULL;
        unsigned best_index = 0;
        uint64_t best_visits = 0;
        char best_text[16] = {0};
        for (unsigned index = 0; index < job->root->move_count; ++index) {
            if (used[index]) continue;
            TreeChild *child = &job->root->children[index];
            uint64_t visits = __atomic_load_n(&child->visits, __ATOMIC_RELAXED);
            if (visits == 0 && child->node == NULL) continue;
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
            uint64_t visits = __atomic_load_n(&child->visits, __ATOMIC_RELAXED);
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
    unsigned count = ts_thread_allowed_count();
    if (count > 8) count = 8;
    return count;
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
    position_copy_active(&job->root_position, position);
    job->limits = *limits;
    job->options = *options;
    if (job->options.mode != SEARCH_MODE_ALPHABETA && job->options.threads == 0)
        job->options.threads = default_threads();
    if (job->options.mode == SEARCH_MODE_ALPHABETA) job->options.threads = 1;
    if (job->options.threads > 64) job->options.threads = 64;
    if (job->options.max_tree_nodes < 1000) job->options.max_tree_nodes = DEFAULT_MAX_TREE_NODES;
    job->root_side = position->side;
    for (unsigned ply = 0; ply < SEARCH_MAX_PV; ++ply)
        for (unsigned slot = 0; slot < 2; ++slot) {
            job->ab_killers[ply][slot].from = SHOGI_SQ_NONE;
            job->ab_killers[ply][slot].to = SHOGI_SQ_NONE;
        }
    if (job->options.rollout_depth == 0) job->options.rollout_depth = SEARCH_DEFAULT_ROLLOUT_DEPTH;
    if (job->options.quiescence_depth > 8) job->options.quiescence_depth = SEARCH_DEFAULT_QUIESCENCE_DEPTH;
    if (job->options.exploration_milli == 0) job->options.exploration_milli = SEARCH_DEFAULT_EXPLORATION_MILLI;
    if (job->options.aspiration_window == 0)
        job->options.aspiration_window = SEARCH_DEFAULT_ASPIRATION_WINDOW;
    job->exploration_constant = (float)job->options.exploration_milli / 1000.0f;
    if (job->options.multi_pv == 0) job->options.multi_pv = SEARCH_DEFAULT_MULTIPV;
    if (job->options.multi_pv > SEARCH_MAX_MULTIPV) job->options.multi_pv = SEARCH_MAX_MULTIPV;
    if (job->options.leaf_batch_size == 0) {
        job->options.leaf_batch_size = job->options.evaluator != NULL &&
            job->options.evaluator->state_score_batch_size != 0
            ? job->options.evaluator->state_score_batch_size : SEARCH_NEURAL_MAX_BATCH;
    }
    if (job->options.leaf_batch_size > SEARCH_NEURAL_MAX_BATCH)
        job->options.leaf_batch_size = SEARCH_NEURAL_MAX_BATCH;
    bool stateful_evaluator = job->options.evaluator != NULL &&
        job->options.evaluator->state_create != NULL &&
        job->options.evaluator->state_make != NULL &&
        job->options.evaluator->state_unmake != NULL &&
        job->options.evaluator->state_score != NULL;
    job->neural_mcts = job->options.mode == SEARCH_MODE_MCTS &&
        (job->options.mcts_policy == SEARCH_MCTS_NEURAL ||
         (job->options.mcts_policy == SEARCH_MCTS_AUTO && stateful_evaluator));
    atomic_init(&job->stop, false);
    atomic_init(&job->pondering, limits->ponder);
    atomic_init(&job->workers_done, 0);
    atomic_init(&job->simulations, 0);
    atomic_init(&job->deadline_ns, search_deadline(limits, position->side));
    job->start_ns = monotonic_ns();
    if (!tree_init(&job->tree, 1U)) {
        free(job);
        return NULL;
    }
    if (job->options.mode == SEARCH_MODE_ALPHABETA) {
        job->ab_hash_capacity = 1U << 18;
        job->ab_hash = calloc(job->ab_hash_capacity, sizeof(*job->ab_hash));
        if (job->ab_hash == NULL) {
            tree_destroy(&job->tree);
            free(job);
            return NULL;
        }
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
        WorkerContext *worker = calloc(1, sizeof(*worker));
        if (worker == NULL) {
            atomic_store(&job->stop, true);
            job->worker_count = index;
            search_join(job, NULL);
            search_destroy(job);
            return NULL;
        }
        worker->job = job;
        worker->id = index;
        worker->evaluator = job->options.evaluator;
        if (job->options.context != NULL && job->options.mode == SEARCH_MODE_MCTS) {
            SearchContextWorker *resource = &job->options.context->workers[index];
            bool expected = false;
            if (atomic_compare_exchange_strong_explicit(
                    &resource->in_use, &expected, true,
                    memory_order_acq_rel, memory_order_acquire))
                worker->persistent_resource = resource;
        }
        if (job->options.evaluator_replicas != NULL &&
            job->options.evaluator_replica_count > 0) {
            unsigned replica = job->options.evaluator_replica_count == 4U &&
                               job->worker_count >= 32U ? index & 3U :
                               index * job->options.evaluator_replica_count /
                               job->worker_count;
            if (replica >= job->options.evaluator_replica_count)
                replica = job->options.evaluator_replica_count - 1U;
            worker->evaluator = &job->options.evaluator_replicas[replica];
        }
        if (ts_thread_create(&job->workers[index], worker_main, worker) != 0) {
            if (worker->persistent_resource != NULL)
                atomic_store_explicit(&worker->persistent_resource->in_use, false,
                                      memory_order_release);
            free(worker);
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
    return atomic_load_explicit((atomic_uint *)&job->workers_done,
                                memory_order_acquire) >= job->worker_count;
}

bool search_is_infinite(const SearchJob *job) {
    return job != NULL && job->limits.infinite;
}

bool search_is_pondering(const SearchJob *job) {
    return job != NULL && atomic_load_explicit((atomic_bool *)&job->pondering,
                                               memory_order_acquire);
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
    progress->nodes = atomic_load_explicit(
        (atomic_uint_least64_t *)&job->simulations, memory_order_relaxed);
    uint64_t now = monotonic_ns();
    uint64_t elapsed = now >= job->start_ns ? now - job->start_ns : 0;
    progress->time_ms = elapsed / UINT64_C(1000000);
    progress->depth = job->options.mode == SEARCH_MODE_ALPHABETA ?
        job->ab_completed_depth : 0;
    if (elapsed != 0) progress->nps = progress->nodes * UINT64_C(1000000000) / elapsed;
    TreeChild *best = best_root_child(job, NULL);
    if (best == NULL && job->root != NULL && job->root->move_count > 0) best = &job->root->children[0];
    if (best != NULL) {
        progress->has_move = true;
        progress->move = best->move;
        uint64_t visits = __atomic_load_n(&best->visits, __ATOMIC_RELAXED);
        uint64_t value = __atomic_load_n(&best->value, __ATOMIC_RELAXED);
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
    free(job->ab_hash);
    tree_destroy(&job->tree);
    free(job);
}
