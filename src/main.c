#define _POSIX_C_SOURCE 200809L

#include "search.h"
#include "shogi.h"
#include "nnue.h"
#include "nnue_data.h"
#include "thread.h"

#include <errno.h>
#include <poll.h>
#include <stdbool.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/types.h>
#include <time.h>
#include <unistd.h>
#include <math.h>

typedef struct {
    ShogiPosition position;
    SearchOptions options;
    ShogiEvaluator evaluator;
    ShogiEvaluator nnue_evaluators[4];
    ShogiNnueModel nnue_replicas[4];
    unsigned nnue_replica_count;
    SearchContext *search_context;
    SearchJob *job;
    uint64_t last_info_ns;
    bool quit;
} Application;

typedef struct {
    ShogiNnueState nnue;
    ShogiNnueDelta *deltas;
    int32_t *rebuild_sums;
    int32_t *root_sum;
    uint64_t king_cache_hash[32];
    uint8_t king_cache_valid[32];
    int32_t *king_cache_sums;
    size_t depth;
    size_t capacity;
} NnueEvaluatorState;

static int nnue_evaluator_callback(void *userdata, const ShogiPosition *position,
                                   ShogiColor perspective) {
    return shogi_nnue_evaluate_position((const ShogiNnueModel *)userdata,
                                         position, perspective);
}

static void *nnue_state_create_callback(void *userdata,
                                        const ShogiPosition *position,
                                        ShogiColor perspective) {
    NnueEvaluatorState *state = calloc(1, sizeof(*state));
    if (state == NULL) return NULL;
    const ShogiNnueModel *model = userdata;
    state->capacity = 256;
    state->deltas = malloc(state->capacity * sizeof(*state->deltas));
    state->rebuild_sums = malloc(state->capacity * model->hidden_dim *
                                 sizeof(*state->rebuild_sums));
    state->root_sum = malloc(model->hidden_dim * sizeof(*state->root_sum));
    state->king_cache_sums = malloc(32U * model->hidden_dim *
                                    sizeof(*state->king_cache_sums));
    if (state->deltas == NULL || state->rebuild_sums == NULL || state->root_sum == NULL ||
        state->king_cache_sums == NULL ||
        !shogi_nnue_state_init(&state->nnue, userdata, perspective) ||
        !shogi_nnue_state_reset(&state->nnue, position)) {
        shogi_nnue_state_destroy(&state->nnue);
        free(state->deltas);
        free(state->rebuild_sums);
        free(state->root_sum);
        free(state->king_cache_sums);
        free(state);
        return NULL;
    }
    memcpy(state->root_sum, state->nnue.sum,
           model->hidden_dim * sizeof(*state->root_sum));
    return state;
}

static void nnue_state_destroy_callback(void *opaque) {
    NnueEvaluatorState *state = opaque;
    if (state == NULL) return;
    shogi_nnue_state_destroy(&state->nnue);
    free(state->deltas);
    free(state->rebuild_sums);
    free(state->root_sum);
    free(state->king_cache_sums);
    free(state);
}

static bool nnue_state_make_callback(void *opaque, const ShogiPosition *after,
                                     const ShogiUndo *undo) {
    NnueEvaluatorState *state = opaque;
    if (state->depth == state->capacity) {
        size_t capacity = state->capacity * 2U;
        ShogiNnueDelta *deltas = realloc(state->deltas,
                                         capacity * sizeof(*deltas));
        int32_t *rebuild_sums = realloc(
            state->rebuild_sums, capacity * state->nnue.hidden_dim * sizeof(*rebuild_sums));
        if (deltas == NULL || rebuild_sums == NULL) {
            if (deltas != NULL) state->deltas = deltas;
            if (rebuild_sums != NULL) state->rebuild_sums = rebuild_sums;
            return false;
        }
        state->deltas = deltas;
        state->rebuild_sums = rebuild_sums;
        state->capacity = capacity;
    }
    bool rebuild = undo->moving_piece != SHOGI_EMPTY &&
        (undo->moving_piece & 0x0fU) == SHOGI_KING &&
        (ShogiColor)undo->color == state->nnue.perspective;
    if (rebuild) {
        memcpy(state->rebuild_sums + state->depth * state->nnue.hidden_dim,
               state->nnue.sum, state->nnue.hidden_dim * sizeof(*state->nnue.sum));
        size_t slot = (size_t)after->hash & 31U;
        if (state->king_cache_valid[slot] &&
            state->king_cache_hash[slot] == after->hash) {
            memset(&state->deltas[state->depth], 0,
                   sizeof(state->deltas[state->depth]));
            state->deltas[state->depth].rebuild = 1;
            memcpy(state->nnue.sum,
                   state->king_cache_sums + slot * state->nnue.hidden_dim,
                   state->nnue.hidden_dim * sizeof(*state->nnue.sum));
            ++state->depth;
            return true;
        }
    }
    if (!shogi_nnue_state_apply_move(&state->nnue, after, undo,
                                     &state->deltas[state->depth])) return false;
    if (rebuild) {
        size_t slot = (size_t)after->hash & 31U;
        memcpy(state->king_cache_sums + slot * state->nnue.hidden_dim,
               state->nnue.sum, state->nnue.hidden_dim * sizeof(*state->nnue.sum));
        state->king_cache_hash[slot] = after->hash;
        state->king_cache_valid[slot] = 1;
    }
    ++state->depth;
    return true;
}

static bool nnue_state_unmake_callback(void *opaque, const ShogiPosition *before,
                                       const ShogiUndo *undo) {
    NnueEvaluatorState *state = opaque;
    (void)undo;
    if (state->depth == 0) return false;
    --state->depth;
    if (state->deltas[state->depth].rebuild) {
        memcpy(state->nnue.sum,
               state->rebuild_sums + state->depth * state->nnue.hidden_dim,
               state->nnue.hidden_dim * sizeof(*state->nnue.sum));
        state->nnue.valid = true;
        return true;
    }
    return shogi_nnue_state_unapply_move(&state->nnue, before,
                                         &state->deltas[state->depth]);
}

static int nnue_state_score_callback(const void *opaque) {
    const NnueEvaluatorState *state = opaque;
    return shogi_nnue_state_evaluate(&state->nnue);
}

static bool nnue_state_rewind_callback(void *opaque,
                                       const ShogiPosition *root) {
    NnueEvaluatorState *state = opaque;
    (void)root;
    if (state == NULL || state->root_sum == NULL || state->nnue.sum == NULL)
        return false;
    memcpy(state->nnue.sum, state->root_sum,
           state->nnue.hidden_dim * sizeof(*state->nnue.sum));
    state->depth = 0;
    state->nnue.valid = true;
    return true;
}

static bool nnue_state_score_batch_callback(const void *const *opaque_states,
                                            size_t count, int *scores) {
    const ShogiNnueState *states[6];
    if (opaque_states == NULL || scores == NULL || count == 0 || count > 12U)
        return false;
    for (size_t base = 0; base < count; base += 6U) {
        size_t tile = count - base;
        if (tile > 6U) tile = 6U;
        for (size_t index = 0; index < tile; ++index) {
            const NnueEvaluatorState *state = opaque_states[base + index];
            if (state == NULL) return false;
            states[index] = &state->nnue;
        }
        if (!shogi_nnue_state_evaluate_batch(states, tile, scores + base))
            return false;
    }
    return true;
}

static bool set_nnue_evaluator(ShogiEvaluator *evaluator,
                               ShogiNnueModel *model) {
    return shogi_evaluator_set(evaluator, model, nnue_evaluator_callback,
                               NULL, "tinyshogi-nnue") &&
           shogi_evaluator_set_state_callbacks(
               evaluator, nnue_state_create_callback, nnue_state_destroy_callback,
               nnue_state_make_callback, nnue_state_unmake_callback,
               nnue_state_score_callback) &&
           shogi_evaluator_set_state_batch_callback(
               evaluator, nnue_state_score_batch_callback, 6U) &&
           shogi_evaluator_set_state_rewind_callback(
               evaluator, nnue_state_rewind_callback);
}

typedef struct {
    ShogiNnueModel *model;
    const char *path;
    unsigned pin_index;
    bool loaded;
} NnueLoadTask;

static void *load_nnue_replica(void *opaque) {
    NnueLoadTask *task = opaque;
    (void)ts_thread_pin_allowed(task->pin_index);
    task->loaded = shogi_nnue_model_load(task->model, task->path);
    return NULL;
}

static void destroy_nnue_replicas(Application *application) {
    for (unsigned index = 0; index < 4U; ++index) {
        shogi_evaluator_destroy(&application->nnue_evaluators[index]);
        shogi_nnue_model_destroy(&application->nnue_replicas[index]);
    }
    application->nnue_replica_count = 0;
    application->options.evaluator_replicas = NULL;
    application->options.evaluator_replica_count = 0;
}

static bool load_nnue_replicas(Application *application, const char *path) {
    unsigned count = 1U;
#if defined(TINYSHOGI_A64FX_NUMA)
    if (application->options.a64fx_uct && application->options.threads >= 32U &&
        ts_thread_allowed_count() >= 32U) count = 4U;
#endif
    ShogiNnueModel models[4];
    NnueLoadTask tasks[4];
    TsThread threads[4] = {0};
    for (unsigned index = 0; index < count; ++index) {
        shogi_nnue_model_init(&models[index]);
        tasks[index] = (NnueLoadTask){&models[index], path, index, false};
        if (ts_thread_create(&threads[index], load_nnue_replica, &tasks[index]) != 0) {
            for (unsigned joined = 0; joined < index; ++joined) (void)ts_thread_join(&threads[joined]);
            for (unsigned clean = 0; clean <= index; ++clean) shogi_nnue_model_destroy(&models[clean]);
            return false;
        }
    }
    bool loaded = true;
    for (unsigned index = 0; index < count; ++index) {
        (void)ts_thread_join(&threads[index]);
        if (!tasks[index].loaded) loaded = false;
    }
    if (!loaded) {
        for (unsigned index = 0; index < count; ++index) shogi_nnue_model_destroy(&models[index]);
        return false;
    }
    destroy_nnue_replicas(application);
    shogi_evaluator_destroy(&application->evaluator);
    for (unsigned index = 0; index < count; ++index) {
        application->nnue_replicas[index] = models[index];
        if (!set_nnue_evaluator(&application->nnue_evaluators[index],
                                &application->nnue_replicas[index])) return false;
    }
    application->nnue_replica_count = count;
    application->options.evaluator = &application->nnue_evaluators[0];
    application->options.evaluator_replicas = application->nnue_evaluators;
    application->options.evaluator_replica_count = count;
    return true;
}

static uint64_t monotonic_ns_main(void) {
    struct timespec time;
    clock_gettime(CLOCK_MONOTONIC, &time);
    return (uint64_t)time.tv_sec * UINT64_C(1000000000) + (uint64_t)time.tv_nsec;
}

static unsigned detected_threads(void) {
    unsigned count = ts_thread_allowed_count();
    if (count > 8) count = 8;
    return count;
}

static void print_bestmove(const SearchResult *result) {
    if (result->declaration_win) {
        puts("bestmove win");
    } else if (result->resign || !result->has_move) {
        puts("bestmove resign");
    } else {
        char text[16];
        if (shogi_move_to_usi(result->move, text, sizeof(text))) printf("bestmove %s\n", text);
        else puts("bestmove resign");
    }
    fflush(stdout);
}

static void print_search_info(const Application *application) {
    SearchProgress progress;
    if (application->job == NULL || !search_get_progress(application->job, &progress)) return;
    SearchLine lines[SEARCH_MAX_MULTIPV];
    size_t line_count = search_get_root_lines(application->job, lines, application->options.multi_pv);
    if (line_count == 0) {
        printf("info depth %d nodes %llu nps %llu time %llu multipv 1 score cp %d",
               progress.depth,
               (unsigned long long)progress.nodes,
               (unsigned long long)progress.nps,
               (unsigned long long)progress.time_ms,
               progress.score_cp);
        if (progress.has_move) {
            char move[16];
            if (shogi_move_to_usi(progress.move, move, sizeof(move))) printf(" pv %s", move);
        }
        putchar('\n');
        fflush(stdout);
        return;
    }
    for (size_t index = 0; index < line_count; ++index) {
        int score = lines[index].score_cp;
        printf("info depth %d nodes %llu nps %llu time %llu multipv %zu score cp %d",
               progress.depth,
               (unsigned long long)progress.nodes,
               (unsigned long long)progress.nps,
               (unsigned long long)progress.time_ms,
               index + 1,
               score);
        fputs(" pv", stdout);
        size_t pv_length = lines[index].pv_length;
        if (pv_length == 0) pv_length = 1;
        for (size_t pv_index = 0; pv_index < pv_length; ++pv_index) {
            ShogiMove move_value = pv_length == lines[index].pv_length ?
                lines[index].pv[pv_index] : lines[index].move;
            char move[16];
            if (shogi_move_to_usi(move_value, move, sizeof(move))) printf(" %s", move);
        }
        putchar('\n');
    }
    fflush(stdout);
}

static void finish_job(Application *application, bool emit_bestmove) {
    if (application->job == NULL) return;
    if (!search_is_done(application->job)) search_request_stop(application->job);
    SearchResult result;
    search_join(application->job, &result);
    if (emit_bestmove) {
        print_search_info(application);
        print_bestmove(&result);
    }
    search_destroy(application->job);
    application->job = NULL;
}

static bool parse_unsigned(const char *text, uint64_t *value) {
    if (text == NULL || *text == '\0' || text[0] == '-') return false;
    char *end = NULL;
    errno = 0;
    unsigned long long parsed = strtoull(text, &end, 10);
    if (errno != 0 || *end != '\0') return false;
    *value = (uint64_t)parsed;
    return true;
}

static bool parse_int(const char *text, int *value) {
    uint64_t parsed;
    if (!parse_unsigned(text, &parsed) || parsed > (uint64_t)INT32_MAX) return false;
    *value = (int)parsed;
    return true;
}

static size_t tokenize(char *line, char **tokens, size_t capacity) {
    size_t count = 0;
    char *save = NULL;
    char *token = strtok_r(line, " \t\r\n", &save);
    while (token != NULL && count < capacity) {
        tokens[count++] = token;
        token = strtok_r(NULL, " \t\r\n", &save);
    }
    return count;
}

static bool set_position_command(Application *application, char *line) {
    char *tokens[1024];
    size_t count = tokenize(line, tokens, sizeof(tokens) / sizeof(tokens[0]));
    if (count < 2 || strcmp(tokens[0], "position") != 0) return false;
    ShogiPosition next;
    size_t move_start = 0;
    if (strcmp(tokens[1], "startpos") == 0) {
        shogi_position_start(&next);
        move_start = 2;
    } else if (strcmp(tokens[1], "sfen") == 0 && count >= 6) {
        char sfen[512];
        int written = snprintf(sfen, sizeof(sfen), "%s %s %s %s", tokens[2], tokens[3], tokens[4], tokens[5]);
        if (written < 0 || (size_t)written >= sizeof(sfen) || !shogi_position_from_sfen(&next, sfen)) return false;
        move_start = 6;
    } else {
        return false;
    }
    if (move_start < count && strcmp(tokens[move_start], "moves") != 0) return false;
    if (move_start < count) ++move_start;
    for (size_t index = move_start; index < count; ++index) {
        if (!shogi_parse_and_make_move(&next, tokens[index])) return false;
    }
    application->position = next;
    return true;
}

static bool is_go_keyword(const char *token) {
    static const char *const keywords[] = {
        "searchmoves", "nodes", "depth", "movetime", "btime", "wtime",
        "byoyomi", "binc", "winc", "infinite", "ponder"
    };
    for (size_t index = 0; index < sizeof(keywords) / sizeof(keywords[0]); ++index) {
        if (strcmp(token, keywords[index]) == 0) return true;
    }
    return false;
}

static bool parse_go(char *line, SearchLimits *limits) {
    char *tokens[128];
    size_t count = tokenize(line, tokens, sizeof(tokens) / sizeof(tokens[0]));
    if (count < 1 || strcmp(tokens[0], "go") != 0) return false;
    memset(limits, 0, sizeof(*limits));
    for (size_t index = 1; index < count; ++index) {
        if (strcmp(tokens[index], "infinite") == 0) {
            limits->infinite = true;
            continue;
        }
        if (strcmp(tokens[index], "ponder") == 0) {
            limits->ponder = true;
            continue;
        }
        if (strcmp(tokens[index], "searchmoves") == 0) {
            limits->has_searchmoves = true;
            ++index;
            while (index < count && !is_go_keyword(tokens[index])) {
                if (limits->searchmove_count >= SHOGI_MAX_MOVES ||
                    !shogi_parse_usi_move(tokens[index], &limits->searchmoves[limits->searchmove_count])) {
                    return false;
                }
                ++limits->searchmove_count;
                ++index;
            }
            --index;
            continue;
        }
        int value;
        uint64_t nodes;
        if (index + 1 >= count) return false;
        const char *key = tokens[index];
        const char *argument = tokens[++index];
        if (strcmp(key, "nodes") == 0) {
            if (!parse_unsigned(argument, &nodes)) return false;
            limits->nodes = nodes;
        } else if (strcmp(key, "depth") == 0) {
            if (!parse_int(argument, &value)) return false;
            limits->depth = value;
        } else if (strcmp(key, "movetime") == 0) {
            if (!parse_int(argument, &value)) return false;
            limits->movetime_ms = value;
        } else if (strcmp(key, "btime") == 0) {
            if (!parse_int(argument, &value)) return false;
            limits->btime_ms = value;
        } else if (strcmp(key, "wtime") == 0) {
            if (!parse_int(argument, &value)) return false;
            limits->wtime_ms = value;
        } else if (strcmp(key, "byoyomi") == 0) {
            if (!parse_int(argument, &value)) return false;
            limits->byoyomi_ms = value;
        } else if (strcmp(key, "binc") == 0) {
            if (!parse_int(argument, &value)) return false;
            limits->binc_ms = value;
        } else if (strcmp(key, "winc") == 0) {
            if (!parse_int(argument, &value)) return false;
            limits->winc_ms = value;
        }
    }
    return true;
}

static void print_usi(void) {
    printf("id name tinyshogi-c11-mcts\n");
    printf("id author tinyshogi\n");
    printf("option name Threads type spin default %u min 1 max 64\n", detected_threads());
    printf("option name Seed type spin default 0 min 0 max 2147483647\n");
    printf("option name MaxTreeNodes type spin default 1000000 min 1000 max 10000000\n");
    printf("option name RolloutDepth type spin default %u min 1 max 512\n", SEARCH_DEFAULT_ROLLOUT_DEPTH);
    printf("option name QuiescenceDepth type spin default %u min 0 max 8\n", SEARCH_DEFAULT_QUIESCENCE_DEPTH);
    printf("option name UCTExploration type spin default %u min 1 max 3000\n", SEARCH_DEFAULT_EXPLORATION_MILLI);
    printf("option name AspirationWindow type spin default %u min 16 max 2000\n", SEARCH_DEFAULT_ASPIRATION_WINDOW);
    printf("option name QuiescenceMargin type spin default %u min 0 max 1000\n", SEARCH_DEFAULT_QUIESCENCE_MARGIN);
    printf("option name MultiPV type spin default %u min 1 max %u\n", SEARCH_DEFAULT_MULTIPV, SEARCH_MAX_MULTIPV);
    puts("option name SearchMode type combo default mcts var mcts var alphabeta");
    puts("option name MCTSMode type combo default auto var auto var neural var rollout");
    puts("option name LeafBatch type spin default 5 min 1 max 12");
    puts("option name A64FXMode type combo default auto var auto var off");
    puts("option name EvalPlugin type string default none");
    puts("option name EvalModel type string default none");
    puts("usiok");
    fflush(stdout);
}

static void set_option(Application *application, char *line) {
    char *tokens[32];
    size_t count = tokenize(line, tokens, sizeof(tokens) / sizeof(tokens[0]));
    if (count < 4 || strcmp(tokens[0], "setoption") != 0 || strcmp(tokens[1], "name") != 0) return;
    size_t value_index = 0;
    for (size_t index = 2; index < count; ++index) {
        if (strcmp(tokens[index], "value") == 0) {
            value_index = index + 1;
            break;
        }
    }
    if (value_index >= count) return;
    uint64_t value;
    if (strcmp(tokens[2], "Threads") == 0 && parse_unsigned(tokens[value_index], &value)) {
        if (value >= 1 && value <= 64) application->options.threads = (unsigned)value;
    } else if (strcmp(tokens[2], "Seed") == 0 && parse_unsigned(tokens[value_index], &value)) {
        if (value <= UINT32_MAX) {
            application->options.seed = value;
            application->options.seed_auto = value == 0;
        }
    } else if (strcmp(tokens[2], "MaxTreeNodes") == 0 && parse_unsigned(tokens[value_index], &value)) {
        if (value >= 1000 && value <= 10000000) application->options.max_tree_nodes = (size_t)value;
    } else if (strcmp(tokens[2], "RolloutDepth") == 0 && parse_unsigned(tokens[value_index], &value)) {
        if (value >= 1 && value <= 512) application->options.rollout_depth = (unsigned)value;
    } else if (strcmp(tokens[2], "QuiescenceDepth") == 0 && parse_unsigned(tokens[value_index], &value)) {
        if (value <= 8) application->options.quiescence_depth = (unsigned)value;
    } else if (strcmp(tokens[2], "UCTExploration") == 0 && parse_unsigned(tokens[value_index], &value)) {
        if (value >= 1 && value <= 3000) application->options.exploration_milli = (unsigned)value;
    } else if (strcmp(tokens[2], "AspirationWindow") == 0 && parse_unsigned(tokens[value_index], &value)) {
        if (value >= 16 && value <= 2000) application->options.aspiration_window = (unsigned)value;
    } else if (strcmp(tokens[2], "QuiescenceMargin") == 0 && parse_unsigned(tokens[value_index], &value)) {
        if (value <= 1000) application->options.quiescence_margin = (unsigned)value;
    } else if (strcmp(tokens[2], "MultiPV") == 0 && parse_unsigned(tokens[value_index], &value)) {
        if (value >= 1 && value <= SEARCH_MAX_MULTIPV) application->options.multi_pv = (unsigned)value;
    } else if (strcmp(tokens[2], "SearchMode") == 0) {
        if (strcmp(tokens[value_index], "alphabeta") == 0)
            application->options.mode = SEARCH_MODE_ALPHABETA;
        else if (strcmp(tokens[value_index], "mcts") == 0)
            application->options.mode = SEARCH_MODE_MCTS;
    } else if (strcmp(tokens[2], "MCTSMode") == 0) {
        if (strcmp(tokens[value_index], "auto") == 0)
            application->options.mcts_policy = SEARCH_MCTS_AUTO;
        else if (strcmp(tokens[value_index], "neural") == 0)
            application->options.mcts_policy = SEARCH_MCTS_NEURAL;
        else if (strcmp(tokens[value_index], "rollout") == 0)
            application->options.mcts_policy = SEARCH_MCTS_ROLLOUT;
    } else if (strcmp(tokens[2], "LeafBatch") == 0 && parse_unsigned(tokens[value_index], &value)) {
        if (value >= 1 && value <= 12) application->options.leaf_batch_size = (unsigned)value;
    } else if (strcmp(tokens[2], "A64FXMode") == 0) {
        bool enabled = strcmp(tokens[value_index], "auto") == 0;
        if (enabled || strcmp(tokens[value_index], "off") == 0) {
            application->options.a64fx_uct = enabled;
            if (application->nnue_replica_count != 0) {
                application->options.evaluator_replicas = application->nnue_evaluators;
                application->options.evaluator_replica_count = enabled ?
                    application->nnue_replica_count : 1U;
            }
        }
    } else if (strcmp(tokens[2], "EvalPlugin") == 0) {
        if (strcmp(tokens[value_index], "none") == 0) {
            destroy_nnue_replicas(application);
            shogi_evaluator_destroy(&application->evaluator);
            application->options.evaluator = &application->evaluator;
        } else {
            ShogiEvaluator next;
            shogi_evaluator_init(&next);
            if (shogi_evaluator_load(&next, tokens[value_index], NULL)) {
                destroy_nnue_replicas(application);
                shogi_evaluator_destroy(&application->evaluator);
                application->evaluator = next;
                application->options.evaluator = &application->evaluator;
                printf("info string evaluator loaded %s\n",
                       application->evaluator.name == NULL ? tokens[value_index] : application->evaluator.name);
            } else {
                printf("info string evaluator load failed: %s\n", shogi_evaluator_error());
            }
        }
        fflush(stdout);
    } else if (strcmp(tokens[2], "EvalModel") == 0) {
        if (strcmp(tokens[value_index], "none") == 0) {
            destroy_nnue_replicas(application);
            shogi_evaluator_destroy(&application->evaluator);
            application->options.evaluator = &application->evaluator;
        } else {
            if (load_nnue_replicas(application, tokens[value_index])) {
                printf("info string NNUE model loaded %s replicas %u\n",
                       tokens[value_index], application->nnue_replica_count);
            } else {
                puts("info string NNUE model load failed");
            }
        }
        fflush(stdout);
    }
}

static bool selftest(void) {
    ShogiPosition position;
    shogi_position_start(&position);
    ShogiMove moves[SHOGI_MAX_MOVES];
    size_t count = shogi_generate_legal(&position, moves, SHOGI_MAX_MOVES);
    if (count == 30) {
        if (!shogi_parse_and_make_move(&position, "7g7f")) return false;
        char sfen[512];
        if (!shogi_position_to_sfen(&position, sfen, sizeof(sfen))) return false;
        return strcmp(sfen, "lnsgkgsnl/1r5b1/ppppppppp/9/9/2P6/PP1PPPPPP/1B5R1/LNSGKGSNL w - 2") == 0;
    }
    return false;
}

typedef struct {
    char sfen[512];
    ShogiNdfRecord record;
    ShogiColor side;
    ShogiMove selected;
    SearchPolicyEntry policy[SHOGI_MAX_MOVES];
    size_t policy_count;
} SelfplaySample;

static uint64_t selfplay_rng(uint64_t *state) {
    uint64_t value = (*state += UINT64_C(0x9e3779b97f4a7c15));
    value = (value ^ (value >> 30)) * UINT64_C(0xbf58476d1ce4e5b9);
    value = (value ^ (value >> 27)) * UINT64_C(0x94d049bb133111eb);
    return value ^ (value >> 31);
}

static bool selfplay_option(const char *key, const char *value, uint64_t *out) {
    if (key == NULL || value == NULL || out == NULL) return false;
    if (value[0] == '-' || value[0] == '\0') return false;
    char *end = NULL;
    unsigned long long parsed = strtoull(value, &end, 10);
    if (*end != '\0') return false;
    (void)key;
    *out = (uint64_t)parsed;
    return true;
}

static size_t selfplay_choose(const SearchPolicyEntry *policy, size_t count,
                              unsigned temperature_milli, unsigned ply, unsigned cutoff,
                              uint64_t *rng) {
    if (count == 0) return 0;
    if (ply >= cutoff || temperature_milli == 0) {
        size_t best = 0;
        for (size_t index = 1; index < count; ++index) {
            if (policy[index].visits > policy[best].visits) best = index;
        }
        return best;
    }
    double temperature = (double)temperature_milli / 1000.0;
    double total = 0.0;
    for (size_t index = 0; index < count; ++index) {
        double weight = pow((double)policy[index].visits, 1.0 / temperature);
        if (!isfinite(weight)) weight = policy[index].visits == 0 ? 0.0 : 1.0e300;
        total += weight;
    }
    if (total <= 0.0 || !isfinite(total)) return (size_t)(selfplay_rng(rng) % count);
    double selected = ((double)(selfplay_rng(rng) >> 11) / 9007199254740992.0) * total;
    for (size_t index = 0; index < count; ++index) {
        double weight = pow((double)policy[index].visits, 1.0 / temperature);
        if (selected < weight) return index;
        selected -= weight;
    }
    return count - 1;
}

static int selfplay_result_value(ShogiResult result, ShogiColor side) {
    if (result == SHOGI_RESULT_DRAW || result == SHOGI_RESULT_ONGOING) return 0;
    ShogiResult win = side == SHOGI_BLACK ? SHOGI_RESULT_BLACK_WIN : SHOGI_RESULT_WHITE_WIN;
    return result == win ? 1 : -1;
}

static bool run_selfplay(int argc, char **argv) {
    unsigned games = 1, simulations = 256, max_plies = 512;
    unsigned threads = 1, temperature_milli = 1000, cutoff = 30, leaf_batch = 5;
    uint64_t seed = 1, game_offset = 0;
    const char *output_path = "selfplay.jsonl";
    const char *output_format = "jsonl";
    const char *eval_model_path = NULL;
    for (int index = 2; index < argc; ++index) {
        uint64_t value;
        const char *key = argv[index];
        if (index + 1 >= argc) return false;
        if (strcmp(key, "--output") == 0) {
            output_path = argv[++index];
            continue;
        }
        if (strcmp(key, "--eval-model") == 0) {
            eval_model_path = argv[++index];
            continue;
        }
        if (strcmp(key, "--output-format") == 0) {
            output_format = argv[++index];
            continue;
        }
        if (!selfplay_option(key, argv[index + 1], &value)) return false;
        if (strcmp(key, "--games") == 0) games = (unsigned)value;
        else if (strcmp(key, "--simulations") == 0) simulations = (unsigned)value;
        else if (strcmp(key, "--threads") == 0) threads = (unsigned)value;
        else if (strcmp(key, "--seed") == 0) seed = value;
        else if (strcmp(key, "--temperature") == 0) temperature_milli = (unsigned)value;
        else if (strcmp(key, "--temperature-cutoff") == 0) cutoff = (unsigned)value;
        else if (strcmp(key, "--max-plies") == 0) max_plies = (unsigned)value;
        else if (strcmp(key, "--leaf-batch") == 0) leaf_batch = (unsigned)value;
        else if (strcmp(key, "--game-offset") == 0) game_offset = value;
        else return false;
        ++index;
    }
    if (games == 0 || simulations == 0 || max_plies == 0 || threads == 0 ||
        leaf_batch == 0 || leaf_batch > 12U) return false;
    bool ndf_output = strcmp(output_format, "ndf1") == 0;
    if (!ndf_output && strcmp(output_format, "jsonl") != 0) return false;
    ShogiNnueModel eval_model;
    ShogiEvaluator evaluator;
    shogi_nnue_model_init(&eval_model);
    shogi_evaluator_init(&evaluator);
    if (eval_model_path != NULL) {
        if (!shogi_nnue_model_load(&eval_model, eval_model_path) ||
            !set_nnue_evaluator(&evaluator, &eval_model)) {
            shogi_nnue_model_destroy(&eval_model);
            shogi_evaluator_destroy(&evaluator);
            return false;
        }
    }
    char *partial_path = NULL;
    const char *open_path = output_path;
    if (ndf_output) {
        size_t length = strlen(output_path);
        partial_path = malloc(length + 9U);
        if (partial_path == NULL) {
            shogi_evaluator_destroy(&evaluator); shogi_nnue_model_destroy(&eval_model);
            return false;
        }
        snprintf(partial_path, length + 9U, "%s.partial", output_path);
        open_path = partial_path;
    }
    FILE *output = fopen(open_path, ndf_output ? "wb+" : "w");
    if (output == NULL) {
        free(partial_path);
        shogi_evaluator_destroy(&evaluator); shogi_nnue_model_destroy(&eval_model); return false;
    }
    SelfplaySample *samples = NULL;
    if (ndf_output && !shogi_ndf_write_header(output, 0)) goto selfplay_fail;
    samples = calloc(max_plies, sizeof(*samples));
    if (samples == NULL) goto selfplay_fail;
    for (unsigned game = 0; game < games; ++game) {
        ShogiPosition position;
        shogi_position_start(&position);
        size_t sample_count = 0;
        ShogiResult result = SHOGI_RESULT_ONGOING;
        uint64_t game_id = game_offset + game;
        uint64_t rng = seed + game_id * UINT64_C(0x9e3779b97f4a7c15);
        for (unsigned ply = 0; ply < max_plies && result == SHOGI_RESULT_ONGOING; ++ply) {
            if (!shogi_position_to_sfen(&position, samples[sample_count].sfen,
                                        sizeof(samples[sample_count].sfen))) goto selfplay_fail;
            samples[sample_count].side = position.side;
            shogi_ndf_record_from_position(&samples[sample_count].record,
                                           &position, 0, 0);
            SearchOptions options = {
                .mode = SEARCH_MODE_MCTS,
                .threads = threads,
                .seed = seed + ply + game_id * 1000003U,
                .seed_auto = false,
                .max_tree_nodes = 200000,
                .rollout_depth = 64,
                .quiescence_depth = SEARCH_DEFAULT_QUIESCENCE_DEPTH,
                .exploration_milli = SEARCH_DEFAULT_EXPLORATION_MILLI,
                .multi_pv = 1,
                .evaluator = &evaluator,
                .mcts_policy = SEARCH_MCTS_AUTO,
                .leaf_batch_size = leaf_batch,
#if defined(TINYSHOGI_A64FX_NUMA)
                .a64fx_uct = true,
#endif
            };
            SearchLimits limits = {0};
            limits.nodes = simulations;
            SearchJob *job = search_start(&position, &limits, &options);
            if (job == NULL) goto selfplay_fail;
            search_join(job, NULL);
            samples[sample_count].policy_count = search_get_root_policy(
                job, samples[sample_count].policy, SHOGI_MAX_MOVES);
            if (samples[sample_count].policy_count == 0) { search_destroy(job); break; }
            size_t choice = selfplay_choose(samples[sample_count].policy,
                                             samples[sample_count].policy_count,
                                             temperature_milli, ply, cutoff, &rng);
            samples[sample_count].selected = samples[sample_count].policy[choice].move;
            ++sample_count;
            search_destroy(job);
            if (!shogi_make_move(&position, samples[sample_count - 1].selected)) break;
            result = shogi_game_result(&position);
        }
        if (result == SHOGI_RESULT_ONGOING) result = SHOGI_RESULT_DRAW;
        for (size_t sample = 0; sample < sample_count; ++sample) {
            int value = selfplay_result_value(result, samples[sample].side);
            if (ndf_output) {
                samples[sample].record.value = (int16_t)(value * 1000);
                if (fwrite(&samples[sample].record, sizeof(samples[sample].record),
                           1, output) != 1) goto selfplay_fail;
                continue;
            }
            char selected[16];
            if (!shogi_move_to_usi(samples[sample].selected, selected, sizeof(selected))) continue;
            fprintf(output, "{\"version\":1,\"game\":%llu,\"ply\":%zu,\"sfen\":\"%s\",\"move\":\"%s\",\"value\":%d,\"policy\":[",
                    (unsigned long long)game_id, sample, samples[sample].sfen,
                    selected, value);
            for (size_t entry = 0; entry < samples[sample].policy_count; ++entry) {
                char move[16];
                if (entry != 0) fputc(',', output);
                if (!shogi_move_to_usi(samples[sample].policy[entry].move, move, sizeof(move))) continue;
                fprintf(output, "[\"%s\",%llu]", move,
                        (unsigned long long)samples[sample].policy[entry].visits);
            }
            fprintf(output, "]}\n");
        }
        fprintf(stderr, "selfplay game %u/%u result %d plies %zu\n", game + 1, games,
                result, sample_count);
    }
    if (ndf_output) {
        long end = ftell(output);
        uint64_t count = end < 16 ? 0U : ((uint64_t)end - 16U) / sizeof(ShogiNdfRecord);
        bool finalized = count <= UINT32_MAX && fseek(output, 0, SEEK_SET) == 0 &&
            shogi_ndf_write_header(output, (uint32_t)count) && fflush(output) == 0 &&
            fsync(fileno(output)) == 0;
        if (fclose(output) != 0) finalized = false;
        output = NULL;
        if (!finalized || rename(partial_path, output_path) != 0) goto selfplay_fail;
    } else if (fclose(output) != 0) {
        output = NULL;
        goto selfplay_fail;
    } else output = NULL;
    free(samples);
    free(partial_path);
    shogi_evaluator_destroy(&evaluator);
    shogi_nnue_model_destroy(&eval_model);
    return true;

selfplay_fail:
    free(samples);
    if (output != NULL) fclose(output);
    if (partial_path != NULL) remove(partial_path);
    free(partial_path);
    shogi_evaluator_destroy(&evaluator);
    shogi_nnue_model_destroy(&eval_model);
    return false;
}

static void process_line(Application *application, char *line) {
    char command[32] = {0};
    if (sscanf(line, "%31s", command) != 1) return;
    if (strcmp(command, "quit") == 0) {
        finish_job(application, false);
        application->quit = true;
    } else if (strcmp(command, "stop") == 0) {
        finish_job(application, true);
    } else if (strcmp(command, "ponderhit") == 0) {
        (void)search_ponderhit(application->job);
    } else if (strcmp(command, "go") == 0) {
        finish_job(application, false);
        SearchLimits limits;
        if (!parse_go(line, &limits)) {
            puts("bestmove resign");
            fflush(stdout);
            return;
        }
        application->job = search_start(&application->position, &limits, &application->options);
        application->last_info_ns = monotonic_ns_main();
        if (application->job == NULL) {
            puts("bestmove resign");
            fflush(stdout);
        }
    } else if (strcmp(command, "usi") == 0) {
        finish_job(application, false);
        print_usi();
    } else if (strcmp(command, "isready") == 0) {
        finish_job(application, false);
        puts("readyok");
        fflush(stdout);
    } else if (strcmp(command, "setoption") == 0) {
        finish_job(application, false);
        set_option(application, line);
    } else if (strcmp(command, "usinewgame") == 0) {
        finish_job(application, false);
        shogi_position_start(&application->position);
    } else if (strcmp(command, "position") == 0) {
        finish_job(application, false);
        (void)set_position_command(application, line);
    } else if (strcmp(command, "d") == 0) {
        finish_job(application, false);
        shogi_print_position(&application->position);
        fflush(stdout);
    } else if (strcmp(command, "sfen") == 0) {
        char sfen[512];
        finish_job(application, false);
        if (shogi_position_to_sfen(&application->position, sfen, sizeof(sfen))) puts(sfen);
        fflush(stdout);
    } else if (strcmp(command, "hash") == 0) {
        finish_job(application, false);
        printf("info string hash %llu\n", (unsigned long long)application->position.hash);
        fflush(stdout);
    } else if (strcmp(command, "eval") == 0) {
        finish_job(application, false);
        int score = shogi_evaluator_score(application->options.evaluator,
                                          &application->position,
                                          application->position.side);
        printf("info string eval cp %d\n", score);
        fflush(stdout);
    } else if (strcmp(command, "evalmoves") == 0) {
        finish_job(application, false);
        ShogiMove moves[SHOGI_MAX_MOVES];
        size_t count = shogi_generate_legal(&application->position, moves,
                                            SHOGI_MAX_MOVES);
        for (size_t index = 0; index < count; ++index) {
            ShogiPosition next = application->position;
            if (!shogi_make_move(&next, moves[index])) continue;
            int score = -shogi_evaluator_score(application->options.evaluator,
                                               &next, next.side);
            char move[16];
            if (shogi_move_to_usi(moves[index], move, sizeof(move)))
                printf("info string evalmove %s cp %d\n", move, score);
        }
        puts("info string evalmoves done");
        fflush(stdout);
    }
}

int main(int argc, char **argv) {
    shogi_init();
    if (argc > 1 && strcmp(argv[1], "--selftest") == 0) return selftest() ? 0 : 1;
    if (argc > 1 && strcmp(argv[1], "--selfplay") == 0) return run_selfplay(argc, argv) ? 0 : 1;

    Application application;
    memset(&application, 0, sizeof(application));
    shogi_evaluator_init(&application.evaluator);
    for (unsigned index = 0; index < 4U; ++index) {
        shogi_evaluator_init(&application.nnue_evaluators[index]);
        shogi_nnue_model_init(&application.nnue_replicas[index]);
    }
    shogi_position_start(&application.position);
    application.options.threads = detected_threads();
    application.options.mode = SEARCH_MODE_MCTS;
    application.options.seed_auto = true;
    application.options.max_tree_nodes = 1000000;
    application.options.rollout_depth = SEARCH_DEFAULT_ROLLOUT_DEPTH;
    application.options.quiescence_depth = SEARCH_DEFAULT_QUIESCENCE_DEPTH;
    application.options.quiescence_margin = SEARCH_DEFAULT_QUIESCENCE_MARGIN;
    application.options.exploration_milli = SEARCH_DEFAULT_EXPLORATION_MILLI;
    application.options.multi_pv = SEARCH_DEFAULT_MULTIPV;
    application.options.evaluator = &application.evaluator;
#if defined(TINYSHOGI_A64FX_NUMA)
    application.options.a64fx_uct = true;
#endif
    application.search_context = search_context_create();
    application.options.context = application.search_context;

    char line[4096];
    bool input_eof = false;
    while (!application.quit) {
        if (application.job == NULL) {
            if (input_eof || fgets(line, sizeof(line), stdin) == NULL) break;
            process_line(&application, line);
            continue;
        }

        if (search_is_done(application.job)) {
            finish_job(&application, true);
            continue;
        }
        struct pollfd descriptor = {STDIN_FILENO, POLLIN | POLLHUP, 0};
        int status = input_eof ? poll(NULL, 0, 20) : poll(&descriptor, 1, 20);
        if (status < 0 && errno == EINTR) continue;
        if (status < 0) {
            finish_job(&application, true);
            break;
        }
        if (status > 0 && (descriptor.revents & (POLLIN | POLLHUP)) != 0) {
            if (fgets(line, sizeof(line), stdin) != NULL) {
                process_line(&application, line);
            } else {
                input_eof = true;
                if (search_waits_for_stop(application.job)) finish_job(&application, true);
            }
        }
        if (application.job != NULL) {
            uint64_t now = monotonic_ns_main();
            if (now - application.last_info_ns >= UINT64_C(250000000)) {
                print_search_info(&application);
                application.last_info_ns = now;
            }
        }
    }
    finish_job(&application, false);
    search_context_destroy(application.search_context);
    destroy_nnue_replicas(&application);
    shogi_evaluator_destroy(&application.evaluator);
    return 0;
}
