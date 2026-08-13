#ifndef TINYSHOGI_SEARCH_H
#define TINYSHOGI_SEARCH_H

#include "shogi.h"
#include "eval.h"

#include <stdbool.h>
#include <stdint.h>

#define SEARCH_DEFAULT_ROLLOUT_DEPTH 256U
#define SEARCH_DEFAULT_QUIESCENCE_DEPTH 2U
#define SEARCH_DEFAULT_EXPLORATION_MILLI 1414U
#define SEARCH_DEFAULT_ASPIRATION_WINDOW 2000U
#define SEARCH_DEFAULT_QUIESCENCE_MARGIN 0U
#define SEARCH_DEFAULT_MULTIPV 1U
#define SEARCH_MAX_MULTIPV 8U
#define SEARCH_MAX_PV 64U

typedef enum {
    SEARCH_MODE_MCTS = 0,
    SEARCH_MODE_ALPHABETA = 1
} SearchMode;

typedef enum {
    SEARCH_MCTS_AUTO = 0,
    SEARCH_MCTS_ROLLOUT = 1,
    SEARCH_MCTS_NEURAL = 2
} SearchMctsPolicy;

typedef struct SearchContext SearchContext;

typedef struct {
    uint64_t nodes;
    int depth;
    int movetime_ms;
    int btime_ms;
    int wtime_ms;
    int byoyomi_ms;
    int binc_ms;
    int winc_ms;
    bool infinite;
    bool ponder;
    bool has_searchmoves;
    ShogiMove searchmoves[SHOGI_MAX_MOVES];
    size_t searchmove_count;
} SearchLimits;

typedef struct {
    SearchMode mode;
    unsigned threads;
    uint64_t seed;
    bool seed_auto;
    size_t max_tree_nodes;
    unsigned rollout_depth;
    unsigned quiescence_depth;
    unsigned exploration_milli;
    unsigned aspiration_window;
    unsigned quiescence_margin;
    unsigned multi_pv;
    const ShogiEvaluator *evaluator;
    const ShogiEvaluator *evaluator_replicas;
    unsigned evaluator_replica_count;
    SearchMctsPolicy mcts_policy;
    unsigned leaf_batch_size;
    bool a64fx_uct;
    SearchContext *context;
} SearchOptions;

typedef struct {
    bool has_move;
    bool declaration_win;
    bool resign;
    ShogiMove move;
    uint64_t simulations;
} SearchResult;

typedef struct {
    uint64_t nodes;
    uint64_t time_ms;
    uint64_t nps;
    int depth;
    int score_cp;
    bool has_move;
    ShogiMove move;
} SearchProgress;

typedef struct {
    ShogiMove move;
    uint64_t visits;
    int score_cp;
    size_t pv_length;
    ShogiMove pv[SEARCH_MAX_PV];
} SearchLine;

typedef struct {
    ShogiMove move;
    uint64_t visits;
} SearchPolicyEntry;

typedef struct SearchJob SearchJob;

/* Retains per-worker tree storage between sequential searches.  A context may
 * have only one active SearchJob at a time. */
SearchContext *search_context_create(void);
void search_context_destroy(SearchContext *context);

SearchJob *search_start(const ShogiPosition *position,
                        const SearchLimits *limits,
                        const SearchOptions *options);
bool search_is_done(const SearchJob *job);
bool search_is_infinite(const SearchJob *job);
bool search_is_pondering(const SearchJob *job);
bool search_waits_for_stop(const SearchJob *job);
bool search_ponderhit(SearchJob *job);
bool search_get_progress(const SearchJob *job, SearchProgress *progress);
size_t search_get_root_lines(const SearchJob *job, SearchLine *lines, size_t capacity);
size_t search_get_root_policy(const SearchJob *job, SearchPolicyEntry *entries, size_t capacity);
void search_request_stop(SearchJob *job);
void search_join(SearchJob *job, SearchResult *result);
void search_destroy(SearchJob *job);

#endif
