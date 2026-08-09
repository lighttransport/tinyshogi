#include "../src/search.h"

#include <stdio.h>
#include <string.h>

static int fail(const char *message) {
    fprintf(stderr, "search test failed: %s\n", message);
    return 1;
}

static SearchOptions test_options(void) {
    SearchOptions options;
    memset(&options, 0, sizeof(options));
    options.threads = 2;
    options.seed = 1;
    options.seed_auto = false;
    options.max_tree_nodes = 10000;
    options.rollout_depth = 64;
    options.quiescence_depth = SEARCH_DEFAULT_QUIESCENCE_DEPTH;
    options.exploration_milli = SEARCH_DEFAULT_EXPLORATION_MILLI;
    options.multi_pv = 2;
    return options;
}

int main(void) {
    shogi_init();
    ShogiPosition position;
    shogi_position_start(&position);
    SearchOptions options = test_options();
    SearchContext *context = search_context_create();
    if (context == NULL) return fail("persistent context creation");
    options.context = context;
    SearchLimits limits;
    memset(&limits, 0, sizeof(limits));
    limits.nodes = 16;

    SearchJob *job = search_start(&position, &limits, &options);
    if (job == NULL) return fail("node-limited search creation");
    SearchResult result;
    search_join(job, &result);
    if (!result.has_move || result.simulations == 0 || result.simulations > limits.nodes) return fail("node-limited search result");
    SearchProgress progress;
    if (!search_get_progress(job, &progress) || progress.nodes != result.simulations || !progress.has_move) {
        return fail("search progress snapshot");
    }
    SearchLine lines[2];
    if (search_get_root_lines(job, lines, 2) != 2) return fail("multipv root lines");
    SearchPolicyEntry policy[SHOGI_MAX_MOVES];
    size_t policy_count = search_get_root_policy(job, policy, SHOGI_MAX_MOVES);
    ShogiMove legal_moves[SHOGI_MAX_MOVES];
    size_t legal_count = shogi_generate_legal(&position, legal_moves, SHOGI_MAX_MOVES);
    if (policy_count != legal_count || policy_count == 0) return fail("root policy move count");
    uint64_t policy_visits = 0;
    for (size_t policy_index = 0; policy_index < policy_count; ++policy_index) {
        policy_visits += policy[policy_index].visits;
        ShogiPosition policy_position = position;
        if (!shogi_make_move(&policy_position, policy[policy_index].move)) return fail("root policy legality");
    }
    if (policy_visits > result.simulations) return fail("root policy visit total");
    if (lines[0].pv_length == 0 || lines[0].pv_length > SEARCH_MAX_PV ||
        lines[0].pv[0].from != lines[0].move.from || lines[0].pv[0].to != lines[0].move.to ||
        lines[0].pv[0].promote != lines[0].move.promote || lines[0].pv[0].drop != lines[0].move.drop) {
        return fail("principal variation root move");
    }
    ShogiPosition pv_position = position;
    for (size_t pv_index = 0; pv_index < lines[0].pv_length; ++pv_index) {
        if (!shogi_make_move(&pv_position, lines[0].pv[pv_index])) return fail("principal variation legality");
    }
    ShogiPosition next = position;
    if (!shogi_make_move(&next, result.move)) return fail("search returned illegal move");
    search_destroy(job);

    memset(&limits, 0, sizeof(limits));
    limits.nodes = 8;
    limits.has_searchmoves = true;
    if (!shogi_parse_usi_move("7g7f", &limits.searchmoves[0])) return fail("searchmoves parse");
    limits.searchmove_count = 1;
    job = search_start(&position, &limits, &options);
    if (job == NULL) return fail("searchmoves search creation");
    search_join(job, &result);
    char constrained[16];
    if (!result.has_move || !shogi_move_to_usi(result.move, constrained, sizeof(constrained)) ||
        strcmp(constrained, "7g7f") != 0) return fail("searchmoves constraint");
    search_destroy(job);

    SearchOptions deterministic = options;
    deterministic.threads = 1;
    limits.nodes = 32;
    job = search_start(&position, &limits, &deterministic);
    if (job == NULL) return fail("deterministic search creation");
    SearchResult first;
    search_join(job, &first);
    search_destroy(job);
    job = search_start(&position, &limits, &deterministic);
    if (job == NULL) return fail("second deterministic search creation");
    SearchResult second;
    search_join(job, &second);
    search_destroy(job);
    char first_move[16];
    char second_move[16];
    if (!first.has_move || !second.has_move ||
        !shogi_move_to_usi(first.move, first_move, sizeof(first_move)) ||
        !shogi_move_to_usi(second.move, second_move, sizeof(second_move)) ||
        strcmp(first_move, second_move) != 0) return fail("seeded deterministic search");

    memset(&limits, 0, sizeof(limits));
    limits.infinite = true;
    job = search_start(&position, &limits, &options);
    if (job == NULL) return fail("infinite search creation");
    search_request_stop(job);
    search_join(job, &result);
    if (!result.has_move) return fail("stopped search fallback");
    search_destroy(job);

    SearchOptions alphabeta = options;
    alphabeta.mode = SEARCH_MODE_ALPHABETA;
    limits.infinite = false;
    limits.nodes = 200;
    limits.depth = 2;
    job = search_start(&position, &limits, &alphabeta);
    if (job == NULL) return fail("alpha-beta search creation");
    search_join(job, &result);
    if (!result.has_move || result.simulations == 0) return fail("alpha-beta search result");
    ShogiPosition alpha_next = position;
    if (!shogi_make_move(&alpha_next, result.move)) return fail("alpha-beta legal move");
    search_destroy(job);

    memset(&limits, 0, sizeof(limits));
    limits.ponder = true;
    limits.movetime_ms = 20;
    job = search_start(&position, &limits, &options);
    if (job == NULL || !search_is_pondering(job) || !search_waits_for_stop(job)) {
        if (job != NULL) search_destroy(job);
        return fail("ponder search creation");
    }
    if (!search_ponderhit(job) || search_is_pondering(job) || search_waits_for_stop(job)) {
        search_destroy(job);
        return fail("ponderhit transition");
    }
    search_join(job, &result);
    if (!result.has_move || result.simulations == 0) {
        search_destroy(job);
        return fail("ponder search result");
    }
    search_destroy(job);
    search_context_destroy(context);
    return 0;
}
