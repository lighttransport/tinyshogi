#include "../src/search.h"

#include <stdio.h>
#include <string.h>
#include <limits.h>

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
    options.perpetual_check = true;
    options.ab_null_move = true;
    return options;
}

static int constant_eval(void *unused, const ShogiPosition *position, ShogiColor side) {
    (void)unused;
    (void)position;
    return side == SHOGI_BLACK ? 500 : -500;
}

static int null_probe_eval(void *data, const ShogiPosition *position, ShogiColor side) {
    unsigned *observed = data;
    if (position->history_length != 0 &&
        position->history[position->history_length - 1] != position->hash) ++*observed;
    return side == SHOGI_BLACK ? 500 : -500;
}

static int root_update_eval(void *data, const ShogiPosition *position, ShogiColor side) {
    ShogiMove *moves = data;
    int score = -200;
    if (position->board[moves[0].to] != SHOGI_EMPTY)
        score = position->move_number <= 2 ? 100 : -100;
    else if (position->board[moves[1].to] != SHOGI_EMPTY)
        score = 0;
    return side == SHOGI_BLACK ? score : -score;
}

static int check_exchange(const char *sfen, const char *text, int expected) {
    ShogiPosition position, saved;
    ShogiMove move;
    if (!shogi_position_from_sfen(&position, sfen) || !shogi_parse_usi_move(text, &move))
        return fail("exchange fixture");
    saved = position;
    int actual = search_static_exchange(&position, move);
    if (actual != expected || memcmp(&position, &saved, sizeof(position)) != 0) {
        fprintf(stderr, "exchange %s expected %d got %d\n", text, expected, actual);
        return fail("exchange value / unchanged position");
    }
    return 0;
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
    SearchLine alpha_line;
    if (search_get_root_lines(job, &alpha_line, 1) != 1 ||
        alpha_line.move.from != result.move.from ||
        alpha_line.move.to != result.move.to ||
        alpha_line.move.promote != result.move.promote ||
        alpha_line.move.drop != result.move.drop) {
        return fail("alpha-beta best move reporting");
    }
    ShogiPosition alpha_next = position;
    if (!shogi_make_move(&alpha_next, result.move)) return fail("alpha-beta legal move");
    search_destroy(job);

    ShogiPosition tactical;
    if (!shogi_position_from_sfen(&tactical,
            "4k4/9/9/4r4/4R4/9/9/9/4K4 b - 1")) {
        return fail("alpha-beta tactical SFEN");
    }
    ShogiMove winning_capture;
    if (!shogi_parse_usi_move("5e5d", &winning_capture))
        return fail("alpha-beta tactical move parse");
    memset(&limits, 0, sizeof(limits));
    limits.depth = 1;
    job = search_start(&tactical, &limits, &alphabeta);
    if (job == NULL) return fail("alpha-beta tactical search creation");
    search_join(job, &result);
    if (!result.has_move || result.move.from != winning_capture.from ||
        result.move.to != winning_capture.to ||
        result.move.promote != winning_capture.promote ||
        result.move.drop != winning_capture.drop) {
        search_destroy(job);
        return fail("alpha-beta tactical best move");
    }
    search_destroy(job);

    if (check_exchange("4k4/9/9/4p4/4R4/9/9/9/4K4 b - 1", "5e5d", 200) ||
        check_exchange("4k4/9/4p4/4p4/4R4/9/9/9/4K4 b - 1", "5e5d", -1800) ||
        check_exchange("4k4/9/9/4+p4/4R4/9/9/9/4K4 b - 1", "5e5d", 650) ||
        check_exchange("4k4/4s4/5p3/6B2/9/9/9/4R4/K8 b - 1", "3d4c", 200) ||
        check_exchange("4k4/9/9/9/9/9/9/9/4K4 b P 1", "P*5e", 0) ||
        check_exchange("4k4/9/9/4p4/9/9/9/9/4K4 b P 1", "P*5e", -200) ||
        check_exchange("4k4/9/4P4/9/9/9/9/9/4K4 b - 1", "5c5b+", -200)) return 1;

    SearchOptions bounded = options;
    bounded.mode = SEARCH_MODE_ALPHABETA;
    bounded.hash_mb = 1;
    static const uint64_t budgets[] = {1, 7, 30, 31, 200, 1000};
    for (unsigned policy = 0; policy < 3; ++policy) {
        bounded.ab_policy = policy;
        for (size_t index = 0; index < 8 * sizeof(budgets) / sizeof(budgets[0]); ++index) {
            search_context_clear(context);
            memset(&limits, 0, sizeof(limits));
            limits.nodes = budgets[index % (sizeof(budgets) / sizeof(budgets[0]))];
            size_t variant = index / (sizeof(budgets) / sizeof(budgets[0]));
            bounded.ab_partial_root = (variant & 1) != 0;
            bounded.ab_quiescence_hash = (variant & 2) != 0;
            bounded.ab_shallow_transpositions = (variant & 4) != 0;
            limits.depth = INT_MAX;
            job = search_start(&position, &limits, &bounded);
            if (job == NULL) return fail("bounded alpha-beta creation");
            search_join(job, &result);
            if (!result.has_move || result.simulations > limits.nodes)
                return fail("alpha-beta node limit includes root and quiescence");
            SearchDiagnostics diagnostics;
            if (!search_get_diagnostics(job, &diagnostics) ||
                diagnostics.main_nodes + diagnostics.quiescence_nodes + diagnostics.root_nodes !=
                    result.simulations)
                return fail("alpha-beta node partition");
            search_destroy(job);
        }
    }

    ShogiPosition null_position = position;
    shogi_search_null_move(&null_position);
    if (null_position.side == position.side || null_position.hash == position.hash ||
        null_position.history_length != position.history_length)
        return fail("null move isolation");
    shogi_search_null_move(&null_position);
    if (memcmp(&null_position, &position, sizeof(position)) != 0)
        return fail("null move restoration");

    /* Exercise the verified-null branch on rich material, and read progress
     * while its worker is running (also useful under ThreadSanitizer). */
    unsigned null_evaluations = 0;
    ShogiEvaluator null_probe;
    shogi_evaluator_init(&null_probe);
    shogi_evaluator_set(&null_probe, &null_evaluations, null_probe_eval, NULL, "null probe");
    bounded.ab_policy = 2;
    bounded.evaluator = &null_probe;
    bounded.quiescence_depth = 0;
    search_context_clear(context);
    memset(&limits, 0, sizeof(limits));
    limits.nodes = 50000;
    limits.depth = 8;
    job = search_start(&position, &limits, &bounded);
    if (job == NULL) return fail("verified null creation");
    while (!search_is_done(job)) {
        search_get_progress(job, &progress);
        if (progress.nodes > limits.nodes) return fail("live alpha-beta node budget");
        if (progress.has_move) {
            ShogiPosition next = position;
            if (!shogi_make_move(&next, progress.move)) return fail("atomic progress move");
        }
        search_get_root_lines(job, lines, 2);
    }
    search_join(job, &result);
    if (!result.has_move || result.simulations > limits.nodes || null_evaluations == 0)
        return fail("verified null branch and node accounting");
    search_destroy(job);
    shogi_evaluator_destroy(&null_probe);

    ShogiEvaluator constant;
    shogi_evaluator_init(&constant);
    shogi_evaluator_set(&constant, NULL, constant_eval, NULL, "constant");
    bounded.evaluator = &constant;
    bounded.quiescence_depth = 0;
    /* Two legal move orders reach the same position without repetitions.
     * The shallow mode must actually reuse score bounds, not just moves. */
    ShogiPosition transposed[2];
    const char *orders[2][4] = {{"7g7f", "3c3d", "2g2f", "8c8d"},
                              {"2g2f", "8c8d", "7g7f", "3c3d"}};
    for (unsigned i = 0; i < 2; ++i) {
        shogi_position_start(&transposed[i]);
        for (unsigned j = 0; j < 4; ++j)
            if (!shogi_parse_and_make_move(&transposed[i], orders[i][j]))
                return fail("transposition fixture");
    }
    if (transposed[0].hash != transposed[1].hash) return fail("transposition board equality");
    for (unsigned enabled = 0; enabled < 2; ++enabled) {
        bounded.ab_shallow_transpositions = enabled != 0;
        search_context_clear(context);
        memset(&limits, 0, sizeof(limits));
        limits.depth = 2;
        limits.nodes = 10000;
        for (unsigned i = 0; i < 2; ++i) {
            job = search_start(&transposed[i], &limits, &bounded);
            if (job == NULL) return fail("transposition search creation");
            search_join(job, &result);
            search_get_progress(job, &progress);
            SearchDiagnostics diagnostics;
            search_get_diagnostics(job, &diagnostics);
            if (progress.depth != 2 || progress.score_cp != 500)
                return fail("transposition preserves completed score");
            if (i == 1 && ((diagnostics.transposition_cutoffs != 0) != (enabled != 0)))
                return fail("guarded cross-history transposition reuse");
            search_destroy(job);
        }
    }
    for (unsigned policy = 0; policy < 3; ++policy) {
        bounded.ab_policy = policy;
        ShogiPosition repeated, fresh;
        shogi_position_from_sfen(&repeated, "4k4/9/9/9/9/9/9/9/4K4 b - 1");
        const char *cycle[] = {"5i5h", "5a5b", "5h5i", "5b5a"};
        for (unsigned index = 0; index < 11; ++index)
            if (!shogi_parse_and_make_move(&repeated, cycle[index % 4])) return fail("repetition fixture");
        char sfen[512];
        shogi_position_to_sfen(&repeated, sfen, sizeof(sfen));
        shogi_position_from_sfen(&fresh, sfen);
        memset(&limits, 0, sizeof(limits));
        limits.nodes = 1000;
        limits.depth = 3;
        limits.has_searchmoves = true;
        limits.searchmove_count = 1;
        shogi_parse_usi_move("5b5a", &limits.searchmoves[0]);
        search_context_clear(context);
        job = search_start(&fresh, &limits, &bounded);
        if (job == NULL) return fail("fresh repetition TT search");
        search_join(job, &result);
        search_destroy(job);
        job = search_start(&repeated, &limits, &bounded);
        if (job == NULL) return fail("repetition TT search");
        search_join(job, &result);
        search_get_progress(job, &progress);
        if (progress.score_cp != 0) return fail("repetition precedes cached score");
        search_destroy(job);

        /* Repetition can occur BELOW a cached node, not just at its entry.
         * Warm a history-free score, then search the same board two plies
         * before the fourth occurrence. White prefers the ensuing draw. */
        shogi_position_from_sfen(&repeated, "4k4/9/9/9/9/9/9/9/4K4 b - 1");
        for (unsigned index = 0; index < 10; ++index)
            if (!shogi_parse_and_make_move(&repeated, cycle[index % 4]))
                return fail("ancestor repetition fixture");
        shogi_position_to_sfen(&repeated, sfen, sizeof(sfen));
        shogi_position_from_sfen(&fresh, sfen);
        shogi_parse_usi_move("5h5i", &limits.searchmoves[0]);
        search_context_clear(context);
        job = search_start(&fresh, &limits, &bounded);
        if (job == NULL) return fail("fresh ancestor repetition TT search");
        search_join(job, &result);
        search_get_progress(job, &progress);
        if (progress.score_cp != 500) return fail("history-free ancestor score");
        search_destroy(job);
        job = search_start(&repeated, &limits, &bounded);
        if (job == NULL) return fail("ancestor repetition TT search");
        search_join(job, &result);
        search_get_progress(job, &progress);
        if (progress.score_cp != 0) return fail("cached ancestor cannot hide repetition");
        search_destroy(job);
    }
    shogi_evaluator_destroy(&constant);

    /* Depth one prefers the first root move; a completed depth-two child
     * refutes it. Retain the better second child if the third is interrupted,
     * without publishing an unfinished child's bound as an exact result. */
    ShogiMove root_moves[3];
    shogi_parse_usi_move("7g7f", &root_moves[0]);
    shogi_parse_usi_move("2g2f", &root_moves[1]);
    shogi_parse_usi_move("3g3f", &root_moves[2]);
    ShogiEvaluator root_probe;
    shogi_evaluator_init(&root_probe);
    shogi_evaluator_set(&root_probe, root_moves, root_update_eval, NULL, "root update probe");
    bounded.evaluator = &root_probe;
    bounded.quiescence_depth = 0;
    bounded.ab_policy = 1;
    bounded.aspiration_window = 2000;
    bool observed_partial = false;
    for (unsigned budget = 8; budget < 120 && !observed_partial; ++budget) {
        SearchProgress snapshots[2];
        for (unsigned partial = 0; partial < 2; ++partial) {
            bounded.ab_partial_root = partial != 0;
            search_context_clear(context);
            memset(&limits, 0, sizeof(limits));
            limits.nodes = budget;
            limits.depth = 2;
            limits.has_searchmoves = true;
            limits.searchmove_count = 3;
            memcpy(limits.searchmoves, root_moves, sizeof(root_moves));
            job = search_start(&position, &limits, &bounded);
            if (job == NULL) return fail("partial root search creation");
            search_join(job, &result);
            search_get_progress(job, &snapshots[partial]);
            if (result.simulations > budget) return fail("partial root node accounting");
            search_destroy(job);
        }
        observed_partial = snapshots[0].depth == 1 && snapshots[1].depth == 1 &&
            snapshots[0].move.to == root_moves[0].to && snapshots[0].score_cp == 100 &&
            snapshots[1].move.to == root_moves[1].to && snapshots[1].score_cp == 0;
    }
    if (!observed_partial) return fail("publish completed exact child of unfinished iteration");
    shogi_evaluator_destroy(&root_probe);

    ShogiPosition mate;
    shogi_position_from_sfen(&mate, "4k4/9/2N1S1N2/9/9/9/9/9/4K4 b G 1");
    bounded.evaluator = NULL;
    memset(&limits, 0, sizeof(limits));
    limits.nodes = 1000;
    limits.depth = 3;
    limits.has_searchmoves = true;
    limits.searchmove_count = 1;
    shogi_parse_usi_move("G*5b", &limits.searchmoves[0]);
    search_context_clear(context);
    job = search_start(&mate, &limits, &bounded);
    if (job == NULL) return fail("mate score search");
    search_join(job, &result);
    search_get_progress(job, &progress);
    if (!result.has_move || progress.score_cp != 28999 ||
        progress.move.drop != SHOGI_GOLD || progress.move.to != limits.searchmoves[0].to)
        return fail("mate distance / unclipped score reporting");
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
