/* SPDX-License-Identifier: Apache-2.0 */
#include "dl_features.h"
#include "search.h"
#include <assert.h>
#include <math.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
static ShogiMove wanted;
static bool equal(ShogiMove a, ShogiMove b) {
    return a.from == b.from && a.to == b.to && a.drop == b.drop && a.promote == b.promote &&
           a.piece == b.piece;
}
static bool oracle(void *u, const ShogiPosition *const *p, const ShogiMove *const *moves,
                   const size_t *counts, size_t batch, float *const *out, float *wdl) {
    for (size_t b = 0; b < batch; b++) {
        if (u)
            return false;
        for (size_t i = 0; i < counts[b]; i++)
            out[b][i] = equal(moves[b][i], wanted) ? 3 : 0;
        bool good = p[b]->board[wanted.from] == SHOGI_EMPTY;
        bool win = good == (p[b]->side == SHOGI_BLACK);
        wdl[3 * b] = win ? 1 : 0;
        wdl[3 * b + 1] = 0;
        wdl[3 * b + 2] = win ? 0 : 1;
    }
    return true;
}
int main(void) {
    shogi_init();
    ShogiPosition p;
    shogi_position_start(&p);
    assert(shogi_parse_usi_move("7g7f", &wanted));
    float *a = malloc(SHOGI_DL_FEATURES * 4), *b = malloc(SHOGI_DL_FEATURES * 4);
    assert(a && b);
    for (unsigned ply = 0; ply < 120; ply++) {
        ShogiMove moves[SHOGI_MAX_MOVES];
        size_t count = shogi_generate_legal(&p, moves, SHOGI_MAX_MOVES);
        if (!count)
            break;
        unsigned char seen[SHOGI_DL_ACTIONS] = {0};
        for (size_t i = 0; i < count; i++) {
            int id = shogi_dl_action(&p, moves[i]);
            if (id < 0 || id >= (int)SHOGI_DL_ACTIONS || seen[id]) {
                char text[16];
                shogi_move_to_usi(moves[i], text, sizeof(text));
                fprintf(
                    stderr,
                    "action failure ply %u side %d move %s from %u to %u piece %u drop %u id %d\n",
                    ply, p.side, text, moves[i].from, moves[i].to, moves[i].piece, moves[i].drop,
                    id);
            }
            assert(id >= 0 && id < (int)SHOGI_DL_ACTIONS && !seen[id]);
            seen[id] = 1;
        }
        shogi_dl_encode(&p, a);
        for (size_t i = 0; i < SHOGI_DL_FEATURES; i++)
            assert(isfinite(a[i]));
        assert(shogi_make_move(&p, moves[(ply * 37 + 3) % count]));
    }
    shogi_position_start(&p);
    ShogiPosition rotated = p;
    rotated.side = SHOGI_WHITE;
    for (int i = 0; i < 81; i++) {
        uint8_t piece = p.board[i];
        rotated.board[80 - i] =
            piece == SHOGI_EMPTY
                ? piece
                : shogi_piece((ShogiColor)(shogi_piece_color(piece) ^ 1), shogi_piece_type(piece));
    }
    rotated.king_square[0] = 80 - p.king_square[1];
    rotated.king_square[1] = 80 - p.king_square[0];
    shogi_dl_encode(&p, a);
    shogi_dl_encode(&rotated, b);
    assert(!memcmp(a, b, SHOGI_DL_FEATURES * 4));
    /* Explicit drops, mandatory promotion, knight planes, and history planes. */
    assert(shogi_position_from_sfen(&p, "4k4/9/9/9/9/9/9/9/4K4 b RBGSNLP 1"));
    const char *drops[] = {"P*1e", "L*1e", "N*1e", "S*1e", "G*1e", "B*1e", "R*1e"};
    for (int i = 0; i < 7; i++) {
        ShogiMove move;
        assert(shogi_parse_usi_move(drops[i], &move));
        assert(shogi_dl_action(&p, move) == move.to * 139 + 132 + i);
    }
    assert(shogi_position_from_sfen(&p, "4k4/1P7/9/9/9/9/9/9/4K4 b - 1"));
    ShogiMove promotion;
    assert(shogi_parse_usi_move("8b8a+", &promotion));
    assert(shogi_dl_action(&p, promotion) == promotion.from * 139 + 1);
    assert(shogi_make_move(&p, promotion));
    assert(shogi_position_from_sfen(&p, "4k4/9/1N7/9/9/9/9/9/4K4 b - 1"));
    assert(shogi_parse_usi_move("8c7a+", &promotion));
    assert(shogi_dl_action(&p, promotion) == promotion.from * 139 + 131);
    assert(shogi_make_move(&p, promotion));
    assert(shogi_position_from_sfen(&p, "4k4/9/9/9/9/9/9/9/4K4 b - 1"));
    const char *cycle[] = {"5i5h", "5a5b", "5h5i", "5b5a"};
    for (int repeat = 1; repeat <= 3; repeat++) {
        for (int i = 0; i < 4; i++)
            assert(shogi_parse_and_make_move(&p, cycle[i]));
        shogi_dl_encode(&p, a);
        assert(a[72] == 1 && a[73] == (repeat >= 2) && a[74] == (repeat >= 3));
        assert(a[75] == 0 && a[76] == 0);
    }
    assert(shogi_position_from_sfen(&p, "4R3k/9/9/9/9/9/9/9/K8 w - 1"));
    const char *perpetual[] = {"1a1b", "5a5b", "1b1a", "5b5a"};
    for (int i = 0; i < 4; i++)
        assert(shogi_parse_and_make_move(&p, perpetual[i]));
    shogi_dl_encode(&p, a);
    assert(a[70] == 1 && a[72] == 1 && a[75] == 0 && a[76] == 1);
    char sfen[256];
    assert(shogi_position_to_sfen(&p, sfen, sizeof(sfen)));
    assert(shogi_position_from_sfen(&rotated, sfen));
    shogi_dl_encode(&rotated, b);
    assert(a[72] != b[72]); /* same board, distinct history-sensitive input */
    shogi_position_start(&p);
    SearchOptions options = search_default_options();
    SearchLimits limits = {.nodes = 64};
    options.mode = SEARCH_MODE_PUCT;
    options.threads = 1;
    options.max_tree_nodes = 1000;
    assert(!search_start(&p, &limits, &options));
    ShogiPolicyValueEvaluator evaluator = {NULL, oracle};
    options.policy_value = &evaluator;
    SearchJob *job = search_start(&p, &limits, &options);
    assert(job);
    SearchResult result;
    search_join(job, &result);
    assert(!result.failed && result.has_move && result.move.from == wanted.from &&
           result.move.to == wanted.to);
    assert(result.simulations == 64);
    search_destroy(job);
    options.threads = 4;
    job = search_start(&p, &limits, &options);
    assert(job);
    search_join(job, &result);
    assert(!result.failed && result.has_move && result.simulations == 64);
    SearchPolicyEntry policy[SHOGI_MAX_MOVES];
    size_t count = search_get_root_policy(job, policy, SHOGI_MAX_MOVES);
    uint64_t total = 0;
    for (size_t i = 0; i < count; i++)
        total += policy[i].visits;
    assert(total > 0 && total < result.simulations);
    search_destroy(job);
    limits.infinite = true;
    limits.nodes = 0;
    job = search_start(&p, &limits, &options);
    assert(job);
    search_request_stop(job);
    search_join(job, &result);
    assert(!result.failed && search_is_done(job));
    search_destroy(job);
    limits.infinite = false;
    limits.nodes = 64;
    evaluator.userdata = &p;
    job = search_start(&p, &limits, &options);
    assert(job);
    search_join(job, &result);
    assert(result.failed && !result.has_move);
    search_destroy(job);
    free(a);
    free(b);
    puts("PASS feature/action/history fixtures, PUCT signs/budget/multithreading/cancellation, "
         "inference failure");
    return 0;
}
