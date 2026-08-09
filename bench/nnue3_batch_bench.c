#define _POSIX_C_SOURCE 200809L
#include "../src/nnue.h"
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <time.h>

static double now(void) {
    struct timespec t; clock_gettime(CLOCK_MONOTONIC, &t);
    return (double)t.tv_sec + (double)t.tv_nsec * 1e-9;
}

int main(int argc, char **argv) {
    if (argc < 2) return 2;
    unsigned rounds = argc > 2 ? (unsigned)strtoul(argv[2], NULL, 10) : 100000U;
    shogi_init();
    ShogiNnueModel model; shogi_nnue_model_init(&model);
    if (!shogi_nnue_model_load(&model, argv[1]) || model.format_version != SHOGI_NNUE3_FORMAT_VERSION ||
        model.hidden_dim != 256U || model.head_dim != 32U) return 1;
    ShogiNnueState states[6]; const ShogiNnueState *p[6];
    for (unsigned i = 0; i < 6U; ++i) {
        ShogiPosition position; shogi_position_start(&position);
        if (i != 0U) {
            ShogiMove moves[SHOGI_MAX_MOVES]; size_t n = shogi_generate_legal(&position, moves, SHOGI_MAX_MOVES);
            ShogiUndo undo; if (n <= i || !shogi_make_move_undo(&position, moves[i], &undo)) return 1;
        }
        if (!shogi_nnue_state_init(&states[i], &model, SHOGI_BLACK) ||
            !shogi_nnue_state_reset(&states[i], &position)) return 1;
        p[i] = &states[i];
    }
    int scores[6], scalar[6];
    for (unsigned i = 0; i < 6U; ++i) scalar[i] = shogi_nnue_state_evaluate(&states[i]);
    if (!shogi_nnue_state_evaluate_batch(p, 5, scores)) return 1;
    for (unsigned i = 0; i < 5U; ++i) if (scores[i] != scalar[i]) return 1;
    if (!shogi_nnue_state_evaluate_batch(p, 6, scores)) return 1;
    for (unsigned i = 0; i < 6U; ++i) if (scores[i] != scalar[i]) return 1;
    volatile int checksum = 0;
    for (unsigned i = 0; i < 1000U; ++i) { shogi_nnue_state_evaluate_batch(p, 6, scores); checksum += scores[i % 6U]; }
    double begin = now();
    for (unsigned i = 0; i < rounds; ++i) { shogi_nnue_state_evaluate_batch(p, 6, scores); checksum += scores[i % 6U]; }
    double elapsed = now() - begin;
    double positions = 6.0 * rounds;
    double gops = positions * 2.0 * 32.0 * 256.0 / elapsed / 1e9;
    printf("PASS model=%s batches=%u seconds=%.6f positions/s=%.0f ns/position=%.2f "
           "GOPS=%.2f arithmetic_peak_efficiency_2GHz=%.2f%% checksum=%d\n",
           argv[1], rounds, elapsed, positions / elapsed, elapsed * 1e9 / positions,
           gops, gops / 256.0 * 100.0, checksum);
    for (unsigned i = 0; i < 6U; ++i) shogi_nnue_state_destroy(&states[i]);
    shogi_nnue_model_destroy(&model); return 0;
}
