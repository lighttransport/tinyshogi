#define _POSIX_C_SOURCE 200809L

#include "../src/nnue.h"

#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

static double seconds(void) {
    struct timespec now;
    clock_gettime(CLOCK_MONOTONIC, &now);
    return (double)now.tv_sec + (double)now.tv_nsec * 1.0e-9;
}

int main(int argc, char **argv) {
    int rounds = argc > 1 ? atoi(argv[1]) : 100000;
    const char *save_path = argc > 2 ? argv[2] : NULL;
    if (rounds <= 0) return 2;
    shogi_init();

    ShogiNnueModel model;
    shogi_nnue_model_init(&model);
    if (!shogi_nnue_model_init_default(&model, 256)) return 1;
    model.format_version = SHOGI_NNUE2_FORMAT_VERSION;
    model.activation_clip = 127;
    for (size_t i = 0; i < (size_t)model.feature_count * model.hidden_dim; ++i)
        model.feature_weights[i] = (int16_t)((int)(i % 17U) - 8);
    for (size_t i = 0; i < (size_t)model.hidden_dim * 2U; ++i)
        model.output_weights[i] = (int16_t)((int)(i % 13U) - 6);
    if (save_path != NULL && !shogi_nnue_model_save(&model, save_path)) return 1;

    ShogiPosition position;
    shogi_position_start(&position);
    ShogiMove moves[SHOGI_MAX_MOVES];
    size_t move_count = shogi_generate_legal(&position, moves, SHOGI_MAX_MOVES);
    if (move_count == 0) return 1;
    ShogiMove move = moves[0];

    ShogiNnueState state;
    if (!shogi_nnue_state_init(&state, &model, SHOGI_BLACK) ||
        !shogi_nnue_state_reset(&state, &position)) return 1;
    ShogiUndo undo;
    ShogiNnueDelta delta;
    if (!shogi_make_move_undo(&position, move, &undo) ||
        !shogi_nnue_state_apply_move(&state, &position, &undo, &delta)) return 1;
    ShogiNnueAccumulator rebuilt;
    if (!shogi_nnue_accumulator_init(&rebuilt, model.hidden_dim) ||
        !shogi_nnue_accumulator_build(&model, &position, &rebuilt) ||
        memcmp(state.sum, rebuilt.sum[SHOGI_BLACK],
               model.hidden_dim * sizeof(*state.sum)) != 0) return 1;
    if (!shogi_unmake_move(&position, &undo) ||
        !shogi_nnue_state_unapply_move(&state, &position, &delta)) return 1;

    volatile int64_t checksum = 0;
    for (int warmup = 0; warmup < 1000; ++warmup) {
        if (!shogi_make_move_undo(&position, move, &undo) ||
            !shogi_nnue_state_apply_move(&state, &position, &undo, &delta)) return 1;
        checksum += shogi_nnue_state_evaluate(&state);
        if (!shogi_unmake_move(&position, &undo) ||
            !shogi_nnue_state_unapply_move(&state, &position, &delta)) return 1;
        checksum += shogi_nnue_state_evaluate(&state);
    }
    double begin = seconds();
    for (int iteration = 0; iteration < rounds; ++iteration) {
        if (!shogi_make_move_undo(&position, move, &undo) ||
            !shogi_nnue_state_apply_move(&state, &position, &undo, &delta)) return 1;
        checksum += shogi_nnue_state_evaluate(&state);
        if (!shogi_unmake_move(&position, &undo) ||
            !shogi_nnue_state_unapply_move(&state, &position, &delta)) return 1;
        checksum += shogi_nnue_state_evaluate(&state);
    }
    double elapsed = seconds() - begin;
    printf("rounds=%d evaluations=%d seconds=%.6f moves/s=%.0f evals/s=%.0f "
           "ns/move-eval-undo=%.1f checksum=%lld\n",
           rounds, rounds * 2, elapsed, rounds / elapsed,
           rounds * 2.0 / elapsed, elapsed * 1.0e9 / rounds,
           (long long)checksum);
    shogi_nnue_accumulator_destroy(&rebuilt);
    shogi_nnue_state_destroy(&state);
    shogi_nnue_model_destroy(&model);
    return 0;
}
