#define _POSIX_C_SOURCE 200809L

#include "../src/nnue.h"
#include "../src/simd.h"

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
    size_t count = argc > 1 ? (size_t)strtoul(argv[1], NULL, 10) : 256U;
    unsigned rounds = argc > 2 ? (unsigned)strtoul(argv[2], NULL, 10) : 1000000U;
    if (count != 256U || rounds == 0) return 2;
    shogi_init();
    ShogiNnueModel model;
    shogi_nnue_model_init(&model);
    if (!shogi_nnue_model_init_default(&model, (uint32_t)count)) return 1;
    model.format_version = SHOGI_NNUE2_FORMAT_VERSION;
    model.activation_clip = 127;
    for (size_t i = 0; i < (size_t)model.feature_count * model.hidden_dim; ++i)
        model.feature_weights[i] = (int16_t)((i % 17U) - 8);
    for (size_t i = 0; i < (size_t)model.hidden_dim * 2U; ++i)
        model.output_weights[i] = (int16_t)((i % 13U) - 6);
    ShogiNnueState states[8];
    memset(states, 0, sizeof(states));
    size_t initialized = 0;
    int16_t *positions = NULL;
    const int16_t *weights = NULL;
    int64_t batch[8], scalar[8];
    volatile int64_t checksum = 0;
    double begin = 0.0, elapsed = 0.0;
    double positions_per_second = 0.0, gops = 0.0;
    for (size_t position_index = 0; position_index < 8; ++position_index) {
        ShogiPosition position;
        shogi_position_start(&position);
        if (position_index != 0) {
            ShogiMove moves[SHOGI_MAX_MOVES];
            size_t move_count = shogi_generate_legal(&position, moves, SHOGI_MAX_MOVES);
            ShogiUndo undo;
            if (move_count <= position_index ||
                !shogi_make_move_undo(&position, moves[position_index], &undo)) goto fail;
        }
        if (!shogi_nnue_state_init(&states[position_index], &model, SHOGI_BLACK)) goto fail;
        ++initialized;
        if (!shogi_nnue_state_reset(&states[position_index], &position)) goto fail;
    }
    positions = aligned_alloc(256U, 8U * count * sizeof(*positions));
    weights = model.output_weights;
    if (positions == NULL) goto fail;
    for (size_t position = 0; position < 8; ++position)
        for (size_t i = 0; i < count; ++i) {
            int32_t activation = states[position].sum[i];
            if (activation < 0) activation = 0;
            if (activation > model.activation_clip) activation = model.activation_clip;
            positions[position * count + i] = (int16_t)activation;
        }
    tinyshogi_dot_i16_i16_batch8(positions, count, weights, count, batch);
    for (size_t position = 0; position < 8; ++position)
        scalar[position] = tinyshogi_dot_i16_i16(positions + position * count, weights, count);
    for (size_t position = 0; position < 8; ++position)
        if (batch[position] != scalar[position]) goto fail;

    for (unsigned i = 0; i < 1000; ++i) {
        tinyshogi_dot_i16_i16_batch8(positions, count, weights, count, batch);
        checksum += batch[i & 7U];
    }
    begin = seconds();
    for (unsigned i = 0; i < rounds; ++i) {
        tinyshogi_dot_i16_i16_batch8(positions, count, weights, count, batch);
        checksum += batch[i & 7U];
    }
    elapsed = seconds() - begin;
    positions_per_second = 8.0 * rounds / elapsed;
    gops = 2.0 * 8.0 * count * rounds / elapsed / 1.0e9;
    printf("PASS width=%zu batches=%u seconds=%.6f positions/s=%.0f "
           "ns/position=%.1f GOPS=%.2f arithmetic_peak_efficiency_2GHz=%.2f%% "
           "checksum=%lld\n", count, rounds, elapsed, positions_per_second,
           elapsed * 1.0e9 / (8.0 * rounds), gops, gops / 256.0 * 100.0,
           (long long)checksum);
    free(positions);
    positions = NULL;
    for (size_t position = 0; position < initialized; ++position)
        shogi_nnue_state_destroy(&states[position]);
    shogi_nnue_model_destroy(&model);
    return 0;

fail:
    free(positions);
    for (size_t position = 0; position < initialized; ++position)
        shogi_nnue_state_destroy(&states[position]);
    shogi_nnue_model_destroy(&model);
    return 1;
}
