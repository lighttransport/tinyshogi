#include "../src/simd.h"

#include <stdint.h>
#include <stdio.h>

int main(void) {
    const int8_t a8[17] = {1, -2, 3, 4, 5, -6, 7, 8, -9, 10, 11, -12, 13, 14, 15, -16, 17};
    const int8_t b8[17] = {-3, 4, 5, -6, 7, 8, -9, 10, 11, -12, 13, 14, -15, 16, 17, 18, -19};
    const int16_t a16[17] = {100, -200, 300, 400, 500, -600, 700, 800, -900, 1000, 1100, -1200, 1300, 1400, 1500, -1600, 1700};
    int32_t expected8 = 0, expected16 = 0;
    for (size_t i = 0; i < 17; ++i) {
        expected8 += (int32_t)a8[i] * b8[i];
        expected16 += (int32_t)a16[i] * b8[i];
    }
    if (tinyshogi_dot_i8_i8(a8, b8, 17) != expected8 ||
        tinyshogi_dot_i16_i8(a16, b8, 17) != expected16) return 1;
    const int32_t relu_left[17] = {1, -2, 3, -4, 5, -6, 7, -8, 9, -10, 11, -12, 13, -14, 15, -16, 17};
    const int16_t relu_right[17] = {2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18};
    int64_t expected_relu = 0;
    for (size_t i = 0; i < 17; ++i)
        if (relu_left[i] > 0) expected_relu += (int64_t)relu_left[i] * relu_right[i];
    if (tinyshogi_dot_relu_i32_i16(relu_left, relu_right, 17) != expected_relu) return 1;
    int32_t clip_left[256];
    int16_t clip_right[256];
    int64_t expected_clip = 0;
    for (size_t i = 0; i < 256; ++i) {
        clip_left[i] = (int32_t)(i % 41U) - 13;
        clip_right[i] = (int16_t)((int)(i % 17U) - 8);
        int32_t activation = clip_left[i];
        if (activation < 0) activation = 0;
        if (activation > 11) activation = 11;
        expected_clip += (int64_t)activation * clip_right[i];
    }
    int64_t actual_clip = tinyshogi_dot_clip_i32_i16(clip_left, clip_right, 256, 11);
    if (actual_clip != expected_clip) {
        fprintf(stderr, "clipped dot mismatch: got=%lld expected=%lld\n",
                (long long)actual_clip, (long long)expected_clip);
        return 1;
    }
    int16_t batch_positions[8 * 256], batch_weights[256];
    int64_t batch_expected[8], batch_actual[8];
    for (size_t position = 0; position < 8; ++position)
        for (size_t i = 0; i < 256; ++i)
            batch_positions[position * 256 + i] = (int16_t)((position * 7 + i) % 31U) - 15;
    for (size_t i = 0; i < 256; ++i) batch_weights[i] = (int16_t)((i * 3U) % 23U) - 11;
    for (size_t position = 0; position < 8; ++position) {
        batch_expected[position] = 0;
        for (size_t i = 0; i < 256; ++i)
            batch_expected[position] += (int64_t)batch_positions[position * 256 + i] * batch_weights[i];
    }
    tinyshogi_dot_i16_i16_batch8(batch_positions, 256, batch_weights, 256, batch_actual);
    for (size_t position = 0; position < 8; ++position)
        if (batch_actual[position] != batch_expected[position]) return 1;
    int32_t sums[17] = {0};
    tinyshogi_add_i16_i32(sums, a16, 17, 1);
    for (size_t i = 0; i < 17; ++i) if (sums[i] != a16[i]) return 1;
    tinyshogi_add_i16_i32(sums, a16, 17, -1);
    for (size_t i = 0; i < 17; ++i) if (sums[i] != 0) return 1;
    const int16_t *rows[2] = {a16, a16};
    tinyshogi_add_i16_i32_rows(sums, rows, 2, 17, 1);
    for (size_t i = 0; i < 17; ++i) if (sums[i] != (int32_t)a16[i] * 2) return 1;
    float floats[17] = {0};
    float increments[17];
    for (size_t i = 0; i < 17; ++i) increments[i] = (float)i - 4.0f;
    tinyshogi_add_f32(floats, increments, 17);
    for (size_t i = 0; i < 17; ++i) if (floats[i] != increments[i]) return 1;
    printf("simd backend=%s\n", tinyshogi_simd_backend());
    return 0;
}
