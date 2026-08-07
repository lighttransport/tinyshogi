#include "../src/simd.h"

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
