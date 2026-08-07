#ifndef TINYSHOGI_SIMD_H
#define TINYSHOGI_SIMD_H

#include <stddef.h>
#include <stdint.h>

const char *tinyshogi_simd_backend(void);
int32_t tinyshogi_dot_i8_i8(const int8_t *left, const int8_t *right, size_t count);
int32_t tinyshogi_dot_i16_i8(const int16_t *left, const int8_t *right, size_t count);
int64_t tinyshogi_dot_relu_i32_i16(const int32_t *left, const int16_t *right, size_t count);
void tinyshogi_add_i16_i32(int32_t *accumulator, const int16_t *weights,
                           size_t count, int sign);
void tinyshogi_add_i16_i32_rows(int32_t *accumulator,
                                const int16_t *const *rows,
                                size_t row_count, size_t count, int sign);
void tinyshogi_add_f32(float *accumulator, const float *values, size_t count);

#endif
