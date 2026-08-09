#ifndef TINYSHOGI_SIMD_H
#define TINYSHOGI_SIMD_H

#include <stddef.h>
#include <stdint.h>

const char *tinyshogi_simd_backend(void);
int32_t tinyshogi_dot_i8_i8(const int8_t *left, const int8_t *right, size_t count);
void tinyshogi_dot_i8_i8_8(const int8_t *left, const int8_t *weights,
                           size_t stride, size_t count, int32_t out[8]);
void tinyshogi_gemm_i8_6x64(size_t count, const int8_t *a, const int8_t *b,
                            int32_t *c, size_t ldc);
void tinyshogi_gemm_i8_64x6(size_t count, const int8_t *weights,
                            const int8_t *positions, int32_t *output,
                            size_t output_stride);
void tinyshogi_gemm_i8_64x5(size_t count, const int8_t *weights,
                            const int8_t *positions, int32_t *output,
                            size_t output_stride);
void tinyshogi_gemm_i16_6x32(size_t count, const int16_t *a, const int16_t *b,
                             int64_t *c, size_t ldc);
/* NNUE3 head tile: four packed output vectors by five positions. */
void tinyshogi_nnue_head_gemm_i16_32x5(size_t count, const int16_t *weights,
                                       const int16_t *positions, int64_t *output);
/* NNUE3 head tile: six packed positions by four output vectors. */
void tinyshogi_nnue_head_gemm_i16_6x32(size_t count, const int16_t *weights,
                                       const int16_t *positions, int64_t *output);
int32_t tinyshogi_dot_i16_i8(const int16_t *left, const int8_t *right, size_t count);
int64_t tinyshogi_dot_i16_i16(const int16_t *left, const int16_t *right, size_t count);
void tinyshogi_dot_i16_i16_4(const int16_t *left, const int16_t *weights,
                             size_t stride, size_t count, int64_t out[4]);
void tinyshogi_dot_i16_i16_8(const int16_t *left, const int16_t *weights,
                             size_t stride, size_t count, int64_t out[8]);
/* Evaluate eight pre-clipped NNUE activation rows against one shared output
 * vector. Positions are row-major with stride measured in int16 elements. */
void tinyshogi_dot_i16_i16_batch8(const int16_t *positions, size_t stride,
                                  const int16_t *weights, size_t count,
                                  int64_t out[8]);
int64_t tinyshogi_dot_relu_i32_i16(const int32_t *left, const int16_t *right, size_t count);
int64_t tinyshogi_dot_clip_i32_i16(const int32_t *left, const int16_t *right,
                                   size_t count, int32_t clip);
void tinyshogi_add_i16_i32(int32_t *accumulator, const int16_t *weights,
                           size_t count, int sign);
void tinyshogi_add_i16_i32_rows(int32_t *accumulator,
                                const int16_t *const *rows,
                                size_t row_count, size_t count, int sign);
void tinyshogi_add_f32(float *accumulator, const float *values, size_t count);

#endif
