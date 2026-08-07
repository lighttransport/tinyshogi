#ifndef TINYSHOGI_A64FX_SDOT_GEMM_H
#define TINYSHOGI_A64FX_SDOT_GEMM_H

#include <stdint.h>

/* A64FX SVE 512-bit INT8 SDOT 4x5 microkernel.
 * A and B use the packed panel layout documented by the pack helpers in the
 * benchmark: A is [K/4][4][64] bytes, B is [K/4][5][4] bytes. C is column
 * major with ldc elements between output columns. K must be a multiple of 4.
 */
void tinyshogi_a64fx_sdot_gemm_4x5(int64_t K, const int8_t *A,
                                   const int8_t *B, int32_t *C,
                                   int64_t ldc);

/* INT16 variant: A is [K/4][4][64] bytes, B is [K/4][5][8] bytes and
 * C is column-major int64_t. K must be a positive multiple of four. */
void tinyshogi_a64fx_sdot_gemm_4x5_i16(int64_t K, const int16_t *A,
                                       const int16_t *B, int64_t *C,
                                       int64_t ldc);

/* 6x4 layout follows Clair's high-throughput form: A is [K/4][6][4]
 * bytes, B is [K/4][4][64] bytes, and C is a row-major 6x64 tile. */
void tinyshogi_a64fx_sdot_gemm_6x4(int64_t K, const int8_t *A,
                                   const int8_t *B, int32_t *C,
                                   int64_t ldc);

void tinyshogi_a64fx_sdot_gemm_6x4_i16(int64_t K, const int16_t *A,
                                       const int16_t *B, int64_t *C,
                                       int64_t ldc);

#endif
