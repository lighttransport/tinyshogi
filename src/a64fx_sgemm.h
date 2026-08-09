#ifndef TINYSHOGI_A64FX_SGEMM_H
#define TINYSHOGI_A64FX_SGEMM_H

#include <stdint.h>

void tinyshogi_a64fx_sgemm_4x5(int64_t K, const float *A, const float *B,
                               float *C, int64_t ldc);

/* Clair-derived 48x8 packed FP32 tile. A is [K][48], B is [K][8],
 * each K step contiguous; C is column-major with ldc elements per column. */
void tinyshogi_a64fx_sgemm_3x8(int64_t K, const float *A, const float *B,
                               float *C, int64_t ldc);

#endif
