#ifndef TINYSHOGI_A64FX_SGEMM_H
#define TINYSHOGI_A64FX_SGEMM_H

#include <stdint.h>

void tinyshogi_a64fx_sgemm_4x5(int64_t K, const float *A, const float *B,
                               float *C, int64_t ldc);

#endif
