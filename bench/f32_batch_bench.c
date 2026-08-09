#define _POSIX_C_SOURCE 200809L

#include "../src/a64fx_sgemm.h"

#include <stdint.h>
#include <math.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

static double seconds(void) {
    struct timespec t;
    clock_gettime(CLOCK_MONOTONIC, &t);
    return (double)t.tv_sec + (double)t.tv_nsec * 1.0e-9;
}

static void pack_a(const float *input, size_t batch, size_t kdim, float *packed) {
    for (size_t k = 0; k < kdim; ++k)
        for (size_t row = 0; row < 48; ++row)
            packed[k * 48U + row] = row < batch ? input[row * kdim + k] : 0.0f;
}

int main(void) {
    enum { K = 256, MMAX = 48, N = 256 };
    float *input = malloc((size_t)MMAX * K * sizeof(*input));
    float *weights = malloc((size_t)N * K * sizeof(*weights));
    float *a_pack = malloc((size_t)K * MMAX * sizeof(*a_pack));
    float *b_pack = malloc((size_t)K * N * sizeof(*b_pack));
    float *c_tile = malloc((size_t)MMAX * 8U * sizeof(*c_tile));
    float *output = malloc((size_t)MMAX * N * sizeof(*output));
    if (input == NULL || weights == NULL || a_pack == NULL || b_pack == NULL ||
        c_tile == NULL || output == NULL) return 1;
    for (size_t i = 0; i < (size_t)MMAX * K; ++i) input[i] = (float)(i % 17) * 0.01f;
    for (size_t i = 0; i < (size_t)N * K; ++i) weights[i] = (float)(i % 13) * 0.02f;
    for (size_t column = 0; column < N; column += 8U)
        for (size_t k = 0; k < K; ++k)
            for (size_t col = 0; col < 8U; ++col)
                b_pack[(column / 8U) * K * 8U + k * 8U + col] =
                    weights[(column + col) * K + k];
    pack_a(input, MMAX, K, a_pack);
    tinyshogi_a64fx_sgemm_3x8(K, a_pack, b_pack, c_tile, MMAX);
    float reference = 0.0f;
    for (size_t k = 0; k < K; ++k) reference += input[k] * weights[k];
    if (fabsf(c_tile[0] - reference) > 1.0e-3f) {
        fprintf(stderr, "FP32 tile mismatch: got %.6f ref %.6f\n", c_tile[0], reference);
        return 1;
    }
    const size_t batches[] = {1, 4, 6, 8, 12, 24, 48};
    const int reps = 1000;
    for (size_t bi = 0; bi < sizeof(batches) / sizeof(batches[0]); ++bi) {
        size_t batch = batches[bi];
        pack_a(input, batch, K, a_pack);
        double start = seconds();
        volatile double checksum = 0.0;
        for (int rep = 0; rep < reps; ++rep) {
            for (size_t column = 0; column < N; column += 8U) {
                tinyshogi_a64fx_sgemm_3x8(K, a_pack,
                                         b_pack + (column / 8U) * K * 8U,
                                         c_tile, MMAX);
                for (size_t row = 0; row < batch; ++row)
                    for (size_t col = 0; col < 8U; ++col)
                        output[row * N + column + col] = c_tile[col * MMAX + row];
            }
            checksum += output[(rep % (int)batch) * N];
        }
        double elapsed = seconds() - start;
        double flops = 2.0 * (double)reps * (double)batch * N * K;
        printf("batch=%zu sec=%.6f positions/s=%.0f GFLOP/s=%.1f checksum=%.3f\n",
               batch, elapsed, (double)reps * batch / elapsed,
               flops / elapsed / 1.0e9, checksum);
    }
    free(input); free(weights); free(a_pack); free(b_pack); free(c_tile); free(output);
    return 0;
}
