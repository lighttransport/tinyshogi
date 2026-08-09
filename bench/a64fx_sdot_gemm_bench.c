#define _POSIX_C_SOURCE 200809L

#include "../src/a64fx_sdot_gemm.h"

#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

enum { MR = 64, NR = 5 };

static double seconds(void) {
    struct timespec now;
    clock_gettime(CLOCK_MONOTONIC, &now);
    return (double)now.tv_sec + (double)now.tv_nsec * 1.0e-9;
}

static void *allocate(size_t bytes) {
    return aligned_alloc(256U, (bytes + 255U) & ~(size_t)255U);
}

static void pack_a(int8_t *dst, const int8_t *src, int K) {
    for (int step = 0; step < K / 4; ++step)
        for (int vec = 0; vec < 4; ++vec)
            for (int lane = 0; lane < 16; ++lane)
                for (int j = 0; j < 4; ++j)
                    dst[step * MR * 4 + vec * 64 + lane * 4 + j] =
                        src[(vec * 16 + lane) * K + step * 4 + j];
}

static void pack_b(int8_t *dst, const int8_t *src, int K) {
    for (int step = 0; step < K / 4; ++step)
        for (int col = 0; col < NR; ++col)
            for (int j = 0; j < 4; ++j)
                dst[step * NR * 4 + col * 4 + j] = src[col * K + step * 4 + j];
}

static int32_t ref_at(const int8_t *a, const int8_t *b, int K, int row, int col) {
    int32_t value = 0;
    for (int k = 0; k < K; ++k) value += (int32_t)a[row * K + k] * b[col * K + k];
    return value;
}

int main(int argc, char **argv) {
    int K = argc > 1 ? atoi(argv[1]) : 256;
    unsigned rounds = argc > 2 ? (unsigned)atoi(argv[2]) : 1000;
    if (K <= 0 || (K & 3)) return 2;
    int8_t *a = allocate((size_t)MR * K), *b = allocate((size_t)NR * K);
    int8_t *ap = allocate((size_t)K * MR), *bp = allocate((size_t)K * NR);
    int32_t *c = allocate((size_t)MR * NR * sizeof(*c));
    if (!a || !b || !ap || !bp || !c) return 1;
    memset(c, 0, (size_t)MR * NR * sizeof(*c));
    for (int i = 0; i < MR * K; ++i) a[i] = (int8_t)(i % 127 - 63);
    for (int i = 0; i < NR * K; ++i) b[i] = (int8_t)(i % 61 - 30);
    pack_a(ap, a, K); pack_b(bp, b, K);
    tinyshogi_a64fx_sdot_gemm_4x5(K, ap, bp, c, MR);
    int32_t max_error = 0;
    for (int col = 0; col < NR; ++col)
        for (int row = 0; row < MR; ++row) {
            int32_t error = abs(c[col * MR + row] - ref_at(a, b, K, row, col));
            if (error > max_error) max_error = error;
        }
    if (max_error != 0) {
        printf("FAIL max_error=%d\n", max_error);
        return 1;
    }
    memset(c, 0, (size_t)MR * NR * sizeof(*c));
    for (unsigned i = 0; i < 100; ++i)
        tinyshogi_a64fx_sdot_gemm_4x5(K, ap, bp, c, MR);
    double begin = seconds();
    for (unsigned i = 0; i < rounds; ++i)
        tinyshogi_a64fx_sdot_gemm_4x5(K, ap, bp, c, MR);
    double elapsed = seconds() - begin;
    double giops = 2.0 * MR * NR * K * rounds / elapsed / 1.0e9;
    printf("PASS checksum=%d rounds=%u GOPS=%.1f efficiency_2GHz=%.1f%%\n",
           c[0], rounds, giops, giops / 512.0 * 100.0);
    free(a); free(b); free(ap); free(bp); free(c);
    return 0;
}
