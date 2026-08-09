#define _POSIX_C_SOURCE 200809L

#include "../src/a64fx_sdot_gemm.h"

#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

enum { M = 5, N = 32 };

static void *allocate(size_t size) {
    return aligned_alloc(256U, (size + 255U) & ~(size_t)255U);
}

static double seconds(void) {
    struct timespec value;
    clock_gettime(CLOCK_MONOTONIC, &value);
    return (double)value.tv_sec + (double)value.tv_nsec * 1.0e-9;
}

static int64_t reference(const int16_t *a, const int16_t *b,
                         int k, int row, int column) {
    int64_t sum = 0;
    for (int index = 0; index < k; ++index)
        sum += (int64_t)a[row * k + index] * b[index * N + column];
    return sum;
}

int main(int argc, char **argv) {
    int k = argc > 1 ? atoi(argv[1]) : 256;
    int rounds = argc > 2 ? atoi(argv[2]) : 100000;
    if (k <= 0 || (k & 3) != 0 || rounds <= 0) return 2;
    int16_t *a = allocate((size_t)M * k * sizeof(*a));
    int16_t *b = allocate((size_t)k * N * sizeof(*b));
    int16_t *packed_a = allocate((size_t)k * M * sizeof(*packed_a));
    int16_t *packed_b = allocate((size_t)k * N * sizeof(*packed_b));
    int64_t *c = allocate((size_t)M * N * sizeof(*c));
    if (a == NULL || b == NULL || packed_a == NULL || packed_b == NULL || c == NULL)
        return 1;
    for (int index = 0; index < M * k; ++index) a[index] = (int16_t)(index % 31 - 15);
    for (int index = 0; index < k * N; ++index) b[index] = (int16_t)(index % 19 - 9);
    for (int step = 0; step < k / 4; ++step)
        for (int row = 0; row < M; ++row)
            for (int lane = 0; lane < 4; ++lane)
                packed_a[step * 20 + row * 4 + lane] = a[row * k + step * 4 + lane];
    for (int step = 0; step < k / 4; ++step)
        for (int vector = 0; vector < 4; ++vector)
            for (int lane = 0; lane < 8; ++lane)
                for (int item = 0; item < 4; ++item)
                    packed_b[step * 128 + vector * 32 + lane * 4 + item] =
                        b[(step * 4 + item) * N + vector * 8 + lane];
    tinyshogi_a64fx_sdot_gemm_5x4_i16(k, packed_a, packed_b, c, N);
    for (int row = 0; row < M; ++row)
        for (int column = 0; column < N; ++column)
            if (c[row * N + column] != reference(a, b, k, row, column)) return 1;
    for (int index = 0; index < 100; ++index)
        tinyshogi_a64fx_sdot_gemm_5x4_i16(k, packed_a, packed_b, c, N);
    double begin = seconds();
    for (int index = 0; index < rounds; ++index)
        tinyshogi_a64fx_sdot_gemm_5x4_i16(k, packed_a, packed_b, c, N);
    double elapsed = seconds() - begin;
    double giops = 2.0 * M * N * k * rounds / elapsed / 1.0e9;
    printf("PASS checksum=%lld rounds=%d GOPS=%.1f efficiency_2GHz=%.1f%%\n",
           (long long)c[0], rounds, giops, giops / 256.0 * 100.0);
    free(a); free(b); free(packed_a); free(packed_b); free(c);
    return 0;
}
