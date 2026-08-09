#define _POSIX_C_SOURCE 200809L

#include "../src/a64fx_sdot_gemm.h"
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

enum { MR = 32, NR = 5 };
static double seconds(void) { struct timespec t; clock_gettime(CLOCK_MONOTONIC,&t); return (double)t.tv_sec+(double)t.tv_nsec*1e-9; }
static void *allocate(size_t bytes) { return aligned_alloc(256U,(bytes+255U)&~(size_t)255U); }
int main(int argc, char **argv) {
    int K = argc > 1 ? atoi(argv[1]) : 256;
    int rounds = argc > 2 ? atoi(argv[2]) : 100;
    if (K <= 0 || (K & 3)) return 2;
    int16_t *a = allocate((size_t)MR * K * sizeof(*a));
    int16_t *b = allocate((size_t)NR * K * sizeof(*b));
    int16_t *ap = allocate((size_t)K * MR * sizeof(*ap));
    int16_t *bp = allocate((size_t)K * NR * sizeof(*bp));
    int64_t *c = allocate((size_t)MR * NR * sizeof(*c));
    if (!a || !b || !ap || !bp || !c) return 1;
    memset(c,0,(size_t)MR*NR*sizeof(*c));
    for (int i = 0; i < MR * K; ++i) a[i] = (int16_t)(i % 31 - 15);
    for (int i = 0; i < NR * K; ++i) b[i] = (int16_t)(i % 19 - 9);
    for (int step = 0; step < K / 4; ++step)
        for (int v = 0; v < 4; ++v)
            for (int lane = 0; lane < 8; ++lane)
                for (int j = 0; j < 4; ++j)
                    ap[step * MR * 4 + v * 32 + lane * 4 + j] =
                        a[(v * 8 + lane) * K + step * 4 + j];
    for (int step = 0; step < K / 4; ++step)
        for (int col = 0; col < NR; ++col)
            for (int j = 0; j < 4; ++j)
                bp[step * NR * 4 + col * 4 + j] = b[col * K + step * 4 + j];
    tinyshogi_a64fx_sdot_gemm_4x5_i16(K, ap, bp, c, MR);
    int64_t ref = 0;
    for (int k = 0; k < K; ++k) ref += (int64_t)a[k] * b[k];
    if (c[0] != ref) { printf("FAIL got=%lld ref=%lld\n", (long long)c[0], (long long)ref); return 1; }
    for (int i = 0; i < 100; ++i)
        tinyshogi_a64fx_sdot_gemm_4x5_i16(K, ap, bp, c, MR);
    double begin = seconds();
    for (int i = 0; i < rounds; ++i)
        tinyshogi_a64fx_sdot_gemm_4x5_i16(K, ap, bp, c, MR);
    double elapsed = seconds()-begin;
    double giops=2.0*MR*NR*K*rounds/elapsed/1.0e9;
    printf("PASS checksum=%lld rounds=%d GOPS=%.1f efficiency_2GHz=%.1f%%\n", (long long)c[0], rounds,giops,giops/256.0*100.0);
    free(a); free(b); free(ap); free(bp); free(c);
    return 0;
}
