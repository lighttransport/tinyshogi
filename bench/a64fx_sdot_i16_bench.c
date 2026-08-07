#include "../src/a64fx_sdot_gemm.h"
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>

enum { MR = 32, NR = 5 };
int main(int argc, char **argv) {
    int K = argc > 1 ? atoi(argv[1]) : 256;
    int rounds = argc > 2 ? atoi(argv[2]) : 100;
    if (K <= 0 || (K & 3)) return 2;
    int16_t *a = malloc((size_t)MR * K * sizeof(*a));
    int16_t *b = malloc((size_t)NR * K * sizeof(*b));
    int16_t *ap = malloc((size_t)K * MR * sizeof(*ap));
    int16_t *bp = malloc((size_t)K * NR * sizeof(*bp));
    int64_t *c = calloc((size_t)MR * NR, sizeof(*c));
    if (!a || !b || !ap || !bp || !c) return 1;
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
    for (int i = 0; i < rounds; ++i)
        tinyshogi_a64fx_sdot_gemm_4x5_i16(K, ap, bp, c, MR);
    printf("PASS checksum=%lld rounds=%d\n", (long long)c[0], rounds);
    free(a); free(b); free(ap); free(bp); free(c);
    return 0;
}
