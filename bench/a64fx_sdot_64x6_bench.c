#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

enum { M = 64, N = 6 };
extern void tinyshogi_a64fx_sdot_gemm_64x6(size_t, const int8_t *,
                                           const int8_t *, int32_t *, size_t);

static void *allocate(size_t bytes) {
    return aligned_alloc(256U, (bytes + 255U) & ~(size_t)255U);
}

static int32_t reference(const int8_t *a, const int8_t *b, int k,
                         int row, int column) {
    int32_t sum = 0;
    for (int index = 0; index < k; ++index)
        sum += (int32_t)a[row * k + index] * b[column * k + index];
    return sum;
}

int main(int argc, char **argv) {
    int k = argc > 1 ? atoi(argv[1]) : 256;
    int rounds = argc > 2 ? atoi(argv[2]) : 10000;
    if (k <= 0 || (k & 3) != 0 || rounds <= 0) return 2;
    int8_t *a = allocate((size_t)M * k), *b = allocate((size_t)N * k);
    int8_t *packed_a = allocate((size_t)M * k);
    int8_t *packed_b = allocate((size_t)N * k);
    int32_t *c = allocate((size_t)M * N * sizeof(*c));
    if (a == NULL || b == NULL || packed_a == NULL || packed_b == NULL || c == NULL)
        return 1;
    for (int i = 0; i < M * k; ++i) a[i] = (int8_t)(i % 127 - 63);
    for (int i = 0; i < N * k; ++i) b[i] = (int8_t)(i % 61 - 30);
    for (int block = 0; block < k / 4; ++block) {
        for (int row = 0; row < M; ++row)
            for (int lane = 0; lane < 4; ++lane)
                packed_a[block * 256 + row * 4 + lane] =
                    a[row * k + block * 4 + lane];
        for (int column = 0; column < N; ++column)
            for (int lane = 0; lane < 4; ++lane)
                packed_b[block * 24 + column * 4 + lane] =
                    b[column * k + block * 4 + lane];
    }
    memset(c, 0, (size_t)M * N * sizeof(*c));
    tinyshogi_a64fx_sdot_gemm_64x6(k, packed_a, packed_b, c, M);
    for (int column = 0; column < N; ++column)
        for (int row = 0; row < M; ++row)
            if (c[column * M + row] != reference(a, b, k, row, column)) {
                fprintf(stderr, "mismatch row=%d column=%d\n", row, column);
                return 1;
            }
    for (int iteration = 0; iteration < rounds; ++iteration)
        tinyshogi_a64fx_sdot_gemm_64x6(k, packed_a, packed_b, c, M);
    printf("PASS checksum=%d rounds=%d\n", c[0], rounds);
    free(a); free(b); free(packed_a); free(packed_b); free(c);
    return 0;
}
