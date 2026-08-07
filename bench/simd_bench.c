#define _POSIX_C_SOURCE 200809L

#include "../src/simd.h"

#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <time.h>

static uint64_t now_ns(void) {
    struct timespec t;
    clock_gettime(CLOCK_MONOTONIC, &t);
    return (uint64_t)t.tv_sec * UINT64_C(1000000000) + (uint64_t)t.tv_nsec;
}

int main(int argc, char **argv) {
    size_t width = argc > 1 ? (size_t)strtoul(argv[1], NULL, 10) : 1024;
    unsigned rounds = argc > 2 ? (unsigned)strtoul(argv[2], NULL, 10) : 100000;
    int8_t *a = malloc(width), *b = malloc(width);
    int16_t *c = malloc(width * sizeof(*c));
    int32_t *d = malloc(width * sizeof(*d));
    if (!a || !b || !c || !d) return 1;
    for (size_t i = 0; i < width; ++i) { a[i] = (int8_t)(i % 17 - 8); b[i] = (int8_t)(i % 13 - 6); c[i] = (int16_t)(i % 101 - 50); }
    for (size_t i = 0; i < width; ++i) d[i] = (int32_t)(i % 101) - 50;
    int32_t result = 0;
    uint64_t start = now_ns();
    for (unsigned i = 0; i < rounds; ++i) result += tinyshogi_dot_i8_i8(a, b, width);
    uint64_t elapsed = now_ns() - start;
    double ops = (double)width * rounds * 2.0;
    printf("backend=%s kernel=i8_i8 width=%zu rounds=%u checksum=%d ns=%llu ops_per_sec=%.3f\n",
           tinyshogi_simd_backend(), width, rounds, result,
           (unsigned long long)elapsed, elapsed ? ops * 1e9 / elapsed : 0.0);
    start = now_ns(); result = 0;
    for (unsigned i = 0; i < rounds; ++i) result += tinyshogi_dot_i16_i8(c, b, width);
    elapsed = now_ns() - start;
    printf("backend=%s kernel=i16_i8 width=%zu rounds=%u checksum=%d ns=%llu ops_per_sec=%.3f\n",
           tinyshogi_simd_backend(), width, rounds, result,
           (unsigned long long)elapsed, elapsed ? ops * 1e9 / elapsed : 0.0);
    int64_t wide_result = 0;
    start = now_ns();
    for (unsigned i = 0; i < rounds; ++i)
        wide_result += tinyshogi_dot_relu_i32_i16(d, c, width);
    elapsed = now_ns() - start;
    printf("backend=%s kernel=relu_i32_i16 width=%zu rounds=%u checksum=%lld ns=%llu ops_per_sec=%.3f\n",
           tinyshogi_simd_backend(), width, rounds, (long long)wide_result,
           (unsigned long long)elapsed, elapsed ? ops * 1e9 / elapsed : 0.0);
    free(a); free(b); free(c); free(d);
    return 0;
}
