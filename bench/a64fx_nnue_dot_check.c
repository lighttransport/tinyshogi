#define _POSIX_C_SOURCE 200809L

#include "../src/simd.h"
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <time.h>

static double seconds(void) {
    struct timespec now;
    clock_gettime(CLOCK_MONOTONIC, &now);
    return (double)now.tv_sec + (double)now.tv_nsec * 1.0e-9;
}

int main(int argc, char **argv) {
    size_t count = argc > 1 ? strtoul(argv[1], NULL, 10) : 256U;
    unsigned rounds = argc > 2 ? (unsigned)strtoul(argv[2], NULL, 10) : 1000000U;
    if (count == 0 || (count & 255U) != 0U || rounds == 0) return 2;
    int32_t *a = aligned_alloc(256U, count * sizeof(*a));
    int16_t *b = aligned_alloc(256U, count * sizeof(*b));
    if (a == NULL || b == NULL) return 1;
    int64_t expected = 0, expected_clip = 0;
    for (size_t i = 0; i < count; ++i) {
        a[i] = (i % 37) - 18;
        b[i] = (i % 29) - 14;
        if (a[i] > 0) expected += (int64_t)a[i] * b[i];
        int32_t activation = a[i];
        if (activation < 0) activation = 0;
        if (activation > 7) activation = 7;
        expected_clip += (int64_t)activation * b[i];
    }
    int64_t got = tinyshogi_dot_relu_i32_i16(a, b, count);
    int64_t got_clip = tinyshogi_dot_clip_i32_i16(a, b, count, 7);
    if (got != expected || got_clip != expected_clip) {
        printf("FAIL relu=%lld expected=%lld clip=%lld expected_clip=%lld\n",
               (long long)got, (long long)expected,
               (long long)got_clip, (long long)expected_clip);
        free(a);
        free(b);
        return 1;
    }
    volatile int64_t checksum = 0;
    for (unsigned iteration = 0; iteration < 1000; ++iteration)
        checksum += tinyshogi_dot_clip_i32_i16(a, b, count, 7);
    double begin = seconds();
    for (unsigned iteration = 0; iteration < rounds; ++iteration)
        checksum += tinyshogi_dot_clip_i32_i16(a, b, count, 7);
    double elapsed = seconds() - begin;
    double giops = 2.0 * count * rounds / elapsed / 1.0e9;
    printf("PASS relu=%lld clip=%lld width=%zu rounds=%u ns/dot=%.1f "
           "GOPS=%.2f arithmetic_peak_efficiency_2GHz=%.2f%% checksum=%lld\n",
           (long long)got, (long long)got_clip,
           count, rounds, elapsed * 1.0e9 / rounds, giops,
           giops / 256.0 * 100.0, (long long)checksum);
    free(a);
    free(b);
    return 0;
}
