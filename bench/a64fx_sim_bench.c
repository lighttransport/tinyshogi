#include "../src/simd.h"

#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>

int main(int argc, char **argv) {
    int kernel = argc > 1 ? atoi(argv[1]) : 1;
    size_t width = argc > 2 ? (size_t)strtoul(argv[2], NULL, 10) : 4096;
    unsigned rounds = argc > 3 ? (unsigned)strtoul(argv[3], NULL, 10) : 1000;
    int8_t *a8 = malloc(width), *b8 = malloc(width);
    int16_t *a16 = malloc(width * sizeof(*a16));
    int32_t *a32 = malloc(width * sizeof(*a32));
    if (!a8 || !b8 || !a16 || !a32) return 1;
    for (size_t i = 0; i < width; ++i) {
        a8[i] = (int8_t)(i % 17 - 8);
        b8[i] = (int8_t)(i % 13 - 6);
        a16[i] = (int16_t)(i % 101 - 50);
        a32[i] = (int32_t)(i % 101) - 50;
    }
    int64_t total = 0;
    for (unsigned i = 0; i < rounds; ++i) {
        if (kernel == 1) total += tinyshogi_dot_i8_i8(a8, b8, width);
        else if (kernel == 2) total += tinyshogi_dot_i16_i8(a16, b8, width);
        else total += tinyshogi_dot_relu_i32_i16(a32, a16, width);
    }
    printf("%lld\n", (long long)total);
    free(a8); free(b8); free(a16); free(a32);
    return 0;
}
