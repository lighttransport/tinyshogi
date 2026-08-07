#include "../src/simd.h"
#include <stdint.h>
#include <stdio.h>

int main(void) {
    enum { N = 4096 };
    static int32_t a[N];
    static int16_t b[N];
    int64_t expected = 0;
    for (int i = 0; i < N; ++i) {
        a[i] = (i % 37) - 18;
        b[i] = (i % 29) - 14;
        if (a[i] > 0) expected += (int64_t)a[i] * b[i];
    }
    int64_t got = tinyshogi_dot_relu_i32_i16(a, b, N);
    printf("got=%lld expected=%lld\n", (long long)got, (long long)expected);
    return got == expected ? 0 : 1;
}
