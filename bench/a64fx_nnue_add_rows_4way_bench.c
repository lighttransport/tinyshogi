#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>

void tinyshogi_nnue_add_i16_i32_rows_sve_4way(int32_t *, const int16_t *const *,
                                               size_t, size_t, int);

int main(int ac, char **av) {
    enum { N = 256, R = 54 };
    int rounds = ac > 1 ? atoi(av[1]) : 10;
    int sign = ac > 2 ? atoi(av[2]) : 1;
    int row_count = ac > 3 ? atoi(av[3]) : R;
    if (row_count < 1 || row_count > R) return 2;
    int32_t a[N], ref[N];
    int16_t w[R][N];
    const int16_t *rows[R];
    for (int r = 0; r < R; ++r) rows[r] = w[r];
    for (int i = 0; i < N; ++i) {
        a[i] = i - 128;
        ref[i] = a[i];
        for (int r = 0; r < row_count; ++r) {
            w[r][i] = (int16_t)(r * 17 + i % 11 - 5);
            ref[i] += sign > 0 ? w[r][i] : -w[r][i];
        }
    }
    tinyshogi_nnue_add_i16_i32_rows_sve_4way(a, rows, row_count, N, sign);
    for (int i = 0; i < N; ++i)
        if (a[i] != ref[i]) {
            printf("FAIL i=%d got=%d ref=%d\n", i, a[i], ref[i]);
            return 1;
        }
    for (int round = 1; round < rounds; ++round)
        tinyshogi_nnue_add_i16_i32_rows_sve_4way(a, rows, row_count, N, sign);
    printf("PASS 4way %d rounds=%d sign=%d\n", a[0], rounds, sign);
    return 0;
}
