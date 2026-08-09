#include "../src/a64fx_uct.h"

#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>

static uint32_t next_random(uint32_t *state) {
    *state = *state * 1664525U + 1013904223U;
    return *state;
}

static size_t scalar_argmax(const float *mean, const float *inverse, size_t count,
                            float scale, int maximizing) {
    size_t best = SIZE_MAX;
    float best_score = -INFINITY;
    for (size_t index = 0; index < count; ++index) {
        float value = maximizing ? mean[index] : 1.0f - mean[index];
        float score = fmaf(scale, inverse[index], value);
        if (score > best_score) {
            best_score = score;
            best = index;
        }
    }
    return best;
}

int main(void) {
    _Alignas(64) float mean[600], inverse[600];
    uint32_t random_state = 7U;
    for (size_t count = 1; count <= 600; ++count) {
        for (size_t index = 0; index < count; ++index) {
            mean[index] = (float)(next_random(&random_state) & 0xffffU) / 65535.0f;
            inverse[index] = 0.01f + (float)(next_random(&random_state) & 0xffffU) / 65535.0f;
        }
        if (count >= 3) mean[1] = mean[2] = 0.75f;
        for (int maximizing = 0; maximizing <= 1; ++maximizing) {
            float scale = 0.125f + (float)(count % 17U) * 0.0625f;
            size_t expected = scalar_argmax(mean, inverse, count, scale, maximizing);
            size_t actual = tinyshogi_a64fx_uct_argmax(mean, inverse, count, scale,
                                                       maximizing != 0);
            if (actual != expected) {
                fprintf(stderr, "UCT mismatch count=%zu maximizing=%d expected=%zu actual=%zu\n",
                        count, maximizing, expected, actual);
                return 1;
            }
        }
    }
    puts("PASS A64FX SVE UCT argmax");
    return 0;
}
