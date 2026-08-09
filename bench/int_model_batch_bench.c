#define _POSIX_C_SOURCE 200809L

#include "../src/int_model.h"

#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

static double seconds(void) {
    struct timespec t;
    clock_gettime(CLOCK_MONOTONIC, &t);
    return (double)t.tv_sec + (double)t.tv_nsec * 1.0e-9;
}

static int write_model(const char *path) {
    FILE *file = fopen(path, "wb");
    if (file == NULL) return 0;
    uint32_t metadata[4] = {1, 256, 256, 32};
    int32_t scales[4] = {65536, 256, 64, 64};
    int8_t *w1 = malloc(256U * 256U), *value = malloc(256U), *policy = malloc(32U * 256U);
    int32_t *bias = calloc(256U, sizeof(*bias));
    int32_t value_bias = 0;
    if (w1 == NULL || value == NULL || policy == NULL || bias == NULL) return 0;
    for (int unit = 0; unit < 256; ++unit) {
        value[unit] = (int8_t)(unit % 7 - 3);
        for (int feature = 0; feature < 256; ++feature)
            w1[unit * 256 + feature] = (int8_t)((unit + feature) % 5 - 2);
    }
    for (int i = 0; i < 32 * 256; ++i) policy[i] = (int8_t)(i % 11 - 5);
    int ok = fwrite("TSM3", 1, 4, file) == 4 &&
             fwrite(metadata, sizeof(metadata[0]), 4, file) == 4 &&
             fwrite(scales, sizeof(scales[0]), 4, file) == 4 &&
             fwrite(w1, 1, 256U * 256U, file) == 256U * 256U &&
             fwrite(bias, sizeof(bias[0]), 256, file) == 256 &&
             fwrite(value, 1, 256, file) == 256 &&
             fwrite(&value_bias, sizeof(value_bias), 1, file) == 1 &&
             fwrite(policy, 1, 32U * 256U, file) == 32U * 256U;
    if (fclose(file) != 0) ok = 0;
    free(w1); free(value); free(policy); free(bias);
    return ok;
}

int main(void) {
    setbuf(stdout, NULL);
    const char *path = "/tmp/tinyshogi-int-batch-bench-tsm3.bin";
    if (!write_model(path)) return 1;
    IntModel model;
    if (!int_model_load(&model, path)) return 1;
    IntModelBatchWorkspace workspace;
    if (!int_model_batch_workspace_init(&workspace, &model, 48)) return 1;
    int8_t *features_storage = malloc(48U * 256U + 128U);
    int16_t *hidden_storage = malloc(48U * 256U * sizeof(int16_t) + 128U);
    int32_t *logits_storage = malloc(48U * 32U * sizeof(int32_t) + 128U);
    int32_t *values_storage = malloc(48U * sizeof(int32_t) + 128U);
    int8_t *features = features_storage != NULL ? features_storage + 64 : NULL;
    int16_t *hidden = hidden_storage != NULL ? (int16_t *)((char *)hidden_storage + 64) : NULL;
    int32_t *logits = logits_storage != NULL ? (int32_t *)((char *)logits_storage + 64) : NULL;
    int32_t *values = values_storage != NULL ? (int32_t *)((char *)values_storage + 64) : NULL;
    if (features == NULL || hidden == NULL || logits == NULL || values == NULL) return 1;
    for (int i = 0; i < 48 * 256; ++i) features[i] = (int8_t)(i % 17 - 8);
    const size_t batches[] = {1, 4, 6, 8, 12, 24, 48};
    const int reps = 10000;
    for (size_t bi = 0; bi < sizeof(batches) / sizeof(batches[0]); ++bi) {
        size_t batch = batches[bi];
        volatile int64_t checksum = 0;
        for (int i = 0; i < 100; ++i)
            int_model_eval_batch(&model, &workspace, features, 256, batch,
                                 hidden, 256, logits, 32, values);
        double start = seconds();
        for (int i = 0; i < reps; ++i) {
            int_model_eval_batch(&model, &workspace, features, 256, batch,
                                 hidden, 256, logits, 32, values);
            checksum += logits[(i % (int)batch) * 32] + values[i % (int)batch];
        }
        double elapsed = seconds() - start;
        double positions = (double)reps * (double)batch;
        printf("batch=%zu evals=%d sec=%.6f positions/s=%.0f us/position=%.3f checksum=%lld\n",
               batch, reps, elapsed, positions / elapsed,
               elapsed * 1.0e6 / positions, (long long)checksum);
    }
    free(features_storage); free(hidden_storage); free(logits_storage); free(values_storage);
    int_model_batch_workspace_destroy(&workspace);
    int_model_destroy(&model);
    remove(path);
    return 0;
}
