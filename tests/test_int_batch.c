#include "../src/int_model.h"

#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

static int fail(const char *message) {
    fprintf(stderr, "integer batch test failed: %s\n", message);
    return 1;
}

static int write_fixture(const char *path) {
    FILE *file = fopen(path, "wb");
    if (file == NULL) return 0;
    uint32_t metadata[4] = {1, 256, 256, 32};
    int32_t scales[4] = {65536, 256, 64, 64};
    int8_t w1[256 * 256], value[256], policy[32 * 256];
    int32_t bias[256];
    int32_t value_bias = 17;
    for (int unit = 0; unit < 256; ++unit) {
        bias[unit] = unit % 7 - 3;
        value[unit] = (int8_t)(unit % 9 - 4);
        for (int feature = 0; feature < 256; ++feature)
            w1[unit * 256 + feature] = (int8_t)((unit + feature * 3) % 11 - 5);
    }
    for (int action = 0; action < 32; ++action)
        for (int unit = 0; unit < 256; ++unit)
            policy[action * 64 + unit] = (int8_t)((action * 5 + unit) % 13 - 6);
    int ok = fwrite("TSM3", 1, 4, file) == 4 &&
             fwrite(metadata, sizeof(metadata[0]), 4, file) == 4 &&
             fwrite(scales, sizeof(scales[0]), 4, file) == 4 &&
             fwrite(w1, 1, sizeof(w1), file) == sizeof(w1) &&
             fwrite(bias, sizeof(bias[0]), 256, file) == 256 &&
             fwrite(value, 1, sizeof(value), file) == sizeof(value) &&
             fwrite(&value_bias, sizeof(value_bias), 1, file) == 1 &&
             fwrite(policy, 1, sizeof(policy), file) == sizeof(policy);
    if (fclose(file) != 0) ok = 0;
    return ok;
}

int main(void) {
    const char *path = "/tmp/tinyshogi-int-batch-tsm3.bin";
    if (!write_fixture(path)) return fail("fixture write");
    IntModel model;
    if (!int_model_load(&model, path)) return fail("model load");
    IntModelBatchWorkspace workspace;
    if (!int_model_batch_workspace_init(&workspace, &model, 48)) return fail("workspace init");
    int8_t features[48 * 256];
    int16_t batch_hidden[48 * 256], scalar_hidden[256];
    int32_t batch_logits[48 * 32], scalar_logits[32];
    int32_t batch_values[48], scalar_value;
    for (int row = 0; row < 48; ++row)
        for (int feature = 0; feature < 256; ++feature)
            features[row * 256 + feature] = (int8_t)((row * 3 + feature * 5) % 15 - 7);
    const size_t batches[] = {1, 4, 6, 8, 12, 24, 48};
    for (size_t b = 0; b < sizeof(batches) / sizeof(batches[0]); ++b) {
        size_t count = batches[b];
        memset(batch_hidden, 0, sizeof(batch_hidden));
        memset(batch_logits, 0, sizeof(batch_logits));
        memset(batch_values, 0, sizeof(batch_values));
        if (!int_model_eval_batch(&model, &workspace, features, 256, count,
                                  batch_hidden, 256, batch_logits, 32, batch_values))
            return fail("batch evaluation");
        for (size_t row = 0; row < count; ++row) {
            if (!int_model_eval(&model, features + row * 256, scalar_hidden,
                                scalar_logits, &scalar_value))
                return fail("scalar evaluation");
            if (memcmp(batch_hidden + row * 256, scalar_hidden, sizeof(scalar_hidden)) != 0 ||
                memcmp(batch_logits + row * 32, scalar_logits, sizeof(scalar_logits)) != 0 ||
                batch_values[row] != scalar_value)
                return fail("batch/scalar mismatch");
        }
    }
    int_model_batch_workspace_destroy(&workspace);
    int_model_destroy(&model);
    remove(path);
    puts("PASS integer batch evaluation");
    return 0;
}
