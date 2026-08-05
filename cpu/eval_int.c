#include "../src/int_model.h"

#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

static int8_t quantize_feature(float raw) {
    float scaled = raw * 127.0f;
    int value = (int)(scaled >= 0.0f ? scaled + 0.5f : scaled - 0.5f);
    return value > 127 ? 127 : value < -127 ? -127 : (int8_t)value;
}

int main(int argc, char **argv) {
    if (argc != 3) {
        fprintf(stderr, "usage: %s model.tsm3 features.tfe\n", argv[0]);
        return 2;
    }
    IntModel model;
    if (!int_model_load(&model, argv[1])) {
        fprintf(stderr, "cannot load TSM3 model\n");
        return 1;
    }
    FILE *file = fopen(argv[2], "rb");
    uint32_t header[4];
    if (!file || fread(header, sizeof(header[0]), 4, file) != 4 ||
        memcmp(header, "TFE1", 4) != 0 || header[1] != 1 || header[3] * 81U != model.feature_dim) {
        fprintf(stderr, "invalid TFE1 or feature dimension\n");
        if (file) fclose(file);
        int_model_destroy(&model);
        return 1;
    }
    size_t count = header[2];
    float *raw = malloc(count * model.feature_dim * sizeof(*raw));
    int8_t *features = malloc(count * model.feature_dim);
    int16_t *hidden = malloc(model.hidden_dim * sizeof(*hidden));
    int32_t *logits = malloc(model.action_count * sizeof(*logits));
    int32_t *probabilities = malloc(model.action_count * sizeof(*probabilities));
    if (!raw || !features || !hidden || !logits || !probabilities ||
        fread(raw, sizeof(*raw), count * model.feature_dim, file) != count * model.feature_dim) {
        fprintf(stderr, "short TFE1 input\n");
        free(raw); free(features); free(hidden); free(logits); free(probabilities);
        fclose(file); int_model_destroy(&model); return 1;
    }
    fclose(file);
    uint64_t checksum = UINT64_C(1469598103934665603);
    for (size_t sample = 0; sample < count; ++sample) {
        for (uint32_t index = 0; index < model.feature_dim; ++index)
            features[sample * model.feature_dim + index] = quantize_feature(raw[sample * model.feature_dim + index]);
        int32_t value;
        if (!int_model_eval(&model, features + sample * model.feature_dim, hidden, logits, &value)) return 1;
        int_model_softmax(&model, logits, probabilities);
        uint32_t best = 0;
        for (uint32_t action = 1; action < model.action_count; ++action)
            if (probabilities[action] > probabilities[best]) best = action;
        checksum ^= (uint32_t)value; checksum *= UINT64_C(1099511628211);
        checksum ^= best; checksum *= UINT64_C(1099511628211);
        printf("sample=%zu value_q16=%d best_action=%u probability_q16=%d\n",
               sample, value, best, probabilities[best]);
    }
    printf("checksum=%016llx\n", (unsigned long long)checksum);
    free(raw); free(features); free(hidden); free(logits); free(probabilities);
    int_model_destroy(&model);
    return 0;
}
