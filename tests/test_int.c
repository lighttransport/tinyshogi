#include "../src/int_math.h"
#include "../src/int_model.h"

#include <stdio.h>
#include <limits.h>

static int fail(const char *message) {
    fprintf(stderr, "integer test failed: %s\n", message);
    return 1;
}

int main(void) {
    int32_t extreme_logits[3] = {INT32_MAX, INT32_MIN, 0};
    int32_t extreme_probabilities[3];
    int_softmax_q16(extreme_logits, extreme_probabilities, 3);
    if (extreme_probabilities[0] < 65500 || extreme_probabilities[1] != 0) return fail("softmax extreme range");
    int32_t one = int_exp_q16(0);
    if (one < 65530 || one > 65542) return fail("exp(0)");
    int32_t log_one = int_log_q16(INT_Q16_ONE);
    if (log_one < -8 || log_one > 8) return fail("log(1)");
    int32_t exp_half = int_exp_q16(INT_Q16_ONE / 2);
    if (exp_half <= INT_Q16_ONE) return fail("exp monotonicity");
    int32_t tanh = int_tanh_q16(INT_Q16_ONE);
    if (tanh < 49000 || tanh > 51000) return fail("tanh(1)");
    int32_t logits[3] = {0, INT_Q16_ONE, -INT_Q16_ONE};
    int32_t probabilities[3];
    int_softmax_q16(logits, probabilities, 3);
    if (probabilities[1] <= probabilities[0] || probabilities[0] <= probabilities[2]) return fail("softmax ordering");
    if (probabilities[0] + probabilities[1] + probabilities[2] < 65530 ||
        probabilities[0] + probabilities[1] + probabilities[2] > 65542) return fail("softmax sum");
    const char *path = "/tmp/tinyshogi-test-tsm3.bin";
    FILE *model_file = fopen(path, "wb");
    if (model_file == NULL) return fail("model fixture create");
    fwrite("TSM3", 1, 4, model_file);
    uint32_t metadata[4] = {1, 4, 2, 3};
    int32_t scales[4] = {65536, 256, 64, 64};
    int8_t w1[8] = {1, 0, 0, 1, -1, 0, 0, -1};
    int32_t b1[2] = {0, 0};
    int8_t value[2] = {1, 1};
    int32_t value_bias = 0;
    int8_t policy[6] = {1, 0, 0, 1, -1, 0};
    fwrite(metadata, sizeof(metadata[0]), 4, model_file);
    fwrite(scales, sizeof(scales[0]), 4, model_file);
    fwrite(w1, sizeof(w1[0]), 8, model_file);
    fwrite(b1, sizeof(b1[0]), 2, model_file);
    fwrite(value, sizeof(value[0]), 2, model_file);
    fwrite(&value_bias, sizeof(value_bias), 1, model_file);
    fwrite(policy, sizeof(policy[0]), 6, model_file);
    fclose(model_file);
    IntModel model;
    if (!int_model_load(&model, path)) return fail("model load");
    int8_t features[4] = {1, 2, 3, 4};
    int16_t hidden[2]; int32_t model_logits[3]; int32_t model_value;
    if (!int_model_eval(&model, features, hidden, model_logits, &model_value)) return fail("model eval");
    int32_t model_probabilities[3]; int_model_softmax(&model, model_logits, model_probabilities);
    if (model_probabilities[0] + model_probabilities[1] + model_probabilities[2] < 65530 ||
        model_probabilities[0] + model_probabilities[1] + model_probabilities[2] > 65542) return fail("model softmax sum");
    int16_t hidden_repeat[2]; int32_t logits_repeat[3]; int32_t value_repeat;
    if (!int_model_eval(&model, features, hidden_repeat, logits_repeat, &value_repeat) ||
        hidden[0] != hidden_repeat[0] || hidden[1] != hidden_repeat[1] ||
        model_value != value_repeat || logits_repeat[0] != model_logits[0] ||
        logits_repeat[1] != model_logits[1] || logits_repeat[2] != model_logits[2]) return fail("model determinism");
    int_model_destroy(&model);
    remove(path);
    return 0;
}
