#ifndef TINYSHOGI_INT_MODEL_H
#define TINYSHOGI_INT_MODEL_H

#include <stdbool.h>
#include <stddef.h>
#include <stdint.h>

typedef struct {
    uint32_t feature_dim;
    uint32_t hidden_dim;
    uint32_t action_count;
    int32_t input_scale_q16;
    int32_t hidden_scale_q16;
    int32_t policy_scale_q16;
    int32_t value_scale_q16;
    int8_t *w1;
    int32_t *b1;
    int8_t *value;
    int32_t value_bias;
    int8_t *policy;
} IntModel;

bool int_model_load(IntModel *model, const char *path);
void int_model_destroy(IntModel *model);
bool int_model_eval(const IntModel *model, const int8_t *features,
                    int16_t *hidden, int32_t *policy_logits, int32_t *value_q16);
void int_model_softmax(const IntModel *model, const int32_t *logits, int32_t *probabilities);

#endif
