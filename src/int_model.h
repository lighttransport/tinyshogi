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
    int16_t *value_i16;
    int16_t *policy_i16;
    int8_t *w1_gemm_i8;
    uint32_t w1_gemm_hidden_dim;
} IntModel;

typedef struct {
    size_t capacity;
    size_t feature_dim;
    size_t hidden_dim;
    size_t action_count;
    int8_t *features_panel;
    int32_t *hidden_gemm;
} IntModelBatchWorkspace;

bool int_model_load(IntModel *model, const char *path);
void int_model_destroy(IntModel *model);
bool int_model_eval(const IntModel *model, const int8_t *features,
                    int16_t *hidden, int32_t *policy_logits, int32_t *value_q16);
bool int_model_batch_workspace_init(IntModelBatchWorkspace *workspace,
                                    const IntModel *model, size_t capacity);
void int_model_batch_workspace_destroy(IntModelBatchWorkspace *workspace);
bool int_model_eval_batch(const IntModel *model, IntModelBatchWorkspace *workspace,
                          const int8_t *features, size_t feature_stride,
                          size_t batch_count, int16_t *hidden, size_t hidden_stride,
                          int32_t *policy_logits, size_t policy_stride,
                          int32_t *value_q16);
void int_model_softmax(const IntModel *model, const int32_t *logits, int32_t *probabilities);

#endif
