#include "int_model.h"

#include "int_math.h"
#include "simd.h"

#include <limits.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#if defined(__x86_64__) || defined(__i386__)
#include <immintrin.h>
#endif

static int32_t dot_scalar(const int8_t *left, const int8_t *right, size_t count) {
    int32_t result = 0;
    for (size_t index = 0; index < count; ++index) result += (int32_t)left[index] * (int32_t)right[index];
    return result;
}

static int32_t dot_i16_i8_scalar(const int16_t *left, const int8_t *right, size_t count) {
    int32_t result = 0;
    for (size_t index = 0; index < count; ++index) result += (int32_t)left[index] * (int32_t)right[index];
    return result;
}

#if defined(__GNUC__) && (defined(__x86_64__) || defined(__i386__))
__attribute__((target("avx2"))) static int32_t dot_avx2(const int8_t *left, const int8_t *right, size_t count) {
    __m256i accumulator = _mm256_setzero_si256();
    size_t index = 0;
    for (; index + 16 <= count; index += 16) {
        __m128i l8 = _mm_loadu_si128((const __m128i *)(left + index));
        __m128i r8 = _mm_loadu_si128((const __m128i *)(right + index));
        __m256i l16 = _mm256_cvtepi8_epi16(l8);
        __m256i r16 = _mm256_cvtepi8_epi16(r8);
        accumulator = _mm256_add_epi32(accumulator, _mm256_madd_epi16(l16, r16));
    }
    int32_t lanes[8];
    _mm256_storeu_si256((__m256i *)lanes, accumulator);
    int32_t result = 0;
    for (size_t lane = 0; lane < 8; ++lane) result += lanes[lane];
    return result + dot_scalar(left + index, right + index, count - index);
}

__attribute__((target("avx2"))) static int32_t dot_i16_i8_avx2(const int16_t *left, const int8_t *right, size_t count) {
    __m256i accumulator = _mm256_setzero_si256();
    size_t index = 0;
    for (; index + 16 <= count; index += 16) {
        __m256i l16 = _mm256_loadu_si256((const __m256i *)(left + index));
        __m128i r8 = _mm_loadu_si128((const __m128i *)(right + index));
        __m256i r16 = _mm256_cvtepi8_epi16(r8);
        accumulator = _mm256_add_epi32(accumulator, _mm256_madd_epi16(l16, r16));
    }
    int32_t lanes[8]; _mm256_storeu_si256((__m256i *)lanes, accumulator);
    int32_t result = 0;
    for (size_t lane = 0; lane < 8; ++lane) result += lanes[lane];
    return result + dot_i16_i8_scalar(left + index, right + index, count - index);
}
#endif

static int32_t dot_i8(const int8_t *left, const int8_t *right, size_t count) {
#if defined(__aarch64__)
    return tinyshogi_dot_i8_i8(left, right, count);
#else
#if defined(__GNUC__) && (defined(__x86_64__) || defined(__i386__))
    if (__builtin_cpu_supports("avx2")) return dot_avx2(left, right, count);
#endif
    return dot_scalar(left, right, count);
#endif
}

static int32_t dot_i16_i8(const int16_t *left, const int8_t *right, size_t count) {
#if defined(__aarch64__)
    return tinyshogi_dot_i16_i8(left, right, count);
#else
#if defined(__GNUC__) && (defined(__x86_64__) || defined(__i386__))
    if (__builtin_cpu_supports("avx2")) return dot_i16_i8_avx2(left, right, count);
#endif
    return dot_i16_i8_scalar(left, right, count);
#endif
}

static int16_t clamp_i16(int32_t value) {
    if (value > INT16_MAX) return INT16_MAX;
    if (value < INT16_MIN) return INT16_MIN;
    return (int16_t)value;
}

static int32_t scale_q16(int64_t value, int32_t scale) {
    int64_t scaled = (value * scale) >> 16;
    if (scaled > INT32_MAX) return INT32_MAX;
    if (scaled < INT32_MIN) return INT32_MIN;
    return (int32_t)scaled;
}

bool int_model_load(IntModel *model, const char *path) {
    if (model == NULL || path == NULL) return false;
    memset(model, 0, sizeof(*model));
    FILE *file = fopen(path, "rb");
    if (file == NULL) return false;
    char magic[4]; uint32_t metadata[4]; int32_t scales[4];
    bool ok = fread(magic, 1, 4, file) == 4 && memcmp(magic, "TSM3", 4) == 0 &&
              fread(metadata, sizeof(uint32_t), 4, file) == 4 && metadata[0] == 1 &&
              fread(scales, sizeof(int32_t), 4, file) == 4;
    if (!ok || metadata[1] == 0 || metadata[2] == 0 || metadata[3] == 0 ||
        scales[1] <= 0 || scales[2] <= 0 || scales[3] <= 0 ||
        metadata[1] > SIZE_MAX / metadata[2] ||
        (size_t)metadata[3] > SIZE_MAX / metadata[2]) {
        fclose(file); return false;
    }
    model->feature_dim = metadata[1]; model->hidden_dim = metadata[2]; model->action_count = metadata[3];
    model->input_scale_q16 = scales[0]; model->hidden_scale_q16 = scales[1];
    model->policy_scale_q16 = scales[2]; model->value_scale_q16 = scales[3];
    size_t w1_count = (size_t)model->feature_dim * model->hidden_dim;
    size_t policy_count = (size_t)model->action_count * model->hidden_dim;
    model->w1 = malloc(w1_count); model->b1 = malloc(model->hidden_dim * sizeof(int32_t));
    model->value = malloc(model->hidden_dim); model->policy = malloc(policy_count);
    ok = model->w1 != NULL && model->b1 != NULL && model->value != NULL && model->policy != NULL &&
         fread(model->w1, 1, w1_count, file) == w1_count &&
         fread(model->b1, sizeof(int32_t), model->hidden_dim, file) == model->hidden_dim &&
         fread(model->value, 1, model->hidden_dim, file) == model->hidden_dim &&
         fread(&model->value_bias, sizeof(model->value_bias), 1, file) == 1 &&
         fread(model->policy, 1, policy_count, file) == policy_count;
    fclose(file);
    if (!ok) { int_model_destroy(model); return false; }
    return true;
}

void int_model_destroy(IntModel *model) {
    if (model == NULL) return;
    free(model->w1); free(model->b1); free(model->value); free(model->policy);
    memset(model, 0, sizeof(*model));
}

bool int_model_eval(const IntModel *model, const int8_t *features,
                    int16_t *hidden, int32_t *policy_logits, int32_t *value_q16) {
    if (model == NULL || features == NULL || hidden == NULL || policy_logits == NULL || value_q16 == NULL ||
        model->w1 == NULL || model->b1 == NULL || model->policy == NULL || model->value == NULL) return false;
    for (uint32_t unit = 0; unit < model->hidden_dim; ++unit) {
        int32_t activation = scale_q16((int64_t)model->b1[unit] + dot_i8(features, model->w1 + (size_t)unit * model->feature_dim, model->feature_dim), model->hidden_scale_q16);
        hidden[unit] = clamp_i16(activation > 0 ? activation : 0);
    }
    for (uint32_t action = 0; action < model->action_count; ++action) {
        policy_logits[action] = scale_q16(dot_i16_i8(hidden, model->policy + (size_t)action * model->hidden_dim, model->hidden_dim), model->policy_scale_q16);
    }
    int32_t value = model->value_bias + scale_q16(dot_i16_i8(hidden, model->value, model->hidden_dim), model->value_scale_q16);
    *value_q16 = int_tanh_q16(value);
    return true;
}

void int_model_softmax(const IntModel *model, const int32_t *logits, int32_t *probabilities) {
    if (model == NULL) return;
    int_softmax_q16(logits, probabilities, model->action_count);
}
