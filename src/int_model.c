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

#if defined(__GNUC__) || defined(__FUJITSU)
#define TS_MAYBE_UNUSED __attribute__((unused))
#else
#define TS_MAYBE_UNUSED
#endif

static TS_MAYBE_UNUSED int32_t dot_scalar(const int8_t *left, const int8_t *right,
                                          size_t count) {
    int32_t result = 0;
    for (size_t index = 0; index < count; ++index) result += (int32_t)left[index] * (int32_t)right[index];
    return result;
}

static TS_MAYBE_UNUSED int32_t dot_i16_i8_scalar(const int16_t *left,
                                                 const int8_t *right,
                                                 size_t count) {
    int32_t result = 0;
    for (size_t index = 0; index < count; ++index) result += (int32_t)left[index] * (int32_t)right[index];
    return result;
}

static TS_MAYBE_UNUSED int64_t dot_i16_i16_scalar(const int16_t *left,
                                                  const int16_t *right,
                                                  size_t count) {
    int64_t result = 0;
    for (size_t index = 0; index < count; ++index)
        result += (int64_t)left[index] * (int64_t)right[index];
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

static uint32_t round_up_u32(uint32_t value, uint32_t multiple) {
    return (value + multiple - 1U) / multiple * multiple;
}

static void *aligned_calloc_256(size_t count, size_t element_size) {
    if (element_size != 0 && count > SIZE_MAX / element_size) return NULL;
    size_t bytes = count * element_size;
    size_t allocated = (bytes + 255U) & ~(size_t)255U;
    void *memory = aligned_alloc(256U, allocated);
    if (memory != NULL) memset(memory, 0, allocated);
    return memory;
}

static void int_model_build_gemm_caches(IntModel *model) {
    if (model == NULL || model->feature_dim == 0 || model->hidden_dim == 0 ||
        model->action_count == 0) return;
    model->w1_gemm_hidden_dim = round_up_u32(model->hidden_dim, 64U);
    if ((model->feature_dim & 3U) == 0U) {
        size_t count = (size_t)model->feature_dim * model->w1_gemm_hidden_dim;
        model->w1_gemm_i8 = aligned_calloc_256(count, sizeof(*model->w1_gemm_i8));
        if (model->w1_gemm_i8 != NULL) {
            for (uint32_t output_panel = 0; output_panel < model->w1_gemm_hidden_dim; output_panel += 64U)
                for (uint32_t block = 0; block < model->feature_dim; block += 4U) {
                    int8_t *panel = model->w1_gemm_i8 +
                        (size_t)(output_panel / 64U) * model->feature_dim * 64U +
                        (size_t)(block / 4U) * 256U;
                    for (uint32_t output = 0; output < 64U; ++output)
                        for (uint32_t lane = 0; lane < 4U; ++lane)
                            if (output_panel + output < model->hidden_dim)
                                panel[output * 4U + lane] = model->w1[
                                    (size_t)(output_panel + output) * model->feature_dim + block + lane];
                }
        }
    }
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
    model->value_i16 = malloc((size_t)model->hidden_dim * sizeof(int16_t));
    model->policy_i16 = malloc((size_t)model->action_count * model->hidden_dim * sizeof(int16_t));
    ok = model->w1 != NULL && model->b1 != NULL && model->value != NULL && model->policy != NULL &&
         model->value_i16 != NULL && model->policy_i16 != NULL &&
         fread(model->w1, 1, w1_count, file) == w1_count &&
         fread(model->b1, sizeof(int32_t), model->hidden_dim, file) == model->hidden_dim &&
         fread(model->value, 1, model->hidden_dim, file) == model->hidden_dim &&
         fread(&model->value_bias, sizeof(model->value_bias), 1, file) == 1 &&
         fread(model->policy, 1, policy_count, file) == policy_count;
    fclose(file);
    if (!ok) { int_model_destroy(model); return false; }
    for (uint32_t i = 0; i < model->hidden_dim; ++i)
        model->value_i16[i] = model->value[i];
    for (size_t i = 0; i < policy_count; ++i)
        model->policy_i16[i] = model->policy[i];
    int_model_build_gemm_caches(model);
    return true;
}

void int_model_destroy(IntModel *model) {
    if (model == NULL) return;
    free(model->w1); free(model->b1); free(model->value); free(model->policy);
    free(model->value_i16); free(model->policy_i16);
    free(model->w1_gemm_i8);
    memset(model, 0, sizeof(*model));
}

bool int_model_eval(const IntModel *model, const int8_t *features,
                    int16_t *hidden, int32_t *policy_logits, int32_t *value_q16) {
    if (model == NULL || features == NULL || hidden == NULL || policy_logits == NULL || value_q16 == NULL ||
        model->w1 == NULL || model->b1 == NULL || model->policy == NULL || model->value == NULL) return false;
    uint32_t unit = 0;
    for (; unit + 8U <= model->hidden_dim; unit += 8U) {
        int32_t dots[8];
        tinyshogi_dot_i8_i8_8(features, model->w1 + (size_t)unit * model->feature_dim,
                              model->feature_dim, model->feature_dim, dots);
        for (unsigned lane = 0; lane < 8; ++lane) {
            int32_t activation = scale_q16((int64_t)model->b1[unit + lane] + dots[lane],
                                           model->hidden_scale_q16);
            hidden[unit + lane] = clamp_i16(activation > 0 ? activation : 0);
        }
    }
    for (; unit < model->hidden_dim; ++unit) {
        int32_t activation = scale_q16((int64_t)model->b1[unit] + dot_i8(features, model->w1 + (size_t)unit * model->feature_dim, model->feature_dim), model->hidden_scale_q16);
        hidden[unit] = clamp_i16(activation > 0 ? activation : 0);
    }
    uint32_t action = 0;
    for (; action + 8U <= model->action_count; action += 8U) {
        int64_t dots[8];
        if (model->policy_i16 != NULL)
            tinyshogi_dot_i16_i16_8(hidden, model->policy_i16 + (size_t)action * model->hidden_dim,
                                    model->hidden_dim, model->hidden_dim, dots);
        else {
            for (unsigned lane = 0; lane < 8; ++lane)
                dots[lane] = dot_i16_i8(hidden,
                    model->policy + (size_t)(action + lane) * model->hidden_dim,
                    model->hidden_dim);
        }
        for (unsigned lane = 0; lane < 8; ++lane)
            policy_logits[action + lane] = scale_q16(dots[lane], model->policy_scale_q16);
    }
    for (; action + 4U <= model->action_count; action += 4U) {
        int64_t dots[4];
        if (model->policy_i16 != NULL)
            tinyshogi_dot_i16_i16_4(hidden, model->policy_i16 + (size_t)action * model->hidden_dim,
                                    model->hidden_dim, model->hidden_dim, dots);
        else {
            for (unsigned lane = 0; lane < 4; ++lane)
                dots[lane] = dot_i16_i8(hidden,
                    model->policy + (size_t)(action + lane) * model->hidden_dim,
                    model->hidden_dim);
        }
        for (unsigned lane = 0; lane < 4; ++lane)
            policy_logits[action + lane] = scale_q16(dots[lane], model->policy_scale_q16);
    }
    for (; action < model->action_count; ++action) {
        int64_t dot = model->policy_i16 != NULL
            ? tinyshogi_dot_i16_i16(hidden, model->policy_i16 + (size_t)action * model->hidden_dim,
                                    model->hidden_dim)
            : dot_i16_i8(hidden, model->policy + (size_t)action * model->hidden_dim,
                         model->hidden_dim);
        policy_logits[action] = scale_q16(dot, model->policy_scale_q16);
    }
    int64_t value_dot = model->value_i16 != NULL
        ? tinyshogi_dot_i16_i16(hidden, model->value_i16, model->hidden_dim)
        : dot_i16_i8(hidden, model->value, model->hidden_dim);
    int32_t value = model->value_bias + scale_q16(value_dot, model->value_scale_q16);
    *value_q16 = int_tanh_q16(value);
    return true;
}

bool int_model_batch_workspace_init(IntModelBatchWorkspace *workspace,
                                    const IntModel *model, size_t capacity) {
    if (workspace == NULL || model == NULL || capacity == 0 ||
        model->feature_dim == 0 || model->hidden_dim == 0 || model->action_count == 0)
        return false;
    memset(workspace, 0, sizeof(*workspace));
    workspace->capacity = capacity;
    workspace->feature_dim = model->feature_dim;
    workspace->hidden_dim = model->hidden_dim;
    workspace->action_count = model->action_count;
    uint32_t hidden_padded = round_up_u32(model->hidden_dim, 64U);
    workspace->features_panel = aligned_calloc_256(
        (size_t)6U * model->feature_dim, sizeof(*workspace->features_panel));
    workspace->hidden_gemm = aligned_calloc_256(
        (size_t)6U * hidden_padded, sizeof(*workspace->hidden_gemm));
    if (workspace->features_panel == NULL || workspace->hidden_gemm == NULL) {
        int_model_batch_workspace_destroy(workspace);
        return false;
    }
    return true;
}

void int_model_batch_workspace_destroy(IntModelBatchWorkspace *workspace) {
    if (workspace == NULL) return;
    free(workspace->features_panel);
    free(workspace->hidden_gemm);
    memset(workspace, 0, sizeof(*workspace));
}

static void batch_pack_i8_features(const IntModelBatchWorkspace *workspace,
                                   const int8_t *features, size_t feature_stride,
                                   size_t base, size_t rows) {
    size_t kdim = workspace->feature_dim;
    for (size_t block = 0; block < kdim; block += 4U) {
        int8_t *panel = workspace->features_panel + (block / 4U) * 24U;
        for (size_t row = 0; row < 6U; ++row)
            for (size_t lane = 0; lane < 4U; ++lane)
                panel[row * 4U + lane] = row < rows
                    ? features[(base + row) * feature_stride + block + lane] : 0;
    }
}

bool int_model_eval_batch(const IntModel *model, IntModelBatchWorkspace *workspace,
                          const int8_t *features, size_t feature_stride,
                          size_t batch_count, int16_t *hidden, size_t hidden_stride,
                          int32_t *policy_logits, size_t policy_stride,
                          int32_t *value_q16) {
    if (model == NULL || workspace == NULL || features == NULL || hidden == NULL ||
        policy_logits == NULL || value_q16 == NULL || batch_count == 0 ||
        batch_count > workspace->capacity || workspace->feature_dim != model->feature_dim ||
        workspace->hidden_dim != model->hidden_dim || workspace->action_count != model->action_count ||
        feature_stride < model->feature_dim || hidden_stride < model->hidden_dim ||
        policy_stride < model->action_count || model->w1_gemm_i8 == NULL ||
        (model->feature_dim & 3U) != 0U ||
        (model->hidden_dim & 3U) != 0U)
        return false;
    uint32_t hidden_padded = model->w1_gemm_hidden_dim;
    for (size_t base = 0; base < batch_count; base += 6U) {
        size_t rows = batch_count - base;
        if (rows > 6U) rows = 6U;
        batch_pack_i8_features(workspace, features, feature_stride, base, rows);
        for (uint32_t output_panel = 0; output_panel < hidden_padded; output_panel += 64U)
            tinyshogi_gemm_i8_64x6(
                model->feature_dim,
                model->w1_gemm_i8 +
                    (size_t)(output_panel / 64U) * model->feature_dim * 64U,
                workspace->features_panel,
                workspace->hidden_gemm + output_panel, hidden_padded);
        for (size_t row = 0; row < rows; ++row) {
            for (uint32_t unit = 0; unit < model->hidden_dim; ++unit) {
                int32_t activation = scale_q16(
                    (int64_t)model->b1[unit] + workspace->hidden_gemm[row * hidden_padded + unit],
                    model->hidden_scale_q16);
                hidden[(base + row) * hidden_stride + unit] =
                    clamp_i16(activation > 0 ? activation : 0);
            }
        }
        for (size_t row = 0; row < rows; ++row) {
            uint32_t action = 0;
            for (; action + 8U <= model->action_count; action += 8U) {
                int64_t dots[8];
                tinyshogi_dot_i16_i16_8(
                    hidden + (base + row) * hidden_stride,
                    model->policy_i16 + (size_t)action * model->hidden_dim,
                    model->hidden_dim, model->hidden_dim, dots);
                for (unsigned lane = 0; lane < 8; ++lane)
                    policy_logits[(base + row) * policy_stride + action + lane] =
                        scale_q16(dots[lane], model->policy_scale_q16);
            }
            for (; action < model->action_count; ++action) {
                int64_t dot = tinyshogi_dot_i16_i16(
                    hidden + (base + row) * hidden_stride,
                    model->policy_i16 + (size_t)action * model->hidden_dim,
                    model->hidden_dim);
                policy_logits[(base + row) * policy_stride + action] =
                    scale_q16(dot, model->policy_scale_q16);
            }
            int64_t value_dot = tinyshogi_dot_i16_i16(
                hidden + (base + row) * hidden_stride,
                model->value_i16, model->hidden_dim);
            int32_t value = model->value_bias + scale_q16(value_dot, model->value_scale_q16);
            value_q16[base + row] = int_tanh_q16(value);
        }
    }
    return true;
}

void int_model_softmax(const IntModel *model, const int32_t *logits, int32_t *probabilities) {
    if (model == NULL) return;
    int_softmax_q16(logits, probabilities, model->action_count);
}
