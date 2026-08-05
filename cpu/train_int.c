#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <limits.h>
#if defined(__GNUC__) || defined(__clang__)
#include <immintrin.h>
#endif

#include "../src/int_math.h"

#define D (30U * 81U)
#define H 64U
#define A (81U * 81U * 2U + 7U * 81U)
#define MAX_POLICY_LABELS 1024U

typedef struct { uint32_t action; uint32_t visits; } Entry;

static unsigned square_id(const unsigned char *text) {
    if (text[0] < '1' || text[0] > '9' || text[1] < 'a' || text[1] > 'i') return UINT32_MAX;
    return (unsigned)(text[1] - 'a') * 9U + (unsigned)(9 - (text[0] - '0'));
}

static unsigned action_id(const unsigned char *move) {
    unsigned from, to;
    if (move[1] == '*') {
        const char *types = "RBGSNLP"; const char *found = strchr(types, move[0]);
        if (!found) return UINT32_MAX;
        to = square_id(move + 2);
        return to == UINT32_MAX ? UINT32_MAX : 13122U + (unsigned)(found - types) * 81U + to;
    }
    from = square_id(move); to = square_id(move + 2);
    if (from == UINT32_MAX || to == UINT32_MAX) return UINT32_MAX;
    return (from * 81U + to) * 2U + (move[4] == '+' ? 1U : 0U);
}

static int8_t quantize_feature(float raw) {
    float scaled = raw * 127.0f;
    int value = (int)(scaled >= 0.0f ? scaled + 0.5f : scaled - 0.5f);
    return value > 127 ? 127 : value < -127 ? -127 : (int8_t)value;
}

static int read_input(const char *feature_path, const char *label_path, int8_t **features,
                      int8_t **values, unsigned **offsets, unsigned **counts,
                      Entry **entries, unsigned *sample_count, unsigned *entry_count) {
    FILE *feature = fopen(feature_path, "rb"); if (!feature) return 1;
    uint32_t fh[4];
    if (fread(fh, sizeof(uint32_t), 4, feature) != 4 || memcmp(fh, "TFE1", 4) != 0 || fh[1] != 1 || fh[3] != 30) { fprintf(stderr, "invalid TFE1 header\n"); fclose(feature); return 1; }
    *sample_count = fh[2]; *features = malloc((size_t)*sample_count * D);
    float *raw = malloc((size_t)*sample_count * D * sizeof(float));
    if (!*features || !raw || fread(raw, sizeof(float), (size_t)*sample_count * D, feature) != (size_t)*sample_count * D) { free(raw); fclose(feature); return 1; }
    for (size_t i = 0; i < (size_t)*sample_count * D; ++i) {
        (*features)[i] = quantize_feature(raw[i]);
    }
    free(raw); fclose(feature);
    FILE *label = fopen(label_path, "rb"); if (!label) return 1;
    unsigned char header[8];
    if (fread(header, 1, 8, label) != 8 || memcmp(header, "TSF1", 4) != 0 || header[4] != 1) { fprintf(stderr, "invalid TSF1 header\n"); fclose(label); return 1; }
    *values = calloc(*sample_count, 1); *offsets = calloc(*sample_count, sizeof(unsigned)); *counts = calloc(*sample_count, sizeof(unsigned));
    Entry *data = NULL; unsigned used = 0, capacity = 0;
    unsigned char fixed[99];
    for (unsigned sample = 0; sample < *sample_count; ++sample) {
        if (fread(fixed, 1, sizeof(fixed), label) != sizeof(fixed)) { fprintf(stderr, "short TSF1 record %u\n", sample); goto error; }
        (*values)[sample] = (int8_t)fixed[96];
        unsigned policy_count = (unsigned)fixed[97] | ((unsigned)fixed[98] << 8);
        (*offsets)[sample] = used;
        for (unsigned index = 0; index < policy_count; ++index) {
            unsigned char encoded[12]; if (fread(encoded, 1, 12, label) != 12) goto error;
            unsigned action = action_id(encoded); if (action >= A) continue;
            if (used == capacity) { unsigned next = capacity ? capacity * 2U : 1024U; Entry *grown = realloc(data, (size_t)next * sizeof(*data)); if (!grown) goto error; data = grown; capacity = next; }
            data[used].action = action;
            data[used].visits = (unsigned)encoded[8] | ((unsigned)encoded[9] << 8) | ((unsigned)encoded[10] << 16) | ((unsigned)encoded[11] << 24);
            ++used;
        }
        (*counts)[sample] = used - (*offsets)[sample];
    }
    fclose(label); *entries = data; *entry_count = used; return 0;
error:
    fclose(label); free(data); free(*features); free(*values); free(*offsets); free(*counts); return 1;
}

static int32_t dot_hidden(const int8_t *features, const int16_t *weights) {
    int32_t result = 0;
    for (unsigned i = 0; i < D; ++i) result += (int32_t)features[i] * weights[i];
    return result;
}

#if defined(__GNUC__) || defined(__clang__)
__attribute__((target("avx2")))
static int32_t dot_hidden_avx2(const int8_t *features, const int16_t *weights) {
    __m256i sum = _mm256_setzero_si256();
    unsigned i = 0;
    for (; i + 16 <= D; i += 16) {
        __m128i xf = _mm_loadu_si128((const __m128i *)(features + i));
        __m256i xw = _mm256_loadu_si256((const __m256i *)(weights + i));
        __m256i af = _mm256_cvtepi8_epi16(xf);
        sum = _mm256_add_epi32(sum, _mm256_madd_epi16(_mm256_mullo_epi16(af, xw), _mm256_set1_epi16(1)));
    }
    __m128i low = _mm256_castsi256_si128(sum);
    __m128i high = _mm256_extracti128_si256(sum, 1);
    __m128i folded = _mm_add_epi32(low, high);
    folded = _mm_add_epi32(folded, _mm_shuffle_epi32(folded, _MM_SHUFFLE(2, 3, 0, 1)));
    folded = _mm_add_epi32(folded, _mm_shuffle_epi32(folded, _MM_SHUFFLE(1, 0, 3, 2)));
    int32_t result = _mm_cvtsi128_si32(folded);
    for (; i < D; ++i) result += (int32_t)features[i] * weights[i];
    return result;
}
#endif

static int8_t quantize_i8(int32_t value) {
    if (value > 127) return 127;
    if (value < -127) return -127;
    return (int8_t)value;
}

static void write_tsm3(const char *path, const int16_t *w1, const int32_t *value,
                       const int32_t *policy) {
    int32_t max_value = 1, max_policy = 1;
    for (unsigned i = 0; i < H; ++i) if (abs(value[i]) > max_value) max_value = abs(value[i]);
    for (size_t i = 0; i < (size_t)A * H; ++i) if (abs(policy[i]) > max_policy) max_policy = abs(policy[i]);
    FILE *file = fopen(path, "wb"); if (!file) return;
    fwrite("TSM3", 1, 4, file); uint32_t metadata[4] = {1, D, H, A};
    /* hidden = dot / 256, policy/value logits = dot / 1024. */
    int32_t scales[4] = {65536, 256, 64, 64};
    fwrite(metadata, sizeof(uint32_t), 4, file);
    fwrite(scales, sizeof(int32_t), 4, file);
    for (size_t i = 0; i < (size_t)D * H; ++i) fputc((unsigned char)quantize_i8(w1[i]), file);
    int32_t zero[H] = {0}; fwrite(zero, sizeof(int32_t), H, file);
    for (unsigned i = 0; i < H; ++i) { int value_q = value[i] / (max_value / 127 + 1); if (value_q > 127) value_q = 127; if (value_q < -127) value_q = -127; fputc((unsigned char)(int8_t)value_q, file); }
    int32_t value_bias = 0; fwrite(&value_bias, sizeof(value_bias), 1, file);
    for (size_t i = 0; i < (size_t)A * H; ++i) {
        int policy_q = policy[i] / (max_policy / 127 + 1);
        fputc((unsigned char)quantize_i8(policy_q), file);
    }
    fclose(file);
}

int main(int argc, char **argv) {
    if (argc < 4 || argc > 5) { fprintf(stderr, "usage: %s data.tsf features.tfe model.tsm3 [epochs]\n", argv[0]); return 2; }
    unsigned epochs = argc == 5 ? (unsigned)strtoul(argv[4], NULL, 10) : 10U;
    int8_t *features = NULL, *values = NULL; unsigned *offsets = NULL, *counts = NULL, samples = 0, entries_count = 0; Entry *entries = NULL;
    if (!epochs || read_input(argv[2], argv[1], &features, &values, &offsets, &counts, &entries, &samples, &entries_count) != 0) return 1;
    int16_t *w1 = calloc((size_t)H * D, sizeof(*w1));
    int32_t *value = calloc(H, sizeof(int32_t));
    int32_t *policy = calloc((size_t)A * H, sizeof(int32_t));
    int16_t hidden[H]; if (!w1 || !value || !policy) return 1;
    int32_t (*dot)(const int8_t *, const int16_t *) = dot_hidden;
#if defined(__GNUC__) || defined(__clang__)
    if (__builtin_cpu_supports("avx2")) dot = dot_hidden_avx2;
#endif
    for (unsigned unit = 0; unit < H; ++unit) for (unsigned feature = 0; feature < D; ++feature) {
        uint32_t state = unit * 747796405U + feature * 2891336453U + 17U; state ^= state >> 16;
        w1[(size_t)unit * D + feature] = (int16_t)((state % 3U) - 1);
    }
    for (unsigned epoch = 0; epoch < epochs; ++epoch) {
        for (unsigned sample = 0; sample < samples; ++sample) {
            int32_t preactivation[H];
            for (unsigned unit = 0; unit < H; ++unit) {
                preactivation[unit] = dot(features + (size_t)sample * D, w1 + (size_t)unit * D);
                int32_t activation = preactivation[unit] >> 8;
                hidden[unit] = activation > 32767 ? 32767 : (activation > 0 ? (int16_t)activation : 0);
            }
            int64_t value_acc = 0;
            for (unsigned unit = 0; unit < H; ++unit) value_acc += ((int64_t)hidden[unit] * value[unit] * 64) >> 16;
            int32_t value_logit = value_acc > INT32_MAX ? INT32_MAX : value_acc < INT32_MIN ? INT32_MIN : (int32_t)value_acc;
            int32_t value_error = (int32_t)values[sample] * 65536 - value_logit;
            int32_t hidden_gradient[H] = {0};
            for (unsigned unit = 0; unit < H; ++unit) {
                int64_t delta = ((int64_t)value_error * hidden[unit]) >> 24;
                if (delta > INT32_MAX) delta = INT32_MAX;
                if (delta < INT32_MIN) delta = INT32_MIN;
                value[unit] += (int32_t)delta;
                hidden_gradient[unit] += (int32_t)(((int64_t)value_error * value[unit] * 64) >> 16);
            }
            unsigned total_visits = 0;
            for (unsigned j = 0; j < counts[sample]; ++j) total_visits += entries[offsets[sample] + j].visits;
            if (total_visits == 0) total_visits = 1;
            if (counts[sample] > MAX_POLICY_LABELS) return 1;
            int32_t logits[MAX_POLICY_LABELS];
            int32_t probabilities[MAX_POLICY_LABELS];
            for (unsigned j = 0; j < counts[sample]; ++j) {
                Entry entry = entries[offsets[sample] + j];
                int64_t logit_acc = 0;
                for (unsigned unit = 0; unit < H; ++unit) logit_acc += ((int64_t)hidden[unit] * policy[(size_t)entry.action * H + unit] * 64) >> 16;
                logits[j] = logit_acc > INT32_MAX ? INT32_MAX : logit_acc < INT32_MIN ? INT32_MIN : (int32_t)logit_acc;
            }
            int_softmax_q16(logits, probabilities, counts[sample]);
            for (unsigned j = 0; j < counts[sample]; ++j) {
                Entry entry = entries[offsets[sample] + j];
                int32_t target = (int32_t)(((uint64_t)entry.visits * 65536U) / total_visits);
                int32_t error = target - probabilities[j];
                for (unsigned unit = 0; unit < H; ++unit) {
                    int64_t delta = ((int64_t)error * hidden[unit]) >> 24;
                    if (delta > INT32_MAX) delta = INT32_MAX;
                    if (delta < INT32_MIN) delta = INT32_MIN;
                    policy[(size_t)entry.action * H + unit] += (int32_t)delta;
                    hidden_gradient[unit] += (int32_t)(((int64_t)error * policy[(size_t)entry.action * H + unit] * 64) >> 16);
                }
            }
            for (unsigned unit = 0; unit < H; ++unit) if (preactivation[unit] > 0) {
                int32_t gradient = hidden_gradient[unit] >> 8;
                for (unsigned feature = 0; feature < D; ++feature) {
                    int64_t delta = ((int64_t)gradient * features[(size_t)sample * D + feature]) >> 14;
                    int64_t updated = (int64_t)w1[(size_t)unit * D + feature] + delta;
                    if (updated > 127) updated = 127;
                    if (updated < -127) updated = -127;
                    w1[(size_t)unit * D + feature] = (int16_t)updated;
                }
            }
        }
        fprintf(stderr, "integer epoch=%u samples=%u labels=%u\n", epoch + 1, samples, entries_count);
    }
    write_tsm3(argv[3], w1, value, policy);
    free(features); free(values); free(offsets); free(counts); free(entries); free(w1); free(value); free(policy); return 0;
}
