#include "../src/nnue.h"

#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#define NDF_MAGIC "NDF1"
#define DEFAULT_EPOCHS 5U
#define DEFAULT_HIDDEN SHOGI_NNUE_DEFAULT_HIDDEN

typedef struct {
    uint8_t board[SHOGI_SQUARES];
    uint8_t hand[14];
    uint8_t padding;
    int16_t value;
    uint8_t side;
    uint8_t source;
} Record;

static int read_data(const char *path, Record **out, uint32_t *count) {
    FILE *file = fopen(path, "rb");
    if (!file) return 1;
    char magic[4]; uint32_t header[3];
    if (fread(magic, 1, 4, file) != 4 || memcmp(magic, NDF_MAGIC, 4) != 0 ||
        fread(header, sizeof(*header), 3, file) != 3 || header[0] != 1 || header[2] != sizeof(Record)) {
        fclose(file); return 1;
    }
    Record *records = calloc(header[1], sizeof(*records));
    if (records == NULL || fread(records, sizeof(*records), header[1], file) != header[1]) {
        free(records); fclose(file); return 1;
    }
    fclose(file); *out = records; *count = header[1]; return 0;
}

static void make_position(const Record *record, ShogiPosition *position) {
    memset(position, 0, sizeof(*position));
    memcpy(position->board, record->board, sizeof(position->board));
    memcpy(position->hand, record->hand, sizeof(position->hand));
    position->side = (ShogiColor)record->side;
    position->king_square[0] = position->king_square[1] = SHOGI_SQ_NONE;
    for (uint8_t square = 0; square < SHOGI_SQUARES; ++square) {
        if (position->board[square] != SHOGI_EMPTY &&
            shogi_piece_type(position->board[square]) == SHOGI_KING)
            position->king_square[shogi_piece_color(position->board[square])] = square;
    }
}

static float frand(unsigned *state) {
    *state = *state * 1664525U + 1013904223U;
    return ((float)((*state >> 8) & 0xffffffU) / 16777216.0f) * 2.0f - 1.0f;
}

static int16_t quantize(float value, float scale) {
    long rounded = lroundf(value * scale);
    if (rounded > INT16_MAX) rounded = INT16_MAX;
    if (rounded < INT16_MIN) rounded = INT16_MIN;
    return (int16_t)rounded;
}

static int write_model(const char *path, const float *features, const float *output,
                       uint32_t hidden, float bias) {
    ShogiNnueModel model;
    shogi_nnue_model_init(&model);
    if (!shogi_nnue_model_init_default(&model, hidden)) return 1;
    size_t feature_count = (size_t)model.feature_count * hidden;
    for (size_t index = 0; index < feature_count; ++index)
        model.feature_weights[index] = quantize(features[index], 256.0f);
    for (size_t index = 0; index < (size_t)hidden * 2U; ++index)
        model.output_weights[index] = quantize(output[index], 1024.0f);
    model.output_bias = (int32_t)lroundf(bias * 1024.0f);
    int result = shogi_nnue_model_save(&model, path) ? 0 : 1;
    shogi_nnue_model_destroy(&model);
    return result;
}

int main(int argc, char **argv) {
    if (argc < 3 || argc > 5) {
        fprintf(stderr, "usage: %s data.ndf1 output.nnue [epochs] [learning-rate]\n", argv[0]);
        return 2;
    }
    uint32_t epochs = argc >= 4 ? (uint32_t)strtoul(argv[3], NULL, 10) : DEFAULT_EPOCHS;
    float learning_rate = argc >= 5 ? strtof(argv[4], NULL) : 0.01f;
    if (epochs == 0 || learning_rate <= 0.0f) return 2;
    Record *records = NULL; uint32_t count = 0;
    if (read_data(argv[1], &records, &count) != 0 || count == 0) {
        fprintf(stderr, "cannot read NDF1 data\n"); return 1;
    }
    const uint32_t hidden = DEFAULT_HIDDEN;
    size_t feature_weights = (size_t)SHOGI_NNUE_FEATURE_COUNT * hidden;
    float *weights = calloc(feature_weights, sizeof(*weights));
    float *output = calloc((size_t)hidden * 2U, sizeof(*output));
    uint32_t *ids = malloc((SHOGI_SQUARES + 14U) * sizeof(*ids));
    if (!weights || !output || !ids) { free(records); free(weights); free(output); free(ids); return 1; }
    unsigned random_state = 7U;
    for (size_t index = 0; index < feature_weights; ++index) weights[index] = frand(&random_state) * 0.01f;
    for (size_t index = 0; index < (size_t)hidden * 2U; ++index) output[index] = frand(&random_state) * 0.01f;
    shogi_init();
    for (uint32_t epoch = 0; epoch < epochs; ++epoch) {
        double loss = 0.0;
        for (uint32_t sample = 0; sample < count; ++sample) {
            ShogiPosition position; make_position(&records[sample], &position);
            size_t active = shogi_nnue_feature_ids(&position, position.side, ids, SHOGI_SQUARES + 14U);
            float hidden_values[DEFAULT_HIDDEN];
            for (uint32_t unit = 0; unit < hidden; ++unit) {
                float sum = 0.0f;
                for (size_t item = 0; item < active; ++item) sum += weights[(size_t)ids[item] * hidden + unit];
                hidden_values[unit] = sum > 0.0f ? sum : 0.0f;
            }
            float prediction = 0.0f;
            for (uint32_t unit = 0; unit < hidden; ++unit) prediction += hidden_values[unit] * output[position.side * hidden + unit];
            prediction = tanhf(prediction);
            float target = (float)records[sample].value / 1000.0f;
            float error = target - prediction;
            loss += (double)error * error;
            float gradient = error * (1.0f - prediction * prediction);
            for (uint32_t unit = 0; unit < hidden; ++unit) {
                float old_output = output[position.side * hidden + unit];
                output[position.side * hidden + unit] += learning_rate * gradient * hidden_values[unit];
                if (hidden_values[unit] > 0.0f)
                    for (size_t item = 0; item < active; ++item)
                        weights[(size_t)ids[item] * hidden + unit] += learning_rate * gradient * old_output;
            }
        }
        fprintf(stderr, "nnue epoch=%u samples=%u mse=%.8f\n", epoch + 1, count, loss / count);
    }
    int result = write_model(argv[2], weights, output, hidden, 0.0f);
    free(records); free(weights); free(output); free(ids);
    return result;
}
