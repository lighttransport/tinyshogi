#define _POSIX_C_SOURCE 200809L

#include "nnue.h"
#include "simd.h"

#include <limits.h>
#include <math.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#define NNUE_MAGIC "NNUE1"
#define NNUE_HAND_BASE SHOGI_NNUE_BOARD_FEATURES
#define NNUE_HAND_COUNTS 19U

static uint8_t orient_square(uint8_t square, ShogiColor perspective) {
    if (perspective == SHOGI_BLACK || square == SHOGI_SQ_NONE) return square;
    unsigned row = square / SHOGI_BOARD_SIZE;
    unsigned col = square % SHOGI_BOARD_SIZE;
    return (uint8_t)((SHOGI_BOARD_SIZE - 1U - row) * SHOGI_BOARD_SIZE +
                     (SHOGI_BOARD_SIZE - 1U - col));
}

static uint32_t board_feature(uint8_t king, uint8_t square,
                              uint8_t piece, ShogiColor perspective) {
    ShogiColor owner = shogi_piece_color(piece);
    ShogiPieceType type = shogi_piece_type(piece);
    unsigned relative_color = owner == perspective ? 0U : 1U;
    unsigned piece_class = relative_color * 14U + ((unsigned)type - 1U);
    return ((uint32_t)orient_square(king, perspective) * 28U + piece_class) *
           SHOGI_SQUARES + orient_square(square, perspective);
}

static uint32_t hand_feature(unsigned relative_color, unsigned type,
                             unsigned count) {
    if (count >= NNUE_HAND_COUNTS) count = NNUE_HAND_COUNTS - 1U;
    return NNUE_HAND_BASE + (relative_color * 7U + type) * NNUE_HAND_COUNTS + count;
}

size_t shogi_nnue_feature_ids(const ShogiPosition *position,
                              ShogiColor perspective,
                              uint32_t *features, size_t capacity) {
    if (position == NULL || features == NULL || capacity == 0) return 0;
    uint8_t king = position->king_square[perspective];
    if (king == SHOGI_SQ_NONE) return 0;
    size_t count = 0;
    for (uint8_t square = 0; square < SHOGI_SQUARES; ++square) {
        uint8_t piece = position->board[square];
        if (piece == SHOGI_EMPTY) continue;
        if (count < capacity) features[count] = board_feature(king, square, piece, perspective);
        ++count;
    }
    for (unsigned color = 0; color < 2; ++color) {
        unsigned relative = color == (unsigned)perspective ? 0U : 1U;
        for (unsigned type = 0; type < 7; ++type) {
            if (count < capacity) features[count] = hand_feature(relative, type, position->hand[color][type]);
            ++count;
        }
    }
    return count;
}

void shogi_nnue_model_init(ShogiNnueModel *model) {
    if (model != NULL) memset(model, 0, sizeof(*model));
}

void shogi_nnue_model_destroy(ShogiNnueModel *model) {
    if (model == NULL) return;
    free(model->feature_weights);
    free(model->output_weights);
    memset(model, 0, sizeof(*model));
}

bool shogi_nnue_model_init_default(ShogiNnueModel *model, uint32_t hidden_dim) {
    if (model == NULL || hidden_dim == 0 || hidden_dim > 4096U) return false;
    shogi_nnue_model_destroy(model);
    size_t features = (size_t)SHOGI_NNUE_FEATURE_COUNT * hidden_dim;
    model->feature_weights = calloc(features, sizeof(*model->feature_weights));
    model->output_weights = calloc((size_t)hidden_dim * 2U, sizeof(*model->output_weights));
    if (model->feature_weights == NULL || model->output_weights == NULL) {
        shogi_nnue_model_destroy(model);
        return false;
    }
    model->feature_count = SHOGI_NNUE_FEATURE_COUNT;
    model->hidden_dim = hidden_dim;
    model->feature_scale = 256;
    model->output_scale = 1024;
    return true;
}

static bool checked_size(uint32_t a, uint32_t b, size_t element_size, size_t *out) {
    if (b != 0 && a > SIZE_MAX / b) return false;
    size_t count = (size_t)a * b;
    if (element_size != 0 && count > SIZE_MAX / element_size) return false;
    *out = count * element_size;
    return true;
}

bool shogi_nnue_model_load(ShogiNnueModel *model, const char *path) {
    if (model == NULL || path == NULL) return false;
    FILE *file = fopen(path, "rb");
    if (file == NULL) return false;
    char magic[5];
    uint32_t metadata[4];
    int32_t scales[2];
    bool ok = fread(magic, 1, sizeof(magic), file) == sizeof(magic) &&
              memcmp(magic, NNUE_MAGIC, sizeof(magic)) == 0 &&
              fread(metadata, sizeof(*metadata), 4, file) == 4 &&
              metadata[0] == SHOGI_NNUE_FORMAT_VERSION &&
              metadata[1] == SHOGI_NNUE_FEATURE_COUNT && metadata[2] > 0 &&
              fread(scales, sizeof(*scales), 2, file) == 2 &&
              scales[0] > 0 && scales[1] > 0;
    size_t feature_bytes = 0;
    if (ok) ok = checked_size(metadata[1], metadata[2], sizeof(int16_t), &feature_bytes) &&
                metadata[3] == 2U;
    size_t output_bytes = ok ? (size_t)metadata[2] * 2U * sizeof(int16_t) : 0;
    int16_t *feature_weights = ok ? malloc(feature_bytes) : NULL;
    int16_t *output_weights = ok ? malloc(output_bytes) : NULL;
    int32_t bias = 0;
    if (ok) ok = feature_weights != NULL && output_weights != NULL &&
                fread(feature_weights, 1, feature_bytes, file) == feature_bytes &&
                fread(output_weights, 1, output_bytes, file) == output_bytes &&
                fread(&bias, sizeof(bias), 1, file) == 1;
    fclose(file);
    if (!ok) { free(feature_weights); free(output_weights); return false; }
    shogi_nnue_model_destroy(model);
    model->feature_count = metadata[1]; model->hidden_dim = metadata[2];
    model->feature_scale = scales[0]; model->output_scale = scales[1];
    model->feature_weights = feature_weights; model->output_weights = output_weights;
    model->output_bias = bias;
    return true;
}

bool shogi_nnue_model_save(const ShogiNnueModel *model, const char *path) {
    if (model == NULL || path == NULL || model->feature_weights == NULL ||
        model->output_weights == NULL || model->feature_count != SHOGI_NNUE_FEATURE_COUNT ||
        model->hidden_dim == 0 || model->feature_scale <= 0 || model->output_scale <= 0) return false;
    FILE *file = fopen(path, "wb");
    if (file == NULL) return false;
    uint32_t metadata[4] = {SHOGI_NNUE_FORMAT_VERSION, model->feature_count,
                            model->hidden_dim, 2U};
    int32_t scales[2] = {model->feature_scale, model->output_scale};
    size_t feature_bytes = (size_t)model->feature_count * model->hidden_dim * sizeof(int16_t);
    size_t output_bytes = (size_t)model->hidden_dim * 2U * sizeof(int16_t);
    bool ok = fwrite(NNUE_MAGIC, 1, 5, file) == 5 &&
              fwrite(metadata, sizeof(*metadata), 4, file) == 4 &&
              fwrite(scales, sizeof(*scales), 2, file) == 2 &&
              fwrite(model->feature_weights, 1, feature_bytes, file) == feature_bytes &&
              fwrite(model->output_weights, 1, output_bytes, file) == output_bytes &&
              fwrite(&model->output_bias, sizeof(model->output_bias), 1, file) == 1;
    if (fclose(file) != 0) ok = false;
    return ok;
}

bool shogi_nnue_accumulator_init(ShogiNnueAccumulator *accumulator,
                                 uint32_t hidden_dim) {
    if (accumulator == NULL || hidden_dim == 0) return false;
    memset(accumulator, 0, sizeof(*accumulator));
    accumulator->hidden_dim = hidden_dim;
    accumulator->sum[0] = calloc(hidden_dim, sizeof(int32_t));
    accumulator->sum[1] = calloc(hidden_dim, sizeof(int32_t));
    if (accumulator->sum[0] == NULL || accumulator->sum[1] == NULL) {
        shogi_nnue_accumulator_destroy(accumulator); return false;
    }
    return true;
}

void shogi_nnue_accumulator_destroy(ShogiNnueAccumulator *accumulator) {
    if (accumulator == NULL) return;
    free(accumulator->sum[0]); free(accumulator->sum[1]);
    memset(accumulator, 0, sizeof(*accumulator));
}

static bool shogi_nnue_accumulator_build_perspective(
    const ShogiNnueModel *model, const ShogiPosition *position,
    ShogiNnueAccumulator *accumulator, unsigned perspective) {
    if (model == NULL || position == NULL || accumulator == NULL ||
        model->feature_weights == NULL || accumulator->hidden_dim != model->hidden_dim ||
        perspective > SHOGI_WHITE) return false;
    memset(accumulator->sum[perspective], 0, model->hidden_dim * sizeof(int32_t));
    uint32_t ids[SHOGI_SQUARES + 14];
    const int16_t *rows[SHOGI_SQUARES + 14];
    size_t count = shogi_nnue_feature_ids(position, (ShogiColor)perspective, ids,
                                          sizeof(ids) / sizeof(ids[0]));
    for (size_t item = 0; item < count; ++item)
        rows[item] = model->feature_weights + (size_t)ids[item] * model->hidden_dim;
    tinyshogi_add_i16_i32_rows(accumulator->sum[perspective], rows, count,
                               model->hidden_dim, 1);
    return true;
}

bool shogi_nnue_accumulator_build(const ShogiNnueModel *model,
                                  const ShogiPosition *position,
                                  ShogiNnueAccumulator *accumulator) {
    return shogi_nnue_accumulator_build_perspective(model, position, accumulator, 0) &&
           shogi_nnue_accumulator_build_perspective(model, position, accumulator, 1);
}

bool shogi_nnue_accumulator_update(const ShogiNnueModel *model,
                                   const ShogiPosition *before,
                                   const ShogiPosition *after,
                                   ShogiNnueAccumulator *accumulator) {
    if (model == NULL || before == NULL || after == NULL || accumulator == NULL ||
        model->feature_weights == NULL || accumulator->hidden_dim != model->hidden_dim) return false;
    uint32_t old_ids[SHOGI_SQUARES + 14], new_ids[SHOGI_SQUARES + 14];
    const int16_t *removed[SHOGI_SQUARES + 14], *added[SHOGI_SQUARES + 14];
    for (unsigned perspective = 0; perspective < 2; ++perspective) {
        size_t old_count = shogi_nnue_feature_ids(before, (ShogiColor)perspective,
                                                  old_ids, sizeof(old_ids) / sizeof(old_ids[0]));
        size_t new_count = shogi_nnue_feature_ids(after, (ShogiColor)perspective,
                                                  new_ids, sizeof(new_ids) / sizeof(new_ids[0]));
        size_t removed_count = 0, added_count = 0;
        for (size_t index = 0; index < old_count; ++index) {
            bool remains = false;
            for (size_t next = 0; next < new_count; ++next)
                if (old_ids[index] == new_ids[next]) { remains = true; break; }
            if (!remains) {
                removed[removed_count++] = model->feature_weights +
                    (size_t)old_ids[index] * model->hidden_dim;
            }
        }
        for (size_t index = 0; index < new_count; ++index) {
            bool already = false;
            for (size_t old = 0; old < old_count; ++old)
                if (new_ids[index] == old_ids[old]) { already = true; break; }
            if (!already) {
                added[added_count++] = model->feature_weights +
                    (size_t)new_ids[index] * model->hidden_dim;
            }
        }
        tinyshogi_add_i16_i32_rows(accumulator->sum[perspective], removed,
                                   removed_count, model->hidden_dim, -1);
        tinyshogi_add_i16_i32_rows(accumulator->sum[perspective], added,
                                   added_count, model->hidden_dim, 1);
    }
    return true;
}

int shogi_nnue_evaluate(const ShogiNnueModel *model,
                        const ShogiNnueAccumulator *accumulator,
                        ShogiColor perspective) {
    if (model == NULL || accumulator == NULL || model->output_weights == NULL ||
        perspective > SHOGI_WHITE || accumulator->hidden_dim != model->hidden_dim) return 0;
    int64_t value = (int64_t)model->output_bias * model->feature_scale;
    const int16_t *weights = model->output_weights + (size_t)perspective * model->hidden_dim;
    value += tinyshogi_dot_relu_i32_i16(accumulator->sum[perspective], weights,
                                        model->hidden_dim);
    /* Training targets are normalized to [-1, 1]; search consumes centipawns. */
    int64_t scale = (int64_t)model->feature_scale * model->output_scale;
    double normalized = scale == 0 ? (double)value : (double)value / (double)scale;
    double bounded = tanh(normalized) * 1000.0;
    if (bounded > INT_MAX) return INT_MAX;
    if (bounded < INT_MIN) return INT_MIN;
    return (int)bounded;
}

int shogi_nnue_evaluate_position(const ShogiNnueModel *model,
                                 const ShogiPosition *position,
                                 ShogiColor perspective) {
    if (model == NULL || position == NULL) return 0;
    /* Search evaluates positions from worker threads. Reuse one scratch
     * accumulator per thread to keep the hot path free of malloc/free while
     * retaining thread safety and the public accumulator API. */
    static _Thread_local ShogiNnueAccumulator scratch;
    static _Thread_local const ShogiNnueModel *scratch_model;
    static _Thread_local const int16_t *scratch_feature_weights;
    static _Thread_local const int16_t *scratch_output_weights;
    static _Thread_local uint64_t scratch_hash;
    static _Thread_local unsigned scratch_valid_perspectives;
    if (scratch.hidden_dim != model->hidden_dim ||
        scratch.sum[0] == NULL || scratch.sum[1] == NULL) {
        shogi_nnue_accumulator_destroy(&scratch);
        if (!shogi_nnue_accumulator_init(&scratch, model->hidden_dim)) {
            scratch_valid_perspectives = 0;
            return 0;
        }
        scratch_valid_perspectives = 0;
    }
    if (scratch_model != model || scratch_feature_weights != model->feature_weights ||
        scratch_output_weights != model->output_weights || scratch_hash != position->hash)
        scratch_valid_perspectives = 0;
    if ((scratch_valid_perspectives & (1U << perspective)) != 0U &&
        scratch_model == model &&
        scratch_feature_weights == model->feature_weights &&
        scratch_output_weights == model->output_weights &&
        scratch_hash == position->hash)
        return shogi_nnue_evaluate(model, &scratch, perspective);
    if (!shogi_nnue_accumulator_build_perspective(model, position, &scratch, perspective))
        return 0;
    scratch_model = model;
    scratch_feature_weights = model->feature_weights;
    scratch_output_weights = model->output_weights;
    scratch_hash = position->hash;
    scratch_valid_perspectives |= 1U << perspective;
    return shogi_nnue_evaluate(model, &scratch, perspective);
}
