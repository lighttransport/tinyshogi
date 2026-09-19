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

static bool valid_perspective(ShogiColor perspective) {
    return perspective == SHOGI_BLACK || perspective == SHOGI_WHITE;
}

static inline uint8_t orient_square(uint8_t square, ShogiColor perspective) {
    if (perspective == SHOGI_BLACK || square == SHOGI_SQ_NONE) return square;
    return (uint8_t)(SHOGI_SQUARES - 1U - square);
}

static inline uint32_t board_feature(uint8_t king, uint8_t square,
                                     uint8_t piece, ShogiColor perspective) {
    unsigned owner = (piece >> 4) & 1U;
    unsigned type = piece & 0x0fU;
    unsigned piece_class = (owner != (unsigned)perspective ? 14U : 0U) + type - 1U;
    return ((uint32_t)orient_square(king, perspective) * 28U + piece_class) *
           SHOGI_SQUARES + orient_square(square, perspective);
}

static inline uint32_t hand_feature(unsigned relative_color, unsigned type,
                                    unsigned count) {
    if (count >= NNUE_HAND_COUNTS) count = NNUE_HAND_COUNTS - 1U;
    return NNUE_HAND_BASE + (relative_color * 7U + type) * NNUE_HAND_COUNTS + count;
}

static void cache_feature_position(ShogiPosition *cached,
                                   const ShogiPosition *position) {
    memcpy(cached->board, position->board, sizeof(cached->board));
    memcpy(cached->hand, position->hand, sizeof(cached->hand));
    cached->king_square[0] = position->king_square[0];
    cached->king_square[1] = position->king_square[1];
}

size_t shogi_nnue_feature_ids(const ShogiPosition *position,
                              ShogiColor perspective,
                              uint32_t *features, size_t capacity) {
    if (position == NULL || features == NULL || capacity == 0 ||
        !valid_perspective(perspective)) return 0;
    uint8_t king = position->king_square[perspective];
    if (king >= SHOGI_SQUARES ||
        position->board[king] != shogi_piece(perspective, SHOGI_KING)) return 0;
    size_t count = 0;
    for (uint8_t square = 0; square < SHOGI_SQUARES; ++square) {
        uint8_t piece = position->board[square];
        if (piece == SHOGI_EMPTY) continue;
        ShogiPieceType type = shogi_piece_type(piece);
        ShogiColor color = shogi_piece_color(piece);
        if (type < SHOGI_PAWN || type > SHOGI_DRAGON ||
            piece != shogi_piece(color, type)) return 0;
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
    free(model->head_weights);
    free(model->head_weights_packed);
    free(model->head_bias);
    free(model->final_weights);
    free(model->final_bias);
    free(model->output_thresholds);
    memset(model, 0, sizeof(*model));
}

static int bounded_score_reference(int64_t value, int64_t scale) {
    double normalized = scale == 0 ? (double)value : (double)value / (double)scale;
    return (int)(tanh(normalized) * 1000.0);
}

static bool build_output_thresholds(ShogiNnueModel *model) {
    uint64_t *thresholds = malloc(1000U * sizeof(*thresholds));
    if (thresholds == NULL) return false;
    int64_t scale = (int64_t)model->feature_scale * model->output_scale;
    uint64_t previous = 0;
    for (int target = 1; target <= 1000; ++target) {
        if (bounded_score_reference(INT64_MAX, scale) < target) {
            thresholds[target - 1] = UINT64_MAX;
            continue;
        }
        uint64_t low = previous;
        uint64_t high = INT64_MAX;
        while (low < high) {
            uint64_t middle = low + (high - low) / 2U;
            if (bounded_score_reference((int64_t)middle, scale) >= target)
                high = middle;
            else
                low = middle + 1U;
        }
        thresholds[target - 1] = low;
        previous = low;
    }
    free(model->output_thresholds);
    model->output_thresholds = thresholds;
    return true;
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
    model->format_version = SHOGI_NNUE_FORMAT_VERSION;
    model->hidden_dim = hidden_dim;
    model->feature_scale = 256;
    model->output_scale = 1024;
    model->activation_clip = INT32_MAX;
    if (!build_output_thresholds(model)) {
        shogi_nnue_model_destroy(model);
        return false;
    }
    return true;
}

static bool checked_size(uint32_t a, uint32_t b, size_t element_size, size_t *out) {
    if (b != 0 && a > SIZE_MAX / b) return false;
    size_t count = (size_t)a * b;
    if (element_size != 0 && count > SIZE_MAX / element_size) return false;
    *out = count * element_size;
    return true;
}

static bool checked_add(size_t *total, size_t amount) {
    if (total == NULL || *total > SIZE_MAX - amount) return false;
    *total += amount;
    return true;
}

static bool file_has_remaining(FILE *file, size_t required) {
    if (file == NULL || required > (size_t)LONG_MAX) return false;
    long current = ftell(file);
    if (current < 0 || fseek(file, 0, SEEK_END) != 0) return false;
    long end = ftell(file);
    bool restored = fseek(file, current, SEEK_SET) == 0;
    return restored && end >= current && (size_t)(end - current) >= required;
}

static bool nnue3_evaluate_raw(const ShogiNnueModel *model, const int32_t *sum,
                               ShogiColor perspective, int64_t *raw) {
    if (model == NULL || sum == NULL || raw == NULL || model->head_dim == 0 ||
        model->head_weights == NULL || model->head_bias == NULL ||
        model->final_weights == NULL || model->final_bias == NULL) return false;
    const int16_t *head_weights = model->head_weights +
        (size_t)perspective * model->head_dim * model->hidden_dim;
    const int16_t *final_weights = model->final_weights +
        (size_t)perspective * model->head_dim;
    const int64_t *head_bias = model->head_bias +
        (size_t)perspective * model->head_dim;
    int64_t result = model->final_bias[perspective];
    for (uint32_t head = 0; head < model->head_dim; ++head) {
        int64_t head_raw = head_bias[head];
        const int16_t *weights = head_weights + (size_t)head * model->hidden_dim;
        for (uint32_t unit = 0; unit < model->hidden_dim; ++unit) {
            int32_t activation = sum[unit];
            if (activation < 0) activation = 0;
            if (activation > model->activation_clip) activation = model->activation_clip;
            head_raw += (int64_t)activation * weights[unit];
        }
        int32_t head_activation = 0;
        if (head_raw > 0) {
            int64_t rounding = INT64_C(1) << (model->head_shift - 1);
            head_activation = (int32_t)((head_raw + rounding) >> model->head_shift);
        }
        if (head_activation > model->head_clip) head_activation = model->head_clip;
        result += (int64_t)head_activation * final_weights[head];
    }
    *raw = result;
    return true;
}

static bool pack_nnue3_head(ShogiNnueModel *model) {
    if (model == NULL || model->head_weights == NULL) return false;
    if (model->head_dim != 32U || model->hidden_dim != 256U) return true;
    size_t total = (size_t)2U * model->head_dim * model->hidden_dim;
    size_t bytes = total * sizeof(int16_t);
    bytes = (bytes + 255U) & ~(size_t)255U;
    int16_t *packed = aligned_alloc(256U, bytes);
    if (packed == NULL) return false;
    /* The A64FX tile consumes four K values per SDOT step, with eight output
     * lanes in each SVE vector.  Keep one packed panel per perspective. */
    for (unsigned perspective = 0; perspective < 2U; ++perspective) {
        const int16_t *source = model->head_weights +
            (size_t)perspective * model->head_dim * model->hidden_dim;
        int16_t *destination = packed +
            (size_t)perspective * model->head_dim * model->hidden_dim;
        for (size_t block = 0; block < 64U; ++block)
            for (size_t vector = 0; vector < 4U; ++vector)
                for (size_t lane = 0; lane < 8U; ++lane)
                    for (size_t item = 0; item < 4U; ++item) {
                        size_t head = vector * 8U + lane;
                        size_t unit = block * 4U + item;
                        destination[block * 128U + vector * 32U + lane * 4U + item] =
                            source[head * 256U + unit];
                    }
    }
    free(model->head_weights_packed);
    model->head_weights_packed = packed;
    return true;
}

static bool load_nnue3(ShogiNnueModel *model, const char *path) {
    FILE *file = fopen(path, "rb");
    if (file == NULL) return false;
    char magic[5];
    uint32_t metadata[5];
    int32_t scales[3], clips[2];
    bool ok = fread(magic, 1, sizeof(magic), file) == sizeof(magic) &&
        memcmp(magic, "NNUE3", sizeof(magic)) == 0 &&
        fread(metadata, sizeof(*metadata), 5, file) == 5 &&
        metadata[0] == SHOGI_NNUE3_FORMAT_VERSION &&
        metadata[1] == SHOGI_NNUE_FEATURE_COUNT && metadata[2] > 0 &&
        metadata[3] > 0 && metadata[3] <= 128 && metadata[4] == 2 &&
        fread(scales, sizeof(*scales), 3, file) == 3 &&
        scales[0] == 256 && scales[1] == 256 && scales[2] == 1024 &&
        fread(clips, sizeof(*clips), 2, file) == 2 &&
        clips[0] > 0 && clips[0] <= INT16_MAX &&
        clips[1] > 0 && clips[1] <= INT16_MAX;
    size_t feature_bytes = 0, head_weight_bytes = 0, head_bias_bytes = 0;
    size_t final_weight_bytes = 0, final_bias_bytes = 0;
    if (ok) ok = checked_size(metadata[1], metadata[2], sizeof(int16_t), &feature_bytes) &&
        checked_size(metadata[4] * metadata[3], metadata[2], sizeof(int16_t), &head_weight_bytes) &&
        checked_size(metadata[4], metadata[3], sizeof(int64_t), &head_bias_bytes) &&
        checked_size(metadata[4], metadata[3], sizeof(int16_t), &final_weight_bytes) &&
        checked_size(metadata[4], 1, sizeof(int64_t), &final_bias_bytes);
    size_t payload_bytes = 0;
    if (ok) ok = checked_add(&payload_bytes, feature_bytes) &&
        checked_add(&payload_bytes, head_weight_bytes) &&
        checked_add(&payload_bytes, head_bias_bytes) &&
        checked_add(&payload_bytes, final_weight_bytes) &&
        checked_add(&payload_bytes, final_bias_bytes) &&
        file_has_remaining(file, payload_bytes);
    int16_t *feature_weights = ok ? malloc(feature_bytes) : NULL;
    int16_t *head_weights = ok ? malloc(head_weight_bytes) : NULL;
    int64_t *head_bias = ok ? malloc(head_bias_bytes) : NULL;
    int16_t *final_weights = ok ? malloc(final_weight_bytes) : NULL;
    int64_t *final_bias = ok ? malloc(final_bias_bytes) : NULL;
    if (ok) ok = feature_weights != NULL && head_weights != NULL &&
        head_bias != NULL && final_weights != NULL && final_bias != NULL &&
        fread(feature_weights, 1, feature_bytes, file) == feature_bytes &&
        fread(head_weights, 1, head_weight_bytes, file) == head_weight_bytes &&
        fread(head_bias, 1, head_bias_bytes, file) == head_bias_bytes &&
        fread(final_weights, 1, final_weight_bytes, file) == final_weight_bytes &&
        fread(final_bias, 1, final_bias_bytes, file) == final_bias_bytes;
    fclose(file);
    if (!ok) {
        free(feature_weights); free(head_weights); free(head_bias);
        free(final_weights); free(final_bias);
        return false;
    }
    shogi_nnue_model_destroy(model);
    model->format_version = SHOGI_NNUE3_FORMAT_VERSION;
    model->feature_count = metadata[1];
    model->hidden_dim = metadata[2];
    model->head_dim = metadata[3];
    model->feature_scale = scales[0];
    model->output_scale = scales[2];
    model->activation_clip = clips[0];
    model->head_clip = clips[1];
    model->head_shift = 8;
    model->feature_weights = feature_weights;
    model->head_weights = head_weights;
    model->head_bias = head_bias;
    model->final_weights = final_weights;
    model->final_bias = final_bias;
    if (!pack_nnue3_head(model)) {
        shogi_nnue_model_destroy(model);
        return false;
    }
    return build_output_thresholds(model);
}

static bool save_nnue3(const ShogiNnueModel *model, const char *path) {
    if (model == NULL || path == NULL || model->feature_weights == NULL ||
        model->head_weights == NULL || model->head_bias == NULL ||
        model->final_weights == NULL || model->final_bias == NULL ||
        model->feature_count != SHOGI_NNUE_FEATURE_COUNT || model->hidden_dim == 0 ||
        model->head_dim == 0 || model->feature_scale != 256 ||
        model->output_scale != 1024 || model->head_shift != 8) return false;
    FILE *file = fopen(path, "wb");
    if (file == NULL) return false;
    uint32_t metadata[5] = {SHOGI_NNUE3_FORMAT_VERSION, model->feature_count,
                            model->hidden_dim, model->head_dim, 2U};
    int32_t scales[3] = {256, 256, 1024};
    int32_t clips[2] = {model->activation_clip, model->head_clip};
    size_t feature_bytes = (size_t)model->feature_count * model->hidden_dim * sizeof(int16_t);
    size_t head_weight_bytes = (size_t)2U * model->head_dim * model->hidden_dim * sizeof(int16_t);
    size_t head_bias_bytes = (size_t)2U * model->head_dim * sizeof(int64_t);
    size_t final_weight_bytes = (size_t)2U * model->head_dim * sizeof(int16_t);
    size_t final_bias_bytes = 2U * sizeof(int64_t);
    bool ok = fwrite("NNUE3", 1, 5, file) == 5 &&
        fwrite(metadata, sizeof(*metadata), 5, file) == 5 &&
        fwrite(scales, sizeof(*scales), 3, file) == 3 &&
        fwrite(clips, sizeof(*clips), 2, file) == 2 &&
        fwrite(model->feature_weights, 1, feature_bytes, file) == feature_bytes &&
        fwrite(model->head_weights, 1, head_weight_bytes, file) == head_weight_bytes &&
        fwrite(model->head_bias, 1, head_bias_bytes, file) == head_bias_bytes &&
        fwrite(model->final_weights, 1, final_weight_bytes, file) == final_weight_bytes &&
        fwrite(model->final_bias, 1, final_bias_bytes, file) == final_bias_bytes;
    if (fclose(file) != 0) ok = false;
    return ok;
}

bool shogi_nnue_model_load(ShogiNnueModel *model, const char *path) {
    if (model == NULL || path == NULL) return false;
    FILE *file = fopen(path, "rb");
    if (file == NULL) return false;
    char magic[5];
    uint32_t metadata[4];
    int32_t scales[2];
    bool is_v1 = false, is_v2 = false, is_v3 = false;
    bool ok = fread(magic, 1, sizeof(magic), file) == sizeof(magic);
    if (ok) {
        is_v1 = memcmp(magic, NNUE_MAGIC, sizeof(magic)) == 0;
        is_v2 = memcmp(magic, "NNUE2", sizeof(magic)) == 0;
        is_v3 = memcmp(magic, "NNUE3", sizeof(magic)) == 0;
        ok = is_v1 || is_v2 || is_v3;
    }
    if (ok && is_v3) {
        fclose(file);
        return load_nnue3(model, path);
    }
    if (ok) ok =
              fread(metadata, sizeof(*metadata), 4, file) == 4 &&
              metadata[0] == (is_v2 ? SHOGI_NNUE2_FORMAT_VERSION : SHOGI_NNUE_FORMAT_VERSION) &&
              metadata[1] == SHOGI_NNUE_FEATURE_COUNT && metadata[2] > 0 &&
              fread(scales, sizeof(*scales), 2, file) == 2 &&
              scales[0] > 0 && scales[1] > 0;
    int32_t activation_clip = INT32_MAX;
    if (ok && is_v2)
        ok = fread(&activation_clip, sizeof(activation_clip), 1, file) == 1 &&
             activation_clip > 0 && activation_clip <= INT16_MAX;
    size_t feature_bytes = 0;
    if (ok) ok = checked_size(metadata[1], metadata[2], sizeof(int16_t), &feature_bytes) &&
                metadata[3] == 2U;
    size_t output_bytes = 0;
    if (ok) ok = checked_size(metadata[2], 2U, sizeof(int16_t), &output_bytes);
    size_t payload_bytes = 0;
    if (ok) ok = checked_add(&payload_bytes, feature_bytes) &&
        checked_add(&payload_bytes, output_bytes) &&
        checked_add(&payload_bytes, sizeof(int32_t)) &&
        file_has_remaining(file, payload_bytes);
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
    model->format_version = metadata[0];
    model->feature_scale = scales[0]; model->output_scale = scales[1];
    model->feature_weights = feature_weights; model->output_weights = output_weights;
    model->output_bias = bias;
    model->activation_clip = activation_clip;
    if (!build_output_thresholds(model)) {
        shogi_nnue_model_destroy(model);
        return false;
    }
    return true;
}

bool shogi_nnue_model_save(const ShogiNnueModel *model, const char *path) {
    if (model != NULL && model->format_version == SHOGI_NNUE3_FORMAT_VERSION)
        return save_nnue3(model, path);
    if (model == NULL || path == NULL || model->feature_weights == NULL ||
        model->output_weights == NULL || model->feature_count != SHOGI_NNUE_FEATURE_COUNT ||
        model->hidden_dim == 0 || model->feature_scale <= 0 || model->output_scale <= 0) return false;
    FILE *file = fopen(path, "wb");
    if (file == NULL) return false;
    bool is_v2 = model->format_version == SHOGI_NNUE2_FORMAT_VERSION;
    uint32_t metadata[4] = {is_v2 ? SHOGI_NNUE2_FORMAT_VERSION : SHOGI_NNUE_FORMAT_VERSION,
                            model->feature_count,
                            model->hidden_dim, 2U};
    int32_t scales[2] = {model->feature_scale, model->output_scale};
    size_t feature_bytes = (size_t)model->feature_count * model->hidden_dim * sizeof(int16_t);
    size_t output_bytes = (size_t)model->hidden_dim * 2U * sizeof(int16_t);
    bool ok = fwrite(is_v2 ? "NNUE2" : NNUE_MAGIC, 1, 5, file) == 5 &&
             fwrite(metadata, sizeof(*metadata), 4, file) == 4 &&
             fwrite(scales, sizeof(*scales), 2, file) == 2;
    if (ok && is_v2)
        ok = model->activation_clip > 0 && model->activation_clip <= INT16_MAX &&
             fwrite(&model->activation_clip, sizeof(model->activation_clip), 1, file) == 1;
    ok = ok &&
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

static bool shogi_nnue_accumulator_update_perspective(
    const ShogiNnueModel *model, const ShogiPosition *before,
    const ShogiPosition *after, ShogiNnueAccumulator *accumulator,
    unsigned perspective) {
    if (model == NULL || before == NULL || after == NULL || accumulator == NULL ||
        model->feature_weights == NULL || accumulator->hidden_dim != model->hidden_dim) return false;
    uint32_t old_ids[SHOGI_SQUARES + 14], new_ids[SHOGI_SQUARES + 14];
    const int16_t *removed[SHOGI_SQUARES + 14], *added[SHOGI_SQUARES + 14];
    if (perspective > SHOGI_WHITE) return false;
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
    return true;
}

static bool shogi_nnue_accumulator_update_move_local(
    const ShogiNnueModel *model, const ShogiPosition *before,
    const ShogiPosition *after, ShogiNnueAccumulator *accumulator,
    unsigned perspective) {
    if (model == NULL || before == NULL || after == NULL || accumulator == NULL ||
        model->feature_weights == NULL || accumulator->hidden_dim != model->hidden_dim ||
        perspective > SHOGI_WHITE ||
        before->king_square[perspective] != after->king_square[perspective]) return false;
    const int16_t *removed[SHOGI_SQUARES + 14];
    const int16_t *added[SHOGI_SQUARES + 14];
    size_t removed_count = 0, added_count = 0;
    uint8_t king = before->king_square[perspective];
    for (uint8_t square = 0; square < SHOGI_SQUARES; ++square) {
        uint8_t old_piece = before->board[square];
        uint8_t new_piece = after->board[square];
        if (old_piece == new_piece) continue;
        if (old_piece != SHOGI_EMPTY)
            removed[removed_count++] = model->feature_weights +
                (size_t)board_feature(king, square, old_piece,
                                      (ShogiColor)perspective) * model->hidden_dim;
        if (new_piece != SHOGI_EMPTY)
            added[added_count++] = model->feature_weights +
                (size_t)board_feature(king, square, new_piece,
                                      (ShogiColor)perspective) * model->hidden_dim;
    }
    for (unsigned color = 0; color < 2; ++color) {
        unsigned relative = color == perspective ? 0U : 1U;
        for (unsigned type = 0; type < 7; ++type) {
            unsigned old_count = before->hand[color][type];
            unsigned new_count = after->hand[color][type];
            if (old_count == new_count) continue;
            removed[removed_count++] = model->feature_weights +
                (size_t)hand_feature(relative, type, old_count) * model->hidden_dim;
            added[added_count++] = model->feature_weights +
                (size_t)hand_feature(relative, type, new_count) * model->hidden_dim;
        }
    }
    tinyshogi_add_i16_i32_rows(accumulator->sum[perspective], removed,
                               removed_count, model->hidden_dim, -1);
    tinyshogi_add_i16_i32_rows(accumulator->sum[perspective], added,
                               added_count, model->hidden_dim, 1);
    return true;
}

bool shogi_nnue_accumulator_update(const ShogiNnueModel *model,
                                   const ShogiPosition *before,
                                   const ShogiPosition *after,
                                   ShogiNnueAccumulator *accumulator) {
    return shogi_nnue_accumulator_update_perspective(model, before, after,
                                                     accumulator, 0) &&
           shogi_nnue_accumulator_update_perspective(model, before, after,
                                                     accumulator, 1);
}

static int shogi_nnue_evaluate_sum(const ShogiNnueModel *model,
                                   const int32_t *sum,
                                   ShogiColor perspective) {
    if (model->format_version == SHOGI_NNUE3_FORMAT_VERSION) {
        int64_t value = 0;
        if (!nnue3_evaluate_raw(model, sum, perspective, &value)) return 0;
        if (model->output_thresholds != NULL) {
            bool negative = value < 0;
            uint64_t magnitude = negative ? (uint64_t)(-(value + 1)) + 1U : (uint64_t)value;
            unsigned low = 0, high = 1000;
            while (low < high) {
                unsigned middle = low + (high - low) / 2U;
                if (magnitude >= model->output_thresholds[middle]) low = middle + 1U;
                else high = middle;
            }
            return negative ? -(int)low : (int)low;
        }
        return bounded_score_reference(value,
            (int64_t)model->feature_scale * model->output_scale);
    }
    int64_t value = (int64_t)model->output_bias * model->feature_scale;
    const int16_t *weights = model->output_weights + (size_t)perspective * model->hidden_dim;
    if (model->format_version == SHOGI_NNUE2_FORMAT_VERSION) {
        value += tinyshogi_dot_clip_i32_i16(sum, weights, model->hidden_dim,
                                            model->activation_clip);
    } else {
        value += tinyshogi_dot_relu_i32_i16(sum, weights, model->hidden_dim);
    }
    int64_t scale = (int64_t)model->feature_scale * model->output_scale;
    /* The thresholds are generated from the reference tanh at model-load time.
     * Runtime evaluation then needs only ten predictable integer comparisons
     * and remains bit-identical in centipawns. */
    if (model->output_thresholds != NULL) {
        bool negative = value < 0;
        uint64_t magnitude = negative ? (uint64_t)(-(value + 1)) + 1U : (uint64_t)value;
        unsigned low = 0, high = 1000;
        while (low < high) {
            unsigned middle = low + (high - low) / 2U;
            if (magnitude >= model->output_thresholds[middle])
                low = middle + 1U;
            else
                high = middle;
        }
        return negative ? -(int)low : (int)low;
    }
    /* Training targets are normalized to [-1, 1]; search consumes centipawns. */
    double normalized = scale == 0 ? (double)value : (double)value / (double)scale;
    double bounded = tanh(normalized) * 1000.0;
    if (bounded > INT_MAX) return INT_MAX;
    if (bounded < INT_MIN) return INT_MIN;
    return (int)bounded;
}

int shogi_nnue_evaluate(const ShogiNnueModel *model,
                        const ShogiNnueAccumulator *accumulator,
                        ShogiColor perspective) {
    if (model == NULL || accumulator == NULL ||
        (model->format_version == SHOGI_NNUE3_FORMAT_VERSION ?
         model->final_weights == NULL : model->output_weights == NULL) ||
        !valid_perspective(perspective) ||
        accumulator->hidden_dim != model->hidden_dim) return 0;
    return shogi_nnue_evaluate_sum(model, accumulator->sum[perspective], perspective);
}

bool shogi_nnue_state_init(ShogiNnueState *state, const ShogiNnueModel *model,
                           ShogiColor perspective) {
    if (state == NULL || model == NULL || !valid_perspective(perspective) ||
        model->hidden_dim == 0 || model->feature_weights == NULL ||
        (model->format_version == SHOGI_NNUE3_FORMAT_VERSION ?
         model->final_weights == NULL : model->output_weights == NULL)) return false;
    memset(state, 0, sizeof(*state));
    state->sum = calloc(model->hidden_dim, sizeof(*state->sum));
    if (state->sum == NULL) return false;
    state->model = model;
    state->perspective = perspective;
    state->hidden_dim = model->hidden_dim;
    return true;
}

void shogi_nnue_state_destroy(ShogiNnueState *state) {
    if (state == NULL) return;
    free(state->sum);
    memset(state, 0, sizeof(*state));
}

bool shogi_nnue_state_reset(ShogiNnueState *state, const ShogiPosition *position) {
    if (state == NULL || position == NULL || state->model == NULL || state->sum == NULL)
        return false;
    memset(state->sum, 0, state->hidden_dim * sizeof(*state->sum));
    uint32_t ids[SHOGI_SQUARES + 14];
    const int16_t *rows[SHOGI_SQUARES + 14];
    size_t count = shogi_nnue_feature_ids(position, state->perspective, ids,
                                          sizeof(ids) / sizeof(ids[0]));
    for (size_t i = 0; i < count; ++i)
        rows[i] = state->model->feature_weights + (size_t)ids[i] * state->hidden_dim;
    tinyshogi_add_i16_i32_rows(state->sum, rows, count, state->hidden_dim, 1);
    state->valid = true;
    return true;
}

static bool nnue_delta_push(uint32_t *array, uint8_t *count, uint32_t id) {
    if (*count >= SHOGI_NNUE_DELTA_MAX) return false;
    array[(*count)++] = id;
    return true;
}

static void nnue_state_apply_ids(ShogiNnueState *state, const uint32_t *ids,
                                 size_t count, int sign) {
    const int16_t *rows[SHOGI_NNUE_DELTA_MAX];
    /* Counts are bounded by nnue_delta_push; clamp as a last-line defense so a
     * corrupted count cannot overflow rows[]. */
    if (count > SHOGI_NNUE_DELTA_MAX) count = SHOGI_NNUE_DELTA_MAX;
    for (size_t i = 0; i < count; ++i)
        rows[i] = state->model->feature_weights + (size_t)ids[i] * state->hidden_dim;
    tinyshogi_add_i16_i32_rows(state->sum, rows, count, state->hidden_dim, sign);
}

bool shogi_nnue_state_apply_move(ShogiNnueState *state,
                                 const ShogiPosition *after,
                                 const ShogiUndo *undo,
                                 ShogiNnueDelta *delta) {
    if (state == NULL || after == NULL || undo == NULL || delta == NULL ||
        !state->valid || undo->valid == 0) return false;
    memset(delta, 0, sizeof(*delta));
    ShogiColor mover = (ShogiColor)undo->color;
    if (undo->moving_piece != SHOGI_EMPTY &&
        shogi_piece_type(undo->moving_piece) == SHOGI_KING &&
        mover == state->perspective) {
        delta->rebuild = 1;
        return shogi_nnue_state_reset(state, after);
    }
    uint8_t king = after->king_square[state->perspective];
    if (undo->move.from == SHOGI_SQ_NONE) {
        if (!nnue_delta_push(delta->added, &delta->added_count,
                             board_feature(king, undo->move.to,
                                           after->board[undo->move.to],
                                           state->perspective)))
            return false;
    } else {
        if (!nnue_delta_push(delta->removed, &delta->removed_count,
                             board_feature(king, undo->move.from,
                                           undo->moving_piece,
                                           state->perspective)))
            return false;
        if (!nnue_delta_push(delta->added, &delta->added_count,
                             board_feature(king, undo->move.to,
                                           after->board[undo->move.to],
                                           state->perspective)))
            return false;
        if (undo->captured_piece != SHOGI_EMPTY &&
            !nnue_delta_push(delta->removed, &delta->removed_count,
                             board_feature(king, undo->move.to,
                                           undo->captured_piece,
                                           state->perspective)))
            return false;
    }
    if (undo->hand_touched && undo->hand_index < 7) {
        unsigned relative = mover == state->perspective ? 0U : 1U;
        if (!nnue_delta_push(delta->removed, &delta->removed_count,
                             hand_feature(relative, undo->hand_index,
                                          undo->hand_before)))
            return false;
        if (!nnue_delta_push(delta->added, &delta->added_count,
                             hand_feature(relative, undo->hand_index,
                                          after->hand[mover][undo->hand_index])))
            return false;
    }
    nnue_state_apply_ids(state, delta->removed, delta->removed_count, -1);
    nnue_state_apply_ids(state, delta->added, delta->added_count, 1);
    return true;
}

bool shogi_nnue_state_unapply_move(ShogiNnueState *state,
                                   const ShogiPosition *before,
                                   const ShogiNnueDelta *delta) {
    if (state == NULL || before == NULL || delta == NULL || !state->valid) return false;
    if (delta->rebuild) return shogi_nnue_state_reset(state, before);
    nnue_state_apply_ids(state, delta->added, delta->added_count, -1);
    nnue_state_apply_ids(state, delta->removed, delta->removed_count, 1);
    return true;
}

int shogi_nnue_state_evaluate(const ShogiNnueState *state) {
    if (state == NULL || !state->valid || state->model == NULL || state->sum == NULL) return 0;
    return shogi_nnue_evaluate_sum(state->model, state->sum, state->perspective);
}

bool shogi_nnue_state_evaluate_batch(const ShogiNnueState *const *states,
                                     size_t count, int *scores) {
    if (states == NULL || scores == NULL || count == 0 || count > 6U) return false;
    const ShogiNnueState *first = states[0];
    if (first == NULL) return false;
    const ShogiNnueModel *model = first->model;
    if (model != NULL && model->format_version == SHOGI_NNUE3_FORMAT_VERSION &&
        model->hidden_dim == 256U && model->head_dim == 32U &&
        model->head_weights_packed != NULL && model->head_weights != NULL) {
        static _Thread_local _Alignas(256) int16_t positions[64U * 24U];
        static _Thread_local _Alignas(256) int64_t head_outputs[6U * 32U];
        size_t position_stride = count == 6U ? 24U : 20U;
        for (size_t index = 0; index < count; ++index) {
            const ShogiNnueState *state = states[index];
            if (state == NULL || state->model != model || state->perspective != first->perspective ||
                !state->valid || state->sum == NULL) return false;
            for (size_t block = 0; block < 64U; ++block) {
                for (size_t lane = 0; lane < 4U; ++lane) {
                    int32_t value = state->sum[block * 4U + lane];
                    if (value < 0) value = 0;
                    if (value > model->activation_clip) value = model->activation_clip;
                    positions[block * position_stride + index * 4U + lane] = (int16_t)value;
                }
            }
        }
        const int16_t *weights = model->head_weights_packed +
            (size_t)first->perspective * model->head_dim * model->hidden_dim;
        if (count == 6U)
            tinyshogi_nnue_head_gemm_i16_6x32(model->hidden_dim, weights,
                                              positions, head_outputs);
        else
            tinyshogi_nnue_head_gemm_i16_32x5(model->hidden_dim, weights,
                                              positions, head_outputs);
        const int16_t *final_weights = model->final_weights +
            (size_t)first->perspective * model->head_dim;
        const int64_t *head_bias = model->head_bias +
            (size_t)first->perspective * model->head_dim;
        int64_t final_bias = model->final_bias[first->perspective];
        for (size_t index = 0; index < count; ++index) {
            int64_t value = final_bias;
            for (size_t head = 0; head < 32U; ++head) {
                int64_t raw = head_bias[head] + head_outputs[index * 32U + head];
                int32_t activation = raw > 0 ? (int32_t)((raw + 128) >> 8) : 0;
                if (activation > model->head_clip) activation = model->head_clip;
                value += (int64_t)activation * final_weights[head];
            }
            bool negative = value < 0;
            uint64_t magnitude = negative ? (uint64_t)(-(value + 1)) + 1U : (uint64_t)value;
            unsigned low = 0, high = 1000;
            while (low < high) {
                unsigned middle = low + (high - low) / 2U;
                if (magnitude >= model->output_thresholds[middle]) low = middle + 1U;
                else high = middle;
            }
            scores[index] = negative ? -(int)low : (int)low;
        }
        return true;
    }
    for (size_t index = 0; index < count; ++index) {
        if (states[index] == NULL) return false;
        scores[index] = shogi_nnue_state_evaluate(states[index]);
    }
    return true;
}

int shogi_nnue_evaluate_position(const ShogiNnueModel *model,
                                 const ShogiPosition *position,
                                 ShogiColor perspective) {
    if (model == NULL || position == NULL ||
        !valid_perspective(perspective)) return 0;
    /* Search evaluates positions from worker threads. Reuse one scratch
     * accumulator per thread to keep the hot path free of malloc/free while
     * retaining thread safety and the public accumulator API. */
    static _Thread_local ShogiNnueAccumulator scratch;
    static _Thread_local const ShogiNnueModel *scratch_model;
    static _Thread_local const int16_t *scratch_feature_weights;
    static _Thread_local const int16_t *scratch_output_weights;
    static _Thread_local uint64_t scratch_hash;
    static _Thread_local unsigned scratch_valid_perspectives;
    static _Thread_local ShogiPosition scratch_position;
    static _Thread_local bool scratch_position_valid;
    if (scratch.hidden_dim != model->hidden_dim ||
        scratch.sum[0] == NULL || scratch.sum[1] == NULL) {
        shogi_nnue_accumulator_destroy(&scratch);
        if (!shogi_nnue_accumulator_init(&scratch, model->hidden_dim)) {
            scratch_valid_perspectives = 0;
            scratch_position_valid = false;
            return 0;
        }
        scratch_valid_perspectives = 0;
        scratch_position_valid = false;
    }
    if (scratch_model != model || scratch_feature_weights != model->feature_weights ||
        scratch_output_weights != model->output_weights || scratch_hash != position->hash)
        scratch_valid_perspectives = 0;
    if ((scratch_valid_perspectives & (1U << perspective)) != 0U &&
        scratch_model == model &&
        scratch_feature_weights == model->feature_weights &&
        scratch_output_weights == model->output_weights &&
        scratch_hash == position->hash && scratch_position_valid)
        return shogi_nnue_evaluate(model, &scratch, perspective);

    /* Search normally evaluates a child immediately after its parent.  When
     * that perspective is already resident, update only the feature rows
     * changed by the move instead of rebuilding all board and hand rows. */
    if ((scratch_valid_perspectives & (1U << perspective)) != 0U &&
        scratch_model == model && scratch_feature_weights == model->feature_weights &&
        scratch_output_weights == model->output_weights && scratch_position_valid &&
        shogi_nnue_accumulator_update_move_local(model, &scratch_position,
                                                 position, &scratch,
                                                 (unsigned)perspective)) {
        scratch_hash = position->hash;
        cache_feature_position(&scratch_position, position);
        scratch_position_valid = true;
        return shogi_nnue_evaluate(model, &scratch, perspective);
    }
    if (!shogi_nnue_accumulator_build_perspective(model, position, &scratch, perspective))
        return 0;
    scratch_model = model;
    scratch_feature_weights = model->feature_weights;
    scratch_output_weights = model->output_weights;
    scratch_hash = position->hash;
    cache_feature_position(&scratch_position, position);
    scratch_position_valid = true;
    scratch_valid_perspectives |= 1U << perspective;
    return shogi_nnue_evaluate(model, &scratch, perspective);
}
