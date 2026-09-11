#define _POSIX_C_SOURCE 200809L

/*
 * Clean-room reader for the HalfKP 256x2-32-32 network used by the local
 * YaneuraOu nn.bin.  This file deliberately has no YaneuraOu source
 * dependency: the format is parsed from its documented binary invariants and
 * the evaluator is implemented against TinyShogi's public evaluator ABI.
 */

#include "eval.h"
#include "shogi.h"

#include <limits.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#define FEATURE_COUNT 125388U
#define ACCUMULATOR_DIM 256U
#define NETWORK_INPUT_DIM 512U
#define HIDDEN_DIM 32U
#define MAX_DESCRIPTION 4096U

typedef struct {
    unsigned fv_scale;
    int16_t *feature_bias;
    int16_t *feature_weights;
    int32_t bias1[HIDDEN_DIM];
    int8_t weights1[HIDDEN_DIM][NETWORK_INPUT_DIM];
    int32_t bias2[HIDDEN_DIM];
    int8_t weights2[HIDDEN_DIM][HIDDEN_DIM];
    int32_t bias3;
    int8_t weights3[HIDDEN_DIM];
} DirectModel;

typedef struct {
    DirectModel model;
} DirectEvaluator;

typedef struct {
    const DirectEvaluator *evaluator;
    int32_t accumulators[2][ACCUMULATOR_DIM];
    ShogiColor side;
    ShogiColor perspective;
} DirectState;

static bool read_exact(FILE *file, void *destination, size_t size) {
    return size == 0 || fread(destination, 1, size, file) == size;
}

static bool read_u32(FILE *file, uint32_t *value) {
    unsigned char bytes[4];
    if (!read_exact(file, bytes, sizeof(bytes))) return false;
    *value = (uint32_t)bytes[0] |
             ((uint32_t)bytes[1] << 8) |
             ((uint32_t)bytes[2] << 16) |
             ((uint32_t)bytes[3] << 24);
    return true;
}

static bool read_u64(FILE *file, uint64_t *value) {
    unsigned char bytes[8];
    if (!read_exact(file, bytes, sizeof(bytes))) return false;
    *value = (uint64_t)bytes[0] |
             ((uint64_t)bytes[1] << 8) |
             ((uint64_t)bytes[2] << 16) |
             ((uint64_t)bytes[3] << 24) |
             ((uint64_t)bytes[4] << 32) |
             ((uint64_t)bytes[5] << 40) |
             ((uint64_t)bytes[6] << 48) |
             ((uint64_t)bytes[7] << 56);
    return true;
}

static void direct_model_destroy(DirectModel *model) {
    if (model == NULL) return;
    free(model->feature_bias);
    free(model->feature_weights);
    memset(model, 0, sizeof(*model));
}

static bool description_is_supported(const char *description) {
    return strstr(description, "Features=HalfKP(Friend)[125388->256x2]") != NULL &&
           strstr(description, "AffineTransform[1<-32]") != NULL &&
           strstr(description, "AffineTransform[32<-32]") != NULL &&
           strstr(description, "AffineTransform[32<-512]") != NULL;
}

static bool direct_model_load(DirectModel *model, const char *path) {
    if (model == NULL || path == NULL || path[0] == '\0') return false;
    memset(model, 0, sizeof(*model));
    FILE *file = fopen(path, "rb");
    if (file == NULL) return false;

    bool ok = false;
    uint64_t file_hash;
    uint32_t description_size = 0;
    char *description = NULL;
    if (!read_u64(file, &file_hash) || !read_u32(file, &description_size) ||
        description_size == 0 || description_size > MAX_DESCRIPTION) goto done;
    description = malloc((size_t)description_size + 1U);
    if (description == NULL || !read_exact(file, description, description_size)) goto done;
    description[description_size] = '\0';
    if (!description_is_supported(description)) goto done;

    uint32_t feature_hash;
    uint32_t network_hash;
    if (!read_u32(file, &feature_hash)) goto done;

    size_t feature_bias_bytes = ACCUMULATOR_DIM * sizeof(int16_t);
    size_t feature_weight_count = (size_t)FEATURE_COUNT * ACCUMULATOR_DIM;
    size_t feature_weight_bytes = feature_weight_count * sizeof(int16_t);
    model->feature_bias = malloc(feature_bias_bytes);
    model->feature_weights = malloc(feature_weight_bytes);
    if (model->feature_bias == NULL || model->feature_weights == NULL ||
        !read_exact(file, model->feature_bias, feature_bias_bytes) ||
        !read_exact(file, model->feature_weights, feature_weight_bytes) ||
        !read_u32(file, &network_hash) ||
        !read_exact(file, model->bias1, sizeof(model->bias1)) ||
        !read_exact(file, model->weights1, sizeof(model->weights1)) ||
        !read_exact(file, model->bias2, sizeof(model->bias2)) ||
        !read_exact(file, model->weights2, sizeof(model->weights2)) ||
        !read_exact(file, &model->bias3, sizeof(model->bias3)) ||
        !read_exact(file, model->weights3, sizeof(model->weights3))) goto done;

    /* Reject trailing data: accepting a different network silently is worse
     * than refusing to start with a clear evaluator-load failure. */
    unsigned char trailing;
    if (fread(&trailing, 1, 1, file) != 0) goto done;
    (void)file_hash;
    (void)feature_hash;
    (void)network_hash;
    ok = true;
done:
    free(description);
    fclose(file);
    if (!ok) direct_model_destroy(model);
    return ok;
}

static int piece_class(ShogiPieceType type) {
    /* Nine non-king classes; promoted minor pieces share their gold class. */
    static const int classes[15] = {
        0, 0, 1, 2, 3, 4, 5, 7, 8, 4, 4, 4, 4, 6, 8
    };
    return type >= 0 && type < 15 ? classes[type] : -1;
}

static int oriented_square(int square, ShogiColor perspective) {
    int row = square / SHOGI_BOARD_SIZE;
    int column = square % SHOGI_BOARD_SIZE;
    /* TinyShogi's row/column order is 9..1 by file.  Rotate the board for
     * the white perspective after converting to YaneuraOu's square order. */
    int yaneura_square = (SHOGI_BOARD_SIZE - 1 - column) * SHOGI_BOARD_SIZE + row;
    return perspective == SHOGI_BLACK ? yaneura_square : 80 - yaneura_square;
}

static int feature_index(const ShogiPosition *position, ShogiColor perspective,
                         int square, ShogiPieceType type, ShogiColor owner) {
    int class = piece_class(type);
    if (class < 0 || type == SHOGI_KING) return -1;
    int king = oriented_square(position->king_square[perspective], perspective);
    int piece = class * 2 + (owner == perspective ? 0 : 1);
    return king * 1548 + 90 + piece * 81 + oriented_square(square, perspective);
}

static unsigned hand_feature_index(const ShogiPosition *position,
                                   ShogiColor perspective, ShogiColor owner,
                                   unsigned type, unsigned count) {
    static const unsigned hand_base[7] = {1, 39, 49, 59, 69, 79, 85};
    static const unsigned hand_delta[7] = {19, 5, 5, 5, 5, 3, 3};
    unsigned king = (unsigned)oriented_square(
        position->king_square[perspective], perspective);
    return king * 1548U + hand_base[type] +
           (owner == perspective ? 0U : hand_delta[type]) + count;
}

static void add_feature_row(const DirectEvaluator *evaluator,
                            int32_t *accumulator, unsigned index,
                            int direction) {
    if (index >= FEATURE_COUNT) return;
    const int16_t *weights = evaluator->model.feature_weights +
        (size_t)index * ACCUMULATOR_DIM;
    for (unsigned output = 0; output < ACCUMULATOR_DIM; ++output)
        accumulator[output] += direction * weights[output];
}

static void accumulator_for(const DirectEvaluator *evaluator,
                            const ShogiPosition *position,
                            ShogiColor perspective, int32_t *accumulator) {
    for (unsigned output = 0; output < ACCUMULATOR_DIM; ++output)
        accumulator[output] = evaluator->model.feature_bias[output];
    for (int square = 0; square < SHOGI_SQUARES; ++square) {
        uint8_t piece = position->board[square];
        if (piece == SHOGI_EMPTY || shogi_piece_type(piece) == SHOGI_KING) continue;
        int index = feature_index(position, perspective, square,
                                  shogi_piece_type(piece), shogi_piece_color(piece));
        if (index < 0 || (unsigned)index >= FEATURE_COUNT) continue;
        add_feature_row(evaluator, accumulator, (unsigned)index, 1);
    }

    for (unsigned owner = 0; owner < 2; ++owner) {
        for (unsigned type = 0; type < 7; ++type) {
            for (unsigned count = 0; count < position->hand[owner][type]; ++count) {
                unsigned index = hand_feature_index(position, perspective,
                    (ShogiColor)owner, type, count);
                add_feature_row(evaluator, accumulator, index, 1);
            }
        }
    }
}

static int clipped(int64_t value, int limit) {
    if (value < 0) return 0;
    if (value > limit) return limit;
    return (int)value;
}

static int network_evaluate(const DirectModel *model,
                            const int32_t *accumulators,
                            ShogiColor side) {
    int8_t input[NETWORK_INPUT_DIM];
    for (unsigned index = 0; index < ACCUMULATOR_DIM; ++index) {
        input[index] = (int8_t)clipped(
            accumulators[(size_t)side * ACCUMULATOR_DIM + index], 127);
        input[ACCUMULATOR_DIM + index] =
            (int8_t)clipped(accumulators[(size_t)(side ^ 1U) *
                                         ACCUMULATOR_DIM + index], 127);
    }

    int32_t hidden1[HIDDEN_DIM];
    for (unsigned output = 0; output < HIDDEN_DIM; ++output) {
        int64_t value = model->bias1[output];
        for (unsigned index = 0; index < NETWORK_INPUT_DIM; ++index)
            value += (int64_t)model->weights1[output][index] * input[index];
        hidden1[output] = clipped(value >> 6, 127);
    }
    int32_t hidden2[HIDDEN_DIM];
    for (unsigned output = 0; output < HIDDEN_DIM; ++output) {
        int64_t value = model->bias2[output];
        for (unsigned index = 0; index < HIDDEN_DIM; ++index)
            value += (int64_t)model->weights2[output][index] * hidden1[index];
        hidden2[output] = clipped(value >> 6, 127);
    }
    int64_t output = model->bias3;
    for (unsigned index = 0; index < HIDDEN_DIM; ++index)
        output += (int64_t)model->weights3[index] * hidden2[index];
    return (int)(output / model->fv_scale);
}

static int direct_evaluate(void *userdata, const ShogiPosition *position,
                           ShogiColor perspective) {
    DirectEvaluator *evaluator = userdata;
    if (evaluator == NULL || position == NULL) return 0;
    int32_t accumulators[2][ACCUMULATOR_DIM];
    accumulator_for(evaluator, position, SHOGI_BLACK, accumulators[0]);
    accumulator_for(evaluator, position, SHOGI_WHITE, accumulators[1]);
    int score = network_evaluate(&evaluator->model, &accumulators[0][0],
                                 position->side);
    return position->side == perspective ? score : -score;
}

static ShogiPieceType promoted_piece_type(ShogiPieceType type) {
    switch (type) {
    case SHOGI_PAWN: return SHOGI_PRO_PAWN;
    case SHOGI_LANCE: return SHOGI_PRO_LANCE;
    case SHOGI_KNIGHT: return SHOGI_PRO_KNIGHT;
    case SHOGI_SILVER: return SHOGI_PRO_SILVER;
    case SHOGI_BISHOP: return SHOGI_HORSE;
    case SHOGI_ROOK: return SHOGI_DRAGON;
    default: return type;
    }
}

static void update_board_feature(DirectState *state,
                                 const ShogiPosition *position,
                                 ShogiColor perspective, int square,
                                 uint8_t piece, int direction) {
    if (piece == SHOGI_EMPTY || shogi_piece_type(piece) == SHOGI_KING) return;
    int index = feature_index(position, perspective, square,
                              shogi_piece_type(piece), shogi_piece_color(piece));
    if (index >= 0)
        add_feature_row(state->evaluator, state->accumulators[perspective],
                        (unsigned)index, direction);
}

static bool direct_state_update(DirectState *state,
                                const ShogiPosition *position,
                                const ShogiUndo *undo, bool forward) {
    if (state == NULL || position == NULL || undo == NULL || undo->valid == 0)
        return false;
    ShogiColor mover = (ShogiColor)undo->color;
    bool king_move = shogi_piece_type(undo->moving_piece) == SHOGI_KING;
    ShogiPieceType moved_type = shogi_piece_type(undo->moving_piece);
    if (undo->move.promote) moved_type = promoted_piece_type(moved_type);
    uint8_t moved_after = shogi_piece(mover, moved_type);

    for (unsigned view = 0; view < 2; ++view) {
        ShogiColor perspective = (ShogiColor)view;
        if (king_move && perspective == mover) {
            accumulator_for(state->evaluator, position, perspective,
                            state->accumulators[view]);
            continue;
        }
        int old_direction = forward ? -1 : 1;
        int new_direction = -old_direction;
        if (undo->move.from == SHOGI_SQ_NONE) {
            update_board_feature(state, position, perspective, undo->move.to,
                                 moved_after, new_direction);
        } else {
            update_board_feature(state, position, perspective, undo->move.from,
                                 undo->moving_piece, old_direction);
            update_board_feature(state, position, perspective, undo->move.to,
                                 moved_after, new_direction);
            update_board_feature(state, position, perspective, undo->move.to,
                                 undo->captured_piece, old_direction);
        }
        if (undo->hand_touched && undo->hand_index < 7) {
            unsigned count = undo->move.from == SHOGI_SQ_NONE ?
                (unsigned)undo->hand_before - 1U : (unsigned)undo->hand_before;
            unsigned index = hand_feature_index(position, perspective, mover,
                                                undo->hand_index, count);
            int hand_direction = undo->move.from == SHOGI_SQ_NONE ?
                old_direction : new_direction;
            add_feature_row(state->evaluator, state->accumulators[view], index,
                            hand_direction);
        }
    }
    state->side = position->side;
    return true;
}

static void *direct_state_create(void *userdata, const ShogiPosition *position,
                                 ShogiColor perspective) {
    DirectEvaluator *evaluator = userdata;
    if (evaluator == NULL || position == NULL) return NULL;
    DirectState *state = calloc(1, sizeof(*state));
    if (state == NULL) return NULL;
    state->evaluator = evaluator;
    state->side = position->side;
    state->perspective = perspective;
    accumulator_for(evaluator, position, SHOGI_BLACK, state->accumulators[0]);
    accumulator_for(evaluator, position, SHOGI_WHITE, state->accumulators[1]);
    return state;
}

static void direct_state_destroy(void *opaque) { free(opaque); }

static bool direct_state_make(void *opaque, const ShogiPosition *after,
                              const ShogiUndo *undo) {
    return direct_state_update(opaque, after, undo, true);
}

static bool direct_state_unmake(void *opaque, const ShogiPosition *before,
                                const ShogiUndo *undo) {
    return direct_state_update(opaque, before, undo, false);
}

static int direct_state_score(const void *opaque) {
    const DirectState *state = opaque;
    if (state == NULL) return 0;
    int score = network_evaluate(&state->evaluator->model,
                                 &state->accumulators[0][0], state->side);
    return state->side == state->perspective ? score : -score;
}

static void direct_destroy(void *userdata) {
    DirectEvaluator *evaluator = userdata;
    if (evaluator == NULL) return;
    direct_model_destroy(&evaluator->model);
    free(evaluator);
}

static void *direct_create(const char *config) {
    const char *scale_text = config != NULL && config[0] != '\0' ? config :
        getenv("YANEURAOU_FV_SCALE");
    unsigned scale = 16;
    if (scale_text != NULL && scale_text[0] != '\0') {
        char *end;
        unsigned long parsed = strtoul(scale_text, &end, 10);
        if (*end != '\0' || parsed < 1 || parsed > 128) return NULL;
        scale = (unsigned)parsed;
    }
    const char *path;
#ifdef TINYSHOGI_WEB_NNUE
    path = "/nn.bin";
#else
    path = getenv("YANEURAOU_NN_BIN");
    if (path == NULL || path[0] == '\0') path = "eval/nn.bin";
#endif
    DirectEvaluator *evaluator = calloc(1, sizeof(*evaluator));
    if (evaluator == NULL || !direct_model_load(&evaluator->model, path)) {
        direct_destroy(evaluator);
        return NULL;
    }
    evaluator->model.fv_scale = scale;
    return evaluator;
}

static const TinyShogiEvalPlugin plugin = {
    TINYSHOGI_EVAL_ABI_VERSION,
    sizeof(TinyShogiEvalPlugin),
    "yaneuraou-nnue-direct",
    direct_create,
    direct_destroy,
    direct_evaluate,
    direct_state_create,
    direct_state_destroy,
    direct_state_make,
    direct_state_unmake,
    direct_state_score
};

const TinyShogiEvalPlugin *tinyshogi_eval_plugin(void) { return &plugin; }
