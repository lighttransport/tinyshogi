#ifndef TINYSHOGI_NNUE_H
#define TINYSHOGI_NNUE_H

#include "shogi.h"

#include <stdbool.h>
#include <stddef.h>
#include <stdint.h>

#define SHOGI_NNUE_FORMAT_VERSION 1U
#define SHOGI_NNUE2_FORMAT_VERSION 2U
#define SHOGI_NNUE3_FORMAT_VERSION 3U
#define SHOGI_NNUE_BOARD_FEATURES (81U * 28U * 81U)
#define SHOGI_NNUE_HAND_FEATURES (2U * 7U * 19U)
#define SHOGI_NNUE_FEATURE_COUNT (SHOGI_NNUE_BOARD_FEATURES + SHOGI_NNUE_HAND_FEATURES)
#define SHOGI_NNUE_DEFAULT_HIDDEN 256U

typedef struct {
    uint32_t format_version;
    uint32_t feature_count;
    uint32_t hidden_dim;
    int32_t feature_scale;
    int32_t output_scale;
    int16_t *feature_weights;
    int16_t *output_weights;
    uint32_t head_dim;
    int16_t *head_weights;
    int16_t *head_weights_packed;
    int64_t *head_bias;
    int16_t *final_weights;
    int64_t *final_bias;
    int32_t head_clip;
    int32_t head_shift;
    int32_t output_bias;
    int32_t activation_clip;
    uint64_t *output_thresholds;
} ShogiNnueModel;

typedef struct {
    uint32_t hidden_dim;
    int32_t *sum[2];
} ShogiNnueAccumulator;

typedef struct {
    const ShogiNnueModel *model;
    ShogiColor perspective;
    uint32_t hidden_dim;
    int32_t *sum;
    bool valid;
} ShogiNnueState;

typedef struct {
    uint32_t removed[4];
    uint32_t added[4];
    uint8_t removed_count;
    uint8_t added_count;
    uint8_t rebuild;
} ShogiNnueDelta;

void shogi_nnue_model_init(ShogiNnueModel *model);
void shogi_nnue_model_destroy(ShogiNnueModel *model);
bool shogi_nnue_model_init_default(ShogiNnueModel *model, uint32_t hidden_dim);
bool shogi_nnue_model_load(ShogiNnueModel *model, const char *path);
bool shogi_nnue_model_save(const ShogiNnueModel *model, const char *path);

bool shogi_nnue_accumulator_init(ShogiNnueAccumulator *accumulator,
                                 uint32_t hidden_dim);
void shogi_nnue_accumulator_destroy(ShogiNnueAccumulator *accumulator);
bool shogi_nnue_accumulator_build(const ShogiNnueModel *model,
                                  const ShogiPosition *position,
                                  ShogiNnueAccumulator *accumulator);
bool shogi_nnue_accumulator_update(const ShogiNnueModel *model,
                                   const ShogiPosition *before,
                                   const ShogiPosition *after,
                                   ShogiNnueAccumulator *accumulator);
int shogi_nnue_evaluate(const ShogiNnueModel *model,
                        const ShogiNnueAccumulator *accumulator,
                        ShogiColor perspective);
int shogi_nnue_evaluate_position(const ShogiNnueModel *model,
                                 const ShogiPosition *position,
                                 ShogiColor perspective);
bool shogi_nnue_state_init(ShogiNnueState *state, const ShogiNnueModel *model,
                           ShogiColor perspective);
void shogi_nnue_state_destroy(ShogiNnueState *state);
bool shogi_nnue_state_reset(ShogiNnueState *state, const ShogiPosition *position);
bool shogi_nnue_state_apply_move(ShogiNnueState *state,
                                 const ShogiPosition *position_after,
                                 const ShogiUndo *undo,
                                 ShogiNnueDelta *delta);
bool shogi_nnue_state_unapply_move(ShogiNnueState *state,
                                   const ShogiPosition *position_before,
                                   const ShogiNnueDelta *delta);
int shogi_nnue_state_evaluate(const ShogiNnueState *state);
bool shogi_nnue_state_evaluate_batch(const ShogiNnueState *const *states,
                                     size_t count, int *scores);

/* Return the active sparse features for one perspective. */
size_t shogi_nnue_feature_ids(const ShogiPosition *position,
                              ShogiColor perspective,
                              uint32_t *features, size_t capacity);

#endif
