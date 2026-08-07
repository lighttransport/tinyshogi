#ifndef TINYSHOGI_NNUE_H
#define TINYSHOGI_NNUE_H

#include "shogi.h"

#include <stdbool.h>
#include <stddef.h>
#include <stdint.h>

#define SHOGI_NNUE_FORMAT_VERSION 1U
#define SHOGI_NNUE_BOARD_FEATURES (81U * 28U * 81U)
#define SHOGI_NNUE_HAND_FEATURES (2U * 7U * 19U)
#define SHOGI_NNUE_FEATURE_COUNT (SHOGI_NNUE_BOARD_FEATURES + SHOGI_NNUE_HAND_FEATURES)
#define SHOGI_NNUE_DEFAULT_HIDDEN 256U

typedef struct {
    uint32_t feature_count;
    uint32_t hidden_dim;
    int32_t feature_scale;
    int32_t output_scale;
    int16_t *feature_weights;
    int16_t *output_weights;
    int32_t output_bias;
} ShogiNnueModel;

typedef struct {
    uint32_t hidden_dim;
    int32_t *sum[2];
} ShogiNnueAccumulator;

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

/* Return the active sparse features for one perspective. */
size_t shogi_nnue_feature_ids(const ShogiPosition *position,
                              ShogiColor perspective,
                              uint32_t *features, size_t capacity);

#endif
