#ifndef TINYSHOGI_EVAL_H
#define TINYSHOGI_EVAL_H

#include "shogi.h"

#include <stdbool.h>
#include <stddef.h>
#include <stdint.h>

#define TINYSHOGI_EVAL_ABI_VERSION 1U
#define TINYSHOGI_EVAL_PLUGIN_SYMBOL "tinyshogi_eval_plugin"

typedef int (*TinyShogiEvalFunction)(void *userdata,
                                     const ShogiPosition *position,
                                     ShogiColor perspective);

typedef void *(*TinyShogiEvalStateCreate)(void *userdata,
                                          const ShogiPosition *position,
                                          ShogiColor perspective);
typedef void (*TinyShogiEvalStateDestroy)(void *state);
typedef bool (*TinyShogiEvalStateMove)(void *state,
                                       const ShogiPosition *position,
                                       const ShogiUndo *undo);
typedef int (*TinyShogiEvalStateScore)(const void *state);
typedef bool (*TinyShogiEvalStateScoreBatch)(const void *const *states,
                                             size_t count, int *scores);
typedef bool (*TinyShogiEvalStateRewind)(void *state,
                                         const ShogiPosition *root);

typedef struct {
    void *userdata;
    TinyShogiEvalFunction evaluate;
    void (*destroy)(void *userdata);
    const char *name;
    void *module_handle;
    TinyShogiEvalStateCreate state_create;
    TinyShogiEvalStateDestroy state_destroy;
    TinyShogiEvalStateMove state_make;
    TinyShogiEvalStateMove state_unmake;
    TinyShogiEvalStateScore state_score;
    TinyShogiEvalStateScoreBatch state_score_batch;
    TinyShogiEvalStateRewind state_rewind;
    unsigned state_score_batch_size;
} ShogiEvaluator;

/* Public ABI implemented by an external evaluator shared library. */
typedef struct {
    uint32_t abi_version;
    uint32_t struct_size;
    const char *name;
    void *(*create)(const char *config);
    void (*destroy)(void *userdata);
    TinyShogiEvalFunction evaluate;
} TinyShogiEvalPlugin;

typedef const TinyShogiEvalPlugin *(*TinyShogiEvalPluginGetter)(void);

void shogi_evaluator_init(ShogiEvaluator *evaluator);
void shogi_evaluator_destroy(ShogiEvaluator *evaluator);
bool shogi_evaluator_load(ShogiEvaluator *evaluator, const char *path,
                          const char *config);
bool shogi_evaluator_set(ShogiEvaluator *evaluator, void *userdata,
                         TinyShogiEvalFunction evaluate,
                         void (*destroy)(void *userdata), const char *name);
bool shogi_evaluator_set_state_callbacks(ShogiEvaluator *evaluator,
                                         TinyShogiEvalStateCreate create,
                                         TinyShogiEvalStateDestroy destroy,
                                         TinyShogiEvalStateMove make,
                                         TinyShogiEvalStateMove unmake,
                                         TinyShogiEvalStateScore score);
bool shogi_evaluator_set_state_batch_callback(ShogiEvaluator *evaluator,
                                              TinyShogiEvalStateScoreBatch batch,
                                              unsigned preferred_batch_size);
bool shogi_evaluator_set_state_rewind_callback(ShogiEvaluator *evaluator,
                                               TinyShogiEvalStateRewind rewind);
bool shogi_evaluator_active(const ShogiEvaluator *evaluator);
int shogi_evaluator_score(const ShogiEvaluator *evaluator,
                          const ShogiPosition *position,
                          ShogiColor perspective);
void *shogi_evaluator_state_create(const ShogiEvaluator *evaluator,
                                   const ShogiPosition *position,
                                   ShogiColor perspective);
void shogi_evaluator_state_destroy(const ShogiEvaluator *evaluator, void *state);
bool shogi_evaluator_state_make(const ShogiEvaluator *evaluator, void *state,
                                const ShogiPosition *after, const ShogiUndo *undo);
bool shogi_evaluator_state_unmake(const ShogiEvaluator *evaluator, void *state,
                                  const ShogiPosition *before, const ShogiUndo *undo);
bool shogi_evaluator_state_rewind(const ShogiEvaluator *evaluator, void *state,
                                  const ShogiPosition *root);
int shogi_evaluator_state_score(const ShogiEvaluator *evaluator, const void *state);
bool shogi_evaluator_state_score_batch(const ShogiEvaluator *evaluator,
                                       const void *const *states, size_t count,
                                       int *scores);
const char *shogi_evaluator_error(void);

#endif
