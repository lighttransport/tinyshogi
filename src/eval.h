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

typedef struct {
    void *userdata;
    TinyShogiEvalFunction evaluate;
    void (*destroy)(void *userdata);
    const char *name;
    void *module_handle;
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
bool shogi_evaluator_active(const ShogiEvaluator *evaluator);
int shogi_evaluator_score(const ShogiEvaluator *evaluator,
                          const ShogiPosition *position,
                          ShogiColor perspective);
const char *shogi_evaluator_error(void);

#endif
