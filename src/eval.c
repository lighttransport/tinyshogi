#define _POSIX_C_SOURCE 200809L

#include "eval.h"

#include <dlfcn.h>
#include <stdio.h>
#include <string.h>

static _Thread_local char evaluator_error[256];

static void set_error(const char *message) {
    if (message == NULL) message = "unknown evaluator error";
    snprintf(evaluator_error, sizeof(evaluator_error), "%s", message);
}

static void set_dl_error(const char *prefix) {
    const char *detail = dlerror();
    if (detail == NULL) detail = "unknown dynamic loader error";
    snprintf(evaluator_error, sizeof(evaluator_error), "%s: %s", prefix, detail);
}

void shogi_evaluator_init(ShogiEvaluator *evaluator) {
    if (evaluator != NULL) memset(evaluator, 0, sizeof(*evaluator));
}

void shogi_evaluator_destroy(ShogiEvaluator *evaluator) {
    if (evaluator == NULL) return;
    if (evaluator->destroy != NULL) evaluator->destroy(evaluator->userdata);
    if (evaluator->module_handle != NULL) dlclose(evaluator->module_handle);
    memset(evaluator, 0, sizeof(*evaluator));
}

bool shogi_evaluator_set(ShogiEvaluator *evaluator, void *userdata,
                         TinyShogiEvalFunction evaluate,
                         void (*destroy)(void *userdata), const char *name) {
    if (evaluator == NULL || evaluate == NULL) {
        set_error("evaluator callback is missing");
        return false;
    }
    shogi_evaluator_destroy(evaluator);
    evaluator->userdata = userdata;
    evaluator->evaluate = evaluate;
    evaluator->destroy = destroy;
    evaluator->name = name;
    evaluator->module_handle = NULL;
    evaluator_error[0] = '\0';
    return true;
}

bool shogi_evaluator_set_state_callbacks(ShogiEvaluator *evaluator,
                                         TinyShogiEvalStateCreate create,
                                         TinyShogiEvalStateDestroy destroy,
                                         TinyShogiEvalStateMove make,
                                         TinyShogiEvalStateMove unmake,
                                         TinyShogiEvalStateScore score) {
    if (!shogi_evaluator_active(evaluator) || create == NULL || destroy == NULL ||
        make == NULL || unmake == NULL || score == NULL) {
        set_error("stateful evaluator callbacks are incomplete");
        return false;
    }
    evaluator->state_create = create;
    evaluator->state_destroy = destroy;
    evaluator->state_make = make;
    evaluator->state_unmake = unmake;
    evaluator->state_score = score;
    evaluator->state_score_batch = NULL;
    evaluator->state_rewind = NULL;
    evaluator->state_score_batch_size = 0;
    evaluator_error[0] = '\0';
    return true;
}

bool shogi_evaluator_set_state_batch_callback(ShogiEvaluator *evaluator,
                                              TinyShogiEvalStateScoreBatch batch,
                                              unsigned preferred_batch_size) {
    if (!shogi_evaluator_active(evaluator) || batch == NULL || preferred_batch_size == 0) {
        set_error("state batch evaluator callback is incomplete");
        return false;
    }
    evaluator->state_score_batch = batch;
    evaluator->state_score_batch_size = preferred_batch_size;
    evaluator_error[0] = '\0';
    return true;
}

bool shogi_evaluator_set_state_rewind_callback(ShogiEvaluator *evaluator,
                                               TinyShogiEvalStateRewind rewind) {
    if (!shogi_evaluator_active(evaluator) || rewind == NULL ||
        evaluator->state_create == NULL) {
        set_error("state rewind evaluator callback is incomplete");
        return false;
    }
    evaluator->state_rewind = rewind;
    evaluator_error[0] = '\0';
    return true;
}

bool shogi_evaluator_load(ShogiEvaluator *evaluator, const char *path,
                          const char *config) {
    if (evaluator == NULL || path == NULL || path[0] == '\0') {
        set_error("evaluator plugin path is empty");
        return false;
    }
    dlerror();
    void *module = dlopen(path, RTLD_NOW | RTLD_LOCAL);
    if (module == NULL) {
        set_dl_error("cannot load evaluator plugin");
        return false;
    }
    union {
        void *object;
        TinyShogiEvalPluginGetter function;
    } symbol;
    symbol.object = dlsym(module, TINYSHOGI_EVAL_PLUGIN_SYMBOL);
    TinyShogiEvalPluginGetter getter = symbol.function;
    const char *lookup_error = dlerror();
    if (lookup_error != NULL || getter == NULL) {
        snprintf(evaluator_error, sizeof(evaluator_error),
                 "plugin is missing %s", TINYSHOGI_EVAL_PLUGIN_SYMBOL);
        dlclose(module);
        return false;
    }
    const TinyShogiEvalPlugin *plugin = getter();
    if (plugin == NULL || plugin->abi_version != TINYSHOGI_EVAL_ABI_VERSION ||
        plugin->struct_size < TINYSHOGI_EVAL_PLUGIN_V1_SIZE ||
        plugin->evaluate == NULL) {
        set_error("evaluator plugin ABI or callback is invalid");
        dlclose(module);
        return false;
    }
    void *userdata = plugin->create == NULL ? NULL : plugin->create(config);
    if (plugin->create != NULL && userdata == NULL) {
        set_error("evaluator plugin initialization failed");
        dlclose(module);
        return false;
    }
    shogi_evaluator_destroy(evaluator);
    evaluator->userdata = userdata;
    evaluator->evaluate = plugin->evaluate;
    evaluator->destroy = plugin->destroy;
    evaluator->name = plugin->name == NULL ? path : plugin->name;
    evaluator->module_handle = module;
    if (plugin->struct_size >= sizeof(*plugin) && plugin->state_create != NULL &&
        plugin->state_destroy != NULL && plugin->state_make != NULL &&
        plugin->state_unmake != NULL && plugin->state_score != NULL) {
        evaluator->state_create = plugin->state_create;
        evaluator->state_destroy = plugin->state_destroy;
        evaluator->state_make = plugin->state_make;
        evaluator->state_unmake = plugin->state_unmake;
        evaluator->state_score = plugin->state_score;
    }
    evaluator_error[0] = '\0';
    return true;
}

bool shogi_evaluator_active(const ShogiEvaluator *evaluator) {
    return evaluator != NULL && evaluator->evaluate != NULL;
}

int shogi_evaluator_score(const ShogiEvaluator *evaluator,
                          const ShogiPosition *position,
                          ShogiColor perspective) {
    if (!shogi_evaluator_active(evaluator) || position == NULL) return 0;
    return evaluator->evaluate(evaluator->userdata, position, perspective);
}

void *shogi_evaluator_state_create(const ShogiEvaluator *evaluator,
                                   const ShogiPosition *position,
                                   ShogiColor perspective) {
    if (!shogi_evaluator_active(evaluator) || evaluator->state_create == NULL ||
        position == NULL) return NULL;
    return evaluator->state_create(evaluator->userdata, position, perspective);
}

void shogi_evaluator_state_destroy(const ShogiEvaluator *evaluator, void *state) {
    if (evaluator != NULL && evaluator->state_destroy != NULL && state != NULL)
        evaluator->state_destroy(state);
}

bool shogi_evaluator_state_make(const ShogiEvaluator *evaluator, void *state,
                                const ShogiPosition *after, const ShogiUndo *undo) {
    return evaluator != NULL && evaluator->state_make != NULL && state != NULL &&
           evaluator->state_make(state, after, undo);
}

bool shogi_evaluator_state_unmake(const ShogiEvaluator *evaluator, void *state,
                                  const ShogiPosition *before, const ShogiUndo *undo) {
    return evaluator != NULL && evaluator->state_unmake != NULL && state != NULL &&
           evaluator->state_unmake(state, before, undo);
}

bool shogi_evaluator_state_rewind(const ShogiEvaluator *evaluator, void *state,
                                  const ShogiPosition *root) {
    return evaluator != NULL && evaluator->state_rewind != NULL && state != NULL &&
           root != NULL && evaluator->state_rewind(state, root);
}

int shogi_evaluator_state_score(const ShogiEvaluator *evaluator, const void *state) {
    if (evaluator == NULL || evaluator->state_score == NULL || state == NULL) return 0;
    return evaluator->state_score(state);
}

bool shogi_evaluator_state_score_batch(const ShogiEvaluator *evaluator,
                                       const void *const *states, size_t count,
                                       int *scores) {
    if (evaluator == NULL || states == NULL || scores == NULL || count == 0 ||
        evaluator->state_score == NULL) return false;
    if (evaluator->state_score_batch != NULL &&
        evaluator->state_score_batch(states, count, scores)) return true;
    for (size_t index = 0; index < count; ++index) {
        if (states[index] == NULL) return false;
        scores[index] = evaluator->state_score(states[index]);
    }
    return true;
}

const char *shogi_evaluator_error(void) {
    return evaluator_error[0] == '\0' ? "" : evaluator_error;
}
