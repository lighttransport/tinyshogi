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
        plugin->struct_size < sizeof(*plugin) || plugin->evaluate == NULL) {
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

const char *shogi_evaluator_error(void) {
    return evaluator_error[0] == '\0' ? "" : evaluator_error;
}
