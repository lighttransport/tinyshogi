/* SPDX-License-Identifier: Apache-2.0 */
#define _POSIX_C_SOURCE 200809L
#include "dl_eval.h"
#include "dl_features.h"
#include "gn.h"
#include <pthread.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>
static _Thread_local char open_error[256];
typedef struct Request {
    const ShogiPosition *position;
    const ShogiMove *moves;
    size_t count;
    float *logits, *wdl;
    struct Request *next;
    bool done, ok;
} Request;
struct ShogiDlModel {
    gn_model *network;
    ShogiPolicyValueEvaluator evaluator;
    pthread_t thread;
    pthread_mutex_t mutex;
    pthread_cond_t changed;
    Request *head, *tail;
    size_t queued;
    unsigned batch;
    bool stop;
    float *features, *logits, *wdl;
    char error[256];
};
static void *inference_main(void *opaque) {
    ShogiDlModel *m = opaque;
    Request *requests[256];
    pthread_mutex_lock(&m->mutex);
    for (;;) {
        while (!m->head && !m->stop)
            pthread_cond_wait(&m->changed, &m->mutex);
        if (!m->head && m->stop)
            break;
        struct timespec until;
        clock_gettime(CLOCK_MONOTONIC, &until);
        until.tv_nsec += 1000000;
        if (until.tv_nsec >= 1000000000) {
            until.tv_nsec -= 1000000000;
            until.tv_sec++;
        }
        while (m->queued < m->batch && !m->stop)
            if (pthread_cond_timedwait(&m->changed, &m->mutex, &until) != 0)
                break;
        size_t count = 0;
        while (m->head && count < m->batch) {
            requests[count++] = m->head;
            m->head = m->head->next;
            m->queued--;
        }
        if (!m->head)
            m->tail = NULL;
        pthread_mutex_unlock(&m->mutex);
        for (size_t i = 0; i < count; i++)
            shogi_dl_encode(requests[i]->position, m->features + i * SHOGI_DL_FEATURES);
        bool ok = gn_infer(m->network, count, m->features, m->logits, m->wdl) == 0;
        char error[256] = {0};
        if (!ok)
            snprintf(error, sizeof(error), "%s", gn_error());
        for (size_t i = 0; i < count && ok; i++)
            for (size_t j = 0; j < requests[i]->count; j++) {
                int id = shogi_dl_action(requests[i]->position, requests[i]->moves[j]);
                if (id < 0) {
                    ok = false;
                    snprintf(error, sizeof(error), "legal move has no action encoding");
                    break;
                }
                requests[i]->logits[j] = m->logits[i * SHOGI_DL_ACTIONS + (size_t)id];
            }
        pthread_mutex_lock(&m->mutex);
        if (!ok)
            snprintf(m->error, sizeof(m->error), "%s", error);
        for (size_t i = 0; i < count; i++) {
            if (ok)
                memcpy(requests[i]->wdl, m->wdl + i * 3, 3 * sizeof(float));
            requests[i]->ok = ok;
            requests[i]->done = true;
        }
        pthread_cond_broadcast(&m->changed);
    }
    pthread_mutex_unlock(&m->mutex);
    return NULL;
}
static bool evaluate(void *opaque, const ShogiPosition *const *positions,
                     const ShogiMove *const *moves, const size_t *counts, size_t count,
                     float *const *logits, float *wdl) {
    ShogiDlModel *m = opaque;
    if (!count || count > 256)
        return false;
    Request *r = calloc(count, sizeof(*r));
    if (!r)
        return false;
    pthread_mutex_lock(&m->mutex);
    if (m->stop) {
        pthread_mutex_unlock(&m->mutex);
        free(r);
        return false;
    }
    for (size_t i = 0; i < count; i++) {
        r[i].position = positions[i];
        r[i].moves = moves[i];
        r[i].count = counts[i];
        r[i].logits = logits[i];
        r[i].wdl = wdl + 3 * i;
        if (m->tail)
            m->tail->next = &r[i];
        else
            m->head = &r[i];
        m->tail = &r[i];
        m->queued++;
    }
    pthread_cond_broadcast(&m->changed);
    bool done = false, ok = true;
    while (!done) {
        done = true;
        for (size_t i = 0; i < count; i++)
            if (!r[i].done)
                done = false;
        if (!done)
            pthread_cond_wait(&m->changed, &m->mutex);
    }
    for (size_t i = 0; i < count; i++)
        ok = ok && r[i].ok;
    pthread_mutex_unlock(&m->mutex);
    free(r);
    return ok;
}
ShogiDlModel *shogi_dl_open(const char *path, const char *backend, int device, unsigned batch) {
    open_error[0] = 0;
    if (!path || !batch || batch > 256) {
        snprintf(open_error, sizeof(open_error), "invalid model path/batch size");
        return NULL;
    }
    gn_model *network = gn_load(path, backend, device);
    if (!network) {
        snprintf(open_error, sizeof(open_error), "%s", gn_error());
        return NULL;
    }
    const gn_config *c = gn_configuration(network);
    if (c->side != 9 || c->inputs != SHOGI_DL_CHANNELS || c->actions != SHOGI_DL_PLANES) {
        gn_destroy(network);
        snprintf(open_error, sizeof(open_error), "expected 9x9, 80 features, 139 action planes");
        return NULL;
    }
    ShogiDlModel *m = calloc(1, sizeof(*m));
    if (!m) {
        gn_destroy(network);
        snprintf(open_error, sizeof(open_error), "inference queue allocation failed");
        return NULL;
    }
    m->network = network;
    m->batch = batch;
    m->features = malloc((size_t)batch * SHOGI_DL_FEATURES * sizeof(float));
    m->logits = malloc((size_t)batch * SHOGI_DL_ACTIONS * sizeof(float));
    m->wdl = malloc(batch * 3 * sizeof(float));
    if (!m->features || !m->logits || !m->wdl)
        goto fail;
    if (pthread_mutex_init(&m->mutex, NULL))
        goto fail;
    pthread_condattr_t attr;
    if (pthread_condattr_init(&attr)) {
        pthread_mutex_destroy(&m->mutex);
        goto fail;
    }
    int rc = pthread_condattr_setclock(&attr, CLOCK_MONOTONIC);
    if (!rc)
        rc = pthread_cond_init(&m->changed, &attr);
    pthread_condattr_destroy(&attr);
    if (rc) {
        pthread_mutex_destroy(&m->mutex);
        goto fail;
    }
    if (pthread_create(&m->thread, NULL, inference_main, m)) {
        pthread_cond_destroy(&m->changed);
        pthread_mutex_destroy(&m->mutex);
        goto fail;
    }
    m->evaluator.userdata = m;
    m->evaluator.evaluate_batch = evaluate;
    return m;
fail:
    snprintf(open_error, sizeof(open_error), "inference queue allocation/thread setup failed");
    free(m->features);
    free(m->logits);
    free(m->wdl);
    gn_destroy(network);
    free(m);
    return NULL;
}
void shogi_dl_close(ShogiDlModel *m) {
    if (!m)
        return;
    pthread_mutex_lock(&m->mutex);
    m->stop = true;
    pthread_cond_broadcast(&m->changed);
    pthread_mutex_unlock(&m->mutex);
    pthread_join(m->thread, NULL);
    pthread_cond_destroy(&m->changed);
    pthread_mutex_destroy(&m->mutex);
    gn_destroy(m->network);
    free(m->features);
    free(m->logits);
    free(m->wdl);
    free(m);
}
const ShogiPolicyValueEvaluator *shogi_dl_evaluator(ShogiDlModel *m) {
    return m ? &m->evaluator : NULL;
}
const char *shogi_dl_error(const ShogiDlModel *m) { return m ? m->error : open_error; }
