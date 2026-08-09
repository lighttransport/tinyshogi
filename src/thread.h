#ifndef TINYSHOGI_THREAD_H
#define TINYSHOGI_THREAD_H

#include <pthread.h>

typedef struct {
    pthread_t handle;
    int started;
} TsThread;

typedef pthread_mutex_t TsMutex;

int ts_thread_create(TsThread *thread, void *(*entry)(void *), void *argument);
int ts_thread_join(TsThread *thread);
int ts_thread_pin_allowed(unsigned worker_index);
unsigned ts_thread_allowed_count(void);
int ts_mutex_init(TsMutex *mutex);
int ts_mutex_destroy(TsMutex *mutex);
int ts_mutex_lock(TsMutex *mutex);
int ts_mutex_unlock(TsMutex *mutex);

#endif
