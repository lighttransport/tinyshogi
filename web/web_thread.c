#include "../src/thread.h"

/* The browser engine worker uses one synchronous search thread. The worker
 * itself is the concurrency boundary, so no pthreads or shared memory are
 * needed in the WASM module. */
int ts_thread_create(TsThread *thread, void *(*entry)(void *), void *argument) {
    thread->started = 1;
    (void)entry(argument);
    return 0;
}

int ts_thread_join(TsThread *thread) {
    thread->started = 0;
    return 0;
}

int ts_mutex_init(TsMutex *mutex) { (void)mutex; return 0; }
int ts_mutex_destroy(TsMutex *mutex) { (void)mutex; return 0; }
int ts_mutex_lock(TsMutex *mutex) { (void)mutex; return 0; }
int ts_mutex_unlock(TsMutex *mutex) { (void)mutex; return 0; }
