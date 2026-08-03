#include "thread.h"

int ts_thread_create(TsThread *thread, void *(*entry)(void *), void *argument) {
    int result = pthread_create(&thread->handle, NULL, entry, argument);
    thread->started = result == 0;
    return result;
}

int ts_thread_join(TsThread *thread) {
    if (!thread->started) return 0;
    int result = pthread_join(thread->handle, NULL);
    if (result == 0) thread->started = 0;
    return result;
}

int ts_mutex_init(TsMutex *mutex) {
    return pthread_mutex_init(mutex, NULL);
}

int ts_mutex_destroy(TsMutex *mutex) {
    return pthread_mutex_destroy(mutex);
}

int ts_mutex_lock(TsMutex *mutex) {
    return pthread_mutex_lock(mutex);
}

int ts_mutex_unlock(TsMutex *mutex) {
    return pthread_mutex_unlock(mutex);
}
