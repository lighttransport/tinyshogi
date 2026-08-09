#define _GNU_SOURCE
#include "thread.h"

#include <errno.h>
#include <sched.h>

int ts_thread_pin_allowed(unsigned worker_index) {
    cpu_set_t allowed;
    if (sched_getaffinity(0, sizeof(allowed), &allowed) != 0) return errno;
    int cpus[CPU_SETSIZE];
    unsigned ordinal = 0;
    for (int cpu = 0; cpu < CPU_SETSIZE; ++cpu) {
        if (!CPU_ISSET(cpu, &allowed)) continue;
        cpus[ordinal++] = cpu;
    }
    if (ordinal == 0) return EINVAL;
    unsigned index = worker_index;
    /* A full A64FX node exposes four 12-core NUMA/HBM domains.  Spread the
     * first workers across domains; retain ordinal placement for small or
     * irregular cpusets so ordinary Linux hosts behave conventionally. */
    if (ordinal >= 32U && (ordinal & 3U) == 0U)
        index = (worker_index & 3U) * (ordinal / 4U) + worker_index / 4U;
    if (index >= ordinal) index %= ordinal;
    int selected = cpus[index];
    cpu_set_t target;
    CPU_ZERO(&target); CPU_SET(selected, &target);
    return pthread_setaffinity_np(pthread_self(), sizeof(target), &target);
}

unsigned ts_thread_allowed_count(void) {
    cpu_set_t allowed;
    if (sched_getaffinity(0, sizeof(allowed), &allowed) != 0) return 1U;
    unsigned count = 0;
    for (int cpu = 0; cpu < CPU_SETSIZE; ++cpu)
        if (CPU_ISSET(cpu, &allowed)) ++count;
    return count == 0 ? 1U : count;
}

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
