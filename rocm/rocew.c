#include "rocew.h"

#include <dlfcn.h>
#include <stdlib.h>

static void *hip_library;
static int hip_available;

trocewHipGetErrorString rocewHipGetErrorString;
trocewHipInit rocewHipInit;
trocewHipGetDeviceCount rocewHipGetDeviceCount;
trocewHipGetDeviceProperties rocewHipGetDeviceProperties;
trocewHipDeviceTotalMem rocewHipDeviceTotalMem;
trocewHipDeviceGetAttribute rocewHipDeviceGetAttribute;

static void *open_first(const char *const *names)
{
    for (size_t i = 0; names[i]; ++i) {
        void *library = dlopen(names[i], RTLD_NOW | RTLD_LOCAL);
        if (library) return library;
    }
    return NULL;
}

static void close_rocew(void)
{
    if (hip_library) dlclose(hip_library);
    hip_library = NULL;
    hip_available = 0;
}

#define LOAD_HIP(variable, type, symbol) \
    do { \
        variable = (type)dlsym(hip_library, symbol); \
        if (!variable) { close_rocew(); return ROCEW_ERROR_SYMBOL_MISSING; } \
    } while (0)

int rocewInit(void)
{
    static const char *const names[] = {
        "libamdhip64.so", "libamdhip64.so.6", "libamdhip64.so.5",
        "/opt/rocm/lib/libamdhip64.so",
        "/opt/rocm/core/lib/libamdhip64.so",
        "/opt/rocm/core-7.14/lib/libamdhip64.so", NULL
    };
    if (hip_available) return ROCEW_SUCCESS;
    hip_library = open_first(names);
    if (!hip_library) return ROCEW_ERROR_OPEN_FAILED;
    LOAD_HIP(rocewHipGetErrorString, trocewHipGetErrorString, "hipGetErrorString");
    LOAD_HIP(rocewHipInit, trocewHipInit, "hipInit");
    LOAD_HIP(rocewHipGetDeviceCount, trocewHipGetDeviceCount, "hipGetDeviceCount");
    LOAD_HIP(rocewHipGetDeviceProperties, trocewHipGetDeviceProperties, "hipGetDeviceProperties");
    LOAD_HIP(rocewHipDeviceTotalMem, trocewHipDeviceTotalMem, "hipDeviceTotalMem");
    LOAD_HIP(rocewHipDeviceGetAttribute, trocewHipDeviceGetAttribute, "hipDeviceGetAttribute");
    hip_available = 1;
    atexit(close_rocew);
    return ROCEW_SUCCESS;
}

int rocewAvailable(void)
{
    return hip_available;
}
