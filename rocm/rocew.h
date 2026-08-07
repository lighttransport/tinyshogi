/*
 * ROCEW - the small, no-SDK ROCm/HIP runtime loader used by tinyshogi.
 *
 * The declarations intentionally mirror the ABI of the HIP runtime without
 * including ROCm headers.  This keeps the CPU executable link-free from
 * ROCm; the library is opened only by programs which request ROCm support.
 */
#ifndef TINYSHOGI_ROCEW_H
#define TINYSHOGI_ROCEW_H

#include <stddef.h>

#ifdef __cplusplus
extern "C" {
#endif

#define ROCEW_SUCCESS 0
#define ROCEW_ERROR_OPEN_FAILED -1
#define ROCEW_ERROR_SYMBOL_MISSING -2

typedef int hipError_t;
typedef int hipDevice_t;
typedef int hipDeviceAttribute_t;

#define hipSuccess 0
#define hipDeviceAttributeGcnArchName 40

/* The leading fields are stable in the HIP ABI and are sufficient for the
 * device information reported by the probe. */
typedef struct {
    char name[256];
    size_t totalGlobalMem;
    size_t sharedMemPerBlock;
    int regsPerBlock;
    int warpSize;
    size_t memPitch;
    int maxThreadsPerBlock;
    int maxThreadsDim[3];
    int maxGridSize[3];
    int clockRate;
    size_t totalConstMem;
    int major;
    int minor;
    int multiProcessorCount;
    int l2CacheSize;
    int maxThreadsPerMultiProcessor;
    int computeMode;
    int clockInstructionRate;
    int reserved[10];
    char gcnArchName[256];
    char reserved_tail[768];
} rocew_hipDeviceProp_t;

typedef const char *(*trocewHipGetErrorString)(hipError_t);
typedef hipError_t (*trocewHipInit)(unsigned int);
typedef hipError_t (*trocewHipGetDeviceCount)(int *);
typedef hipError_t (*trocewHipGetDeviceProperties)(rocew_hipDeviceProp_t *, hipDevice_t);
typedef hipError_t (*trocewHipDeviceTotalMem)(size_t *, hipDevice_t);
typedef hipError_t (*trocewHipDeviceGetAttribute)(int *, hipDeviceAttribute_t, hipDevice_t);

extern trocewHipGetErrorString rocewHipGetErrorString;
extern trocewHipInit rocewHipInit;
extern trocewHipGetDeviceCount rocewHipGetDeviceCount;
extern trocewHipGetDeviceProperties rocewHipGetDeviceProperties;
extern trocewHipDeviceTotalMem rocewHipDeviceTotalMem;
extern trocewHipDeviceGetAttribute rocewHipDeviceGetAttribute;

int rocewInit(void);
int rocewAvailable(void);

#ifdef __cplusplus
}
#endif

#endif
