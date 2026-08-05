#include <stdio.h>

#include "cuew.h"

int main(void) {
    if (cuewInit(CUEW_INIT_CUDA) != CUEW_SUCCESS) {
        fprintf(stderr, "CUDA driver runtime unavailable\n");
        return 77;
    }
    CUresult result = cuInit(0);
    if (result != CUDA_SUCCESS) {
        fprintf(stderr, "cuInit failed: %d\n", (int)result);
        return 77;
    }
    int count = 0;
    if (cuDeviceGetCount(&count) != CUDA_SUCCESS || count <= 0) {
        fprintf(stderr, "no CUDA device available\n");
        return 77;
    }
    for (int index = 0; index < count; ++index) {
        CUdevice device;
        char name[128] = {0};
        size_t memory = 0;
        int major = 0;
        int minor = 0;
        if (cuDeviceGet(&device, index) != CUDA_SUCCESS ||
            cuDeviceGetName(name, (int)sizeof(name), device) != CUDA_SUCCESS ||
            cuDeviceTotalMem(&memory, device) != CUDA_SUCCESS ||
            cuDeviceComputeCapability(&major, &minor, device) != CUDA_SUCCESS) {
            fprintf(stderr, "failed to query CUDA device %d\n", index);
            return 1;
        }
        printf("device=%d name=%s memory_mb=%zu compute=%d.%d\n",
               index, name, memory / (1024U * 1024U), major, minor);
    }
    return 0;
}
