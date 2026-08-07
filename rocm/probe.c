#include "rocew.h"

#include <stdio.h>

int main(void)
{
    if (rocewInit() != ROCEW_SUCCESS || rocewHipInit(0) != hipSuccess) {
        fprintf(stderr, "ROCm/HIP runtime unavailable\n");
        return 77;
    }
    int count = 0;
    if (rocewHipGetDeviceCount(&count) != hipSuccess || count <= 0) {
        fprintf(stderr, "no ROCm device available\n");
        return 77;
    }
    for (int index = 0; index < count; ++index) {
        rocew_hipDeviceProp_t properties;
        size_t memory = 0;
        if (rocewHipGetDeviceProperties(&properties, index) != hipSuccess ||
            rocewHipDeviceTotalMem(&memory, index) != hipSuccess) {
            fprintf(stderr, "failed to query ROCm device %d\n", index);
            return 1;
        }
        printf("device=%d name=%s memory_mb=%zu arch=%s\n", index,
               properties.name, memory / (1024U * 1024U),
               properties.gcnArchName[0] ? properties.gcnArchName : "unknown");
    }
    return 0;
}
