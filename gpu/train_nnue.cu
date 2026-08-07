#include <cmath>
#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <cstring>

extern "C" {
#include "../src/nnue.h"
}

#if defined(__HIPCC__)
#include <hip/hip_runtime.h>
#define GPU_ERROR hipError_t
#define GPU_SUCCESS hipSuccess
#define gpuMalloc hipMalloc
#define gpuFree hipFree
#define gpuMemcpyHtoD hipMemcpyHtoD
#define gpuMemcpyDtoH hipMemcpyDtoH
#define gpuMemcpyHostToDevice hipMemcpyHostToDevice
#define gpuMemcpyDeviceToHost hipMemcpyDeviceToHost
#define gpuMemset hipMemset
#define gpuGetErrorString hipGetErrorString
#define gpuLaunchKernelG launch_kernel_g
#else
#include <cuda_runtime.h>
#define GPU_ERROR cudaError_t
#define GPU_SUCCESS cudaSuccess
#define gpuMalloc cudaMalloc
#define gpuFree cudaFree
#define gpuMemcpyHtoD cudaMemcpy
#define gpuMemcpyDtoH cudaMemcpy
#define gpuMemcpyHostToDevice cudaMemcpyHostToDevice
#define gpuMemcpyDeviceToHost cudaMemcpyDeviceToHost
#define gpuMemset cudaMemset
#define gpuGetErrorString cudaGetErrorString
#endif

#define NDF_MAGIC "NDF1"
#define MAX_ACTIVE (SHOGI_SQUARES + 14U)
#define DEFAULT_HIDDEN SHOGI_NNUE_DEFAULT_HIDDEN

typedef struct {
    uint8_t board[SHOGI_SQUARES];
    uint8_t hand[14];
    uint8_t padding;
    int16_t value;
    uint8_t side;
    uint8_t source;
} Record;

static_assert(sizeof(Record) == 100, "NDF1 record layout mismatch");

__global__ void train_kernel(const uint32_t *ids, const uint16_t *active,
                             const uint8_t *sides, const float *targets,
                             float *feature_weights, float *output,
                             float learning_rate) {
    uint32_t sample = (uint32_t)blockIdx.x;
    uint32_t unit = (uint32_t)threadIdx.x;
    if (unit >= DEFAULT_HIDDEN) return;
    __shared__ float hidden[DEFAULT_HIDDEN];
    __shared__ float gradient;
    const uint32_t *sample_ids = ids + (size_t)sample * MAX_ACTIVE;
    float sum = 0.0f;
    for (uint32_t index = 0; index < active[sample]; ++index)
        sum += feature_weights[(size_t)sample_ids[index] * DEFAULT_HIDDEN + unit];
    hidden[unit] = sum > 0.0f ? sum : 0.0f;
    __syncthreads();
    if (unit == 0) {
        uint32_t side = sides[sample];
        float prediction = 0.0f;
        for (uint32_t index = 0; index < DEFAULT_HIDDEN; ++index)
            prediction += hidden[index] * output[(size_t)side * DEFAULT_HIDDEN + index];
        prediction = tanhf(prediction);
        gradient = (targets[sample] - prediction) * (1.0f - prediction * prediction) * learning_rate;
        if (sample == 0) output[0] = targets[sample];
    }
    __syncthreads();
    uint32_t side = sides[sample];
    float old_output = output[(size_t)side * DEFAULT_HIDDEN + unit];
    atomicAdd(output + (size_t)side * DEFAULT_HIDDEN + unit, gradient * hidden[unit]);
    if (hidden[unit] > 0.0f) {
        for (uint32_t index = 0; index < active[sample]; ++index)
            atomicAdd(feature_weights + (size_t)sample_ids[index] * DEFAULT_HIDDEN + unit,
                      gradient * old_output);
    }
}

static bool gpu_ok(GPU_ERROR error, const char *what) {
    if (error == GPU_SUCCESS) return true;
    fprintf(stderr, "%s: %s\n", what, gpuGetErrorString(error));
    return false;
}

static bool read_data(const char *path, Record **records, uint32_t *count) {
    FILE *file = fopen(path, "rb");
    if (!file) return false;
    char magic[4]; uint32_t header[3];
    bool ok = fread(magic, 1, 4, file) == 4 && memcmp(magic, NDF_MAGIC, 4) == 0 &&
              fread(header, sizeof(*header), 3, file) == 3 && header[0] == 1 &&
              header[2] == sizeof(Record);
    Record *data = ok ? (Record *)malloc((size_t)header[1] * sizeof(*data)) : nullptr;
    if (ok) ok = data != nullptr && fread(data, sizeof(*data), header[1], file) == header[1];
    fclose(file);
    if (!ok) { free(data); return false; }
    *records = data; *count = header[1]; return true;
}

static void make_position(const Record &record, ShogiPosition *position) {
    memset(position, 0, sizeof(*position));
    memcpy(position->board, record.board, sizeof(position->board));
    memcpy(position->hand, record.hand, sizeof(position->hand));
    position->side = (ShogiColor)record.side;
    position->king_square[0] = position->king_square[1] = SHOGI_SQ_NONE;
    for (uint8_t square = 0; square < SHOGI_SQUARES; ++square)
        if (position->board[square] != SHOGI_EMPTY &&
            shogi_piece_type(position->board[square]) == SHOGI_KING)
            position->king_square[shogi_piece_color(position->board[square])] = square;
}

static int16_t quantize(float value, float scale) {
    long rounded = lroundf(value * scale);
    if (rounded > INT16_MAX) rounded = INT16_MAX;
    if (rounded < INT16_MIN) rounded = INT16_MIN;
    return (int16_t)rounded;
}

static bool write_model(const char *path, const float *features, const float *output) {
    ShogiNnueModel model;
    shogi_nnue_model_init(&model);
    if (!shogi_nnue_model_init_default(&model, DEFAULT_HIDDEN)) return false;
    float max_output = 0.0f;
    for (size_t index = 0; index < (size_t)DEFAULT_HIDDEN * 2U; ++index)
        if (fabsf(output[index]) > max_output) max_output = fabsf(output[index]);
    printf("gpu output_abs_max=%.8g\n", max_output);
    for (size_t index = 0; index < (size_t)model.feature_count * DEFAULT_HIDDEN; ++index)
        model.feature_weights[index] = quantize(features[index], 256.0f);
    for (size_t index = 0; index < (size_t)DEFAULT_HIDDEN * 2U; ++index)
        model.output_weights[index] = quantize(output[index], 1024.0f);
    bool ok = shogi_nnue_model_save(&model, path);
    shogi_nnue_model_destroy(&model);
    return ok;
}

int main(int argc, char **argv) {
    if (argc < 3 || argc > 5) {
        fprintf(stderr, "usage: %s data.ndf1 output.nnue [epochs] [learning-rate]\n", argv[0]);
        return 2;
    }
    unsigned epochs = argc >= 4 ? (unsigned)strtoul(argv[3], nullptr, 10) : 5U;
    float learning_rate = argc >= 5 ? strtof(argv[4], nullptr) : 0.01f;
    Record *records = nullptr; uint32_t count = 0;
    if (epochs == 0 || learning_rate <= 0.0f || !read_data(argv[1], &records, &count) || count == 0) return 1;
    shogi_init();
    size_t feature_bytes = (size_t)SHOGI_NNUE_FEATURE_COUNT * DEFAULT_HIDDEN * sizeof(float);
    float *host_features = (float *)malloc(feature_bytes);
    float *host_output = (float *)calloc((size_t)DEFAULT_HIDDEN * 2U, sizeof(float));
    uint32_t *host_ids = (uint32_t *)calloc((size_t)count * MAX_ACTIVE, sizeof(uint32_t));
    uint16_t *host_active = (uint16_t *)calloc(count, sizeof(uint16_t));
    uint8_t *host_sides = (uint8_t *)malloc(count);
    float *host_targets = (float *)malloc((size_t)count * sizeof(float));
    if (!host_features || !host_output || !host_ids || !host_active || !host_sides || !host_targets) return 1;
    uint32_t random_state = 7;
    for (size_t index = 0; index < (size_t)SHOGI_NNUE_FEATURE_COUNT * DEFAULT_HIDDEN; ++index) {
        random_state = random_state * 1664525U + 1013904223U;
        host_features[index] = ((float)((random_state >> 8) & 0xffffffU) / 16777216.0f - 0.5f) * 0.01f;
    }
    for (uint32_t sample = 0; sample < count; ++sample) {
        ShogiPosition position; make_position(records[sample], &position);
        host_sides[sample] = records[sample].side;
        host_targets[sample] = (float)records[sample].value / 1000.0f;
        host_active[sample] = (uint16_t)shogi_nnue_feature_ids(&position, position.side,
            host_ids + (size_t)sample * MAX_ACTIVE, MAX_ACTIVE);
    }
    float *device_features = nullptr, *device_output = nullptr, *device_targets = nullptr;
    uint32_t *device_ids = nullptr; uint16_t *device_active = nullptr; uint8_t *device_sides = nullptr;
    bool ok = gpu_ok(gpuMalloc((void **)&device_features, feature_bytes), "allocate feature weights") &&
              gpu_ok(gpuMalloc((void **)&device_output, (size_t)DEFAULT_HIDDEN * 2U * sizeof(float)), "allocate output weights") &&
              gpu_ok(gpuMalloc((void **)&device_ids, (size_t)count * MAX_ACTIVE * sizeof(uint32_t)), "allocate feature ids") &&
              gpu_ok(gpuMalloc((void **)&device_active, (size_t)count * sizeof(uint16_t)), "allocate active counts") &&
              gpu_ok(gpuMalloc((void **)&device_sides, count), "allocate sides") &&
              gpu_ok(gpuMalloc((void **)&device_targets, (size_t)count * sizeof(float)), "allocate targets");
#if !defined(__HIPCC__)
    if (ok) {
        cudaDeviceProp properties;
        ok = gpu_ok(cudaGetDeviceProperties(&properties, 0), "query CUDA device");
#if CUDART_VERSION >= 13000
        if (ok && (properties.major < 7 || (properties.major == 7 && properties.minor < 5))) {
            fprintf(stderr, "CUDA %d.%d cannot target compute capability %d.%d; use CUDA 12.x for this GPU\n",
                    CUDART_VERSION / 1000, (CUDART_VERSION % 1000) / 10,
                    properties.major, properties.minor);
            ok = false;
        }
#endif
    }
#endif
    if (ok) ok = gpu_ok(gpuMemcpyHtoD(device_features, host_features, feature_bytes, gpuMemcpyHostToDevice), "copy feature weights") &&
                   gpu_ok(gpuMemcpyHtoD(device_output, host_output, (size_t)DEFAULT_HIDDEN * 2U * sizeof(float), gpuMemcpyHostToDevice), "copy output weights") &&
                   gpu_ok(gpuMemcpyHtoD(device_ids, host_ids, (size_t)count * MAX_ACTIVE * sizeof(uint32_t), gpuMemcpyHostToDevice), "copy feature ids") &&
                   gpu_ok(gpuMemcpyHtoD(device_active, host_active, (size_t)count * sizeof(uint16_t), gpuMemcpyHostToDevice), "copy active counts") &&
                   gpu_ok(gpuMemcpyHtoD(device_sides, host_sides, count, gpuMemcpyHostToDevice), "copy sides") &&
                   gpu_ok(gpuMemcpyHtoD(device_targets, host_targets, (size_t)count * sizeof(float), gpuMemcpyHostToDevice), "copy targets");
    for (unsigned epoch = 0; ok && epoch < epochs; ++epoch) {
        train_kernel<<<count, DEFAULT_HIDDEN>>>(device_ids, device_active, device_sides,
                                                 device_targets, device_features, device_output,
                                                 learning_rate);
#if defined(__HIPCC__)
        ok = gpu_ok(hipGetLastError(), "HIP training launch") &&
             gpu_ok(hipDeviceSynchronize(), "HIP training kernel");
#else
        ok = gpu_ok(cudaGetLastError(), "CUDA training launch") &&
             gpu_ok(cudaDeviceSynchronize(), "CUDA training kernel");
#endif
        if (ok) printf("gpu epoch=%u samples=%u\n", epoch + 1, count);
    }
    if (ok) ok = gpu_ok(gpuMemcpyDtoH(host_features, device_features, feature_bytes, gpuMemcpyDeviceToHost), "download feature weights") &&
                gpu_ok(gpuMemcpyDtoH(host_output, device_output, (size_t)DEFAULT_HIDDEN * 2U * sizeof(float), gpuMemcpyDeviceToHost), "download output weights");
    if (ok && !write_model(argv[2], host_features, host_output)) ok = false;
    if (device_targets) gpuFree(device_targets); if (device_sides) gpuFree(device_sides);
    if (device_active) gpuFree(device_active); if (device_ids) gpuFree(device_ids);
    if (device_output) gpuFree(device_output); if (device_features) gpuFree(device_features);
    free(host_features); free(host_output); free(host_ids); free(host_active); free(host_sides); free(host_targets); free(records);
    return ok ? 0 : 1;
}
