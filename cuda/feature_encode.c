#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include "cuew.h"

#define FEATURE_PLANES 30U
#define FEATURE_SQUARES 81U
#define FIXED_RECORD_BYTES (81U + 14U + 1U + 1U + 2U)

static const char *kernel_source =
    "extern \"C\" __global__ void encode(const unsigned char *board, "
    "const unsigned char *side, float *out, int n) {"
    "int sample = (int)(blockIdx.x * blockDim.x + threadIdx.x);"
    "if (sample >= n) return;"
    "int base = sample * 30 * 81;"
    "for (int i = 0; i < 30 * 81; ++i) out[base + i] = 0.0f;"
    "for (int square = 0; square < 81; ++square) {"
    "int code = (int)board[sample * 81 + square];"
    "int plane = code == 0 ? 28 : code - 1;"
    "out[base + plane * 81 + square] = 1.0f;"
    "}"
    "if (side[sample]) for (int square = 0; square < 81; ++square) "
    "out[base + 29 * 81 + square] = 1.0f;"
    "}";

static int fail(const char *message, int code) {
    fprintf(stderr, "%s (CUDA error %d)\n", message, code);
    return 1;
}

static int read_records(const char *path, unsigned char **boards, unsigned char **sides,
                        unsigned *count) {
    FILE *file = fopen(path, "rb");
    if (file == NULL) return 1;
    unsigned char header[8];
    if (fread(header, 1, sizeof(header), file) != sizeof(header) ||
        memcmp(header, "TSF1", 4) != 0 || header[4] != 1 || header[5] != 0 ||
        header[6] != 0 || header[7] != 0) { fclose(file); return 1; }
    unsigned char *board_data = NULL;
    unsigned char *side_data = NULL;
    unsigned size = 0;
    unsigned capacity = 0;
    unsigned char fixed[FIXED_RECORD_BYTES];
    while (fread(fixed, 1, sizeof(fixed), file) == sizeof(fixed)) {
        if (size == capacity) {
            unsigned next = capacity == 0 ? 256U : capacity * 2U;
            unsigned char *next_boards = malloc((size_t)next * 81U);
            unsigned char *next_sides = malloc(next);
            if (next_boards == NULL || next_sides == NULL) {
                free(next_boards); free(next_sides); free(board_data); free(side_data);
                fclose(file); return 1;
            }
            if (size != 0) {
                memcpy(next_boards, board_data, (size_t)size * 81U);
                memcpy(next_sides, side_data, size);
            }
            free(board_data);
            free(side_data);
            board_data = next_boards;
            side_data = next_sides;
            capacity = next;
        }
        memcpy(board_data + (size_t)size * 81U, fixed, 81U);
        side_data[size] = fixed[95];
        unsigned policy_count = (unsigned)fixed[97] | ((unsigned)fixed[98] << 8);
        for (unsigned index = 0; index < policy_count; ++index) {
            unsigned char policy_entry[12];
            if (fread(policy_entry, 1, sizeof(policy_entry), file) != sizeof(policy_entry)) {
                free(board_data); free(side_data); fclose(file); return 1;
            }
        }
        ++size;
    }
    fclose(file);
    *boards = board_data;
    *sides = side_data;
    *count = size;
    return size == 0 ? 1 : 0;
}

static int compile_kernel(CUmodule *module, CUdevice device) {
    if (cuewInit(CUEW_INIT_NVRTC) != CUEW_SUCCESS) return 77;
    nvrtcProgram program = NULL;
    if (nvrtcCreateProgram(&program, kernel_source, "tinyshogi_features.cu", 0, NULL, NULL) != NVRTC_SUCCESS) return 1;
    char architecture[32];
    int major = 0, minor = 0;
    if (cuDeviceComputeCapability(&major, &minor, device) != CUDA_SUCCESS) {
        nvrtcDestroyProgram(&program); return 1;
    }
    snprintf(architecture, sizeof(architecture), "--gpu-architecture=compute_%d%d", major, minor);
    const char *options[] = {"--std=c++11", architecture};
    nvrtcResult compile_result = nvrtcCompileProgram(program, 2, options);
    if (compile_result != NVRTC_SUCCESS) {
        size_t log_size = 0;
        nvrtcGetProgramLogSize(program, &log_size);
        char *log = calloc(log_size + 1, 1);
        if (log != NULL) { nvrtcGetProgramLog(program, log); fputs(log, stderr); free(log); }
        nvrtcDestroyProgram(&program);
        return 1;
    }
    size_t ptx_size = 0;
    if (nvrtcGetPTXSize(program, &ptx_size) != NVRTC_SUCCESS) { nvrtcDestroyProgram(&program); return 1; }
    char *ptx = malloc(ptx_size);
    if (ptx == NULL || nvrtcGetPTX(program, ptx) != NVRTC_SUCCESS ||
        cuModuleLoadData(module, ptx) != CUDA_SUCCESS) {
        free(ptx); nvrtcDestroyProgram(&program); return 1;
    }
    free(ptx);
    nvrtcDestroyProgram(&program);
    return 0;
}

int main(int argc, char **argv) {
    if (argc != 3) {
        fprintf(stderr, "usage: %s input.tsf output.tfe\n", argv[0]);
        return 2;
    }
    unsigned char *boards = NULL, *sides = NULL;
    unsigned count = 0;
    if (read_records(argv[1], &boards, &sides, &count) != 0) return 1;
    if (cuewInit(CUEW_INIT_CUDA | CUEW_INIT_NVRTC) != CUEW_SUCCESS) {
        free(boards); free(sides); return 77;
    }
    if (cuInit(0) != CUDA_SUCCESS) { free(boards); free(sides); return 77; }
    CUdevice device;
    if (cuDeviceGet(&device, 0) != CUDA_SUCCESS) { free(boards); free(sides); return 77; }
    CUcontext context;
    if (cuCtxCreate(&context, 0, device) != CUDA_SUCCESS) { free(boards); free(sides); return 77; }
    CUmodule module = NULL;
    int compiled = compile_kernel(&module, device);
    if (compiled != 0) { cuCtxDestroy(context); free(boards); free(sides); return compiled; }
    CUfunction function = NULL;
    if (cuModuleGetFunction(&function, module, "encode") != CUDA_SUCCESS) return fail("kernel lookup failed", 1);
    size_t board_bytes = (size_t)count * 81U;
    size_t side_bytes = count;
    size_t output_bytes = (size_t)count * FEATURE_PLANES * FEATURE_SQUARES * sizeof(float);
    CUdeviceptr d_boards, d_sides, d_output;
    if (cuMemAlloc(&d_boards, board_bytes) != CUDA_SUCCESS ||
        cuMemAlloc(&d_sides, side_bytes) != CUDA_SUCCESS ||
        cuMemAlloc(&d_output, output_bytes) != CUDA_SUCCESS ||
        cuMemcpyHtoD(d_boards, boards, board_bytes) != CUDA_SUCCESS ||
        cuMemcpyHtoD(d_sides, sides, side_bytes) != CUDA_SUCCESS) return fail("device allocation/copy failed", 1);
    int sample_count = (int)count;
    void *parameters[] = {&d_boards, &d_sides, &d_output, &sample_count};
    if (cuLaunchKernel(function, (count + 127U) / 128U, 1, 1, 128, 1, 1, 0, NULL, parameters, NULL) != CUDA_SUCCESS ||
        cuCtxSynchronize() != CUDA_SUCCESS) return fail("feature kernel failed", 1);
    float *features = malloc(output_bytes);
    if (features == NULL || cuMemcpyDtoH(features, d_output, output_bytes) != CUDA_SUCCESS) return fail("feature download failed", 1);
    FILE *output = fopen(argv[2], "wb");
    if (output == NULL) return 1;
    fwrite("TFE1", 1, 4, output);
    uint32_t metadata[3] = {1, count, FEATURE_PLANES};
    fwrite(metadata, sizeof(metadata[0]), 3, output);
    fwrite(features, sizeof(float), (size_t)count * FEATURE_PLANES * FEATURE_SQUARES, output);
    fclose(output);
    printf("encoded records=%u planes=%u\n", count, FEATURE_PLANES);
    free(features); cuMemFree(d_output); cuMemFree(d_sides); cuMemFree(d_boards);
    cuModuleUnload(module); cuCtxDestroy(context); free(boards); free(sides);
    return 0;
}
