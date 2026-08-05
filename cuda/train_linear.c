#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include "cuew.h"

#define FEATURE_DIM (30U * 81U)
#define HIDDEN_DIM 64U
#define ACTION_COUNT (81U * 81U * 2U + 7U * 81U)

static const char *kernel_source =
    "extern \"C\" __device__ float dot(const float *a, const float *b, int n) {"
    "float v=0.0f; for(int i=0;i<n;++i) v += a[i]*b[i]; return v;}"
    "extern \"C\" __global__ void train(const float *x,const float *yv,"
    "const uint *offs,const uint *counts,const uint *acts,const float *yt,"
    "float *w1,float *b1,float *vw,float *pw,int n,int dim,float lr) {"
    "int s=(int)(blockIdx.x*blockDim.x+threadIdx.x); if(s>=n)return;"
    "const float *f=x+s*dim; float z[64],h[64],gh[64];"
    "for(int j=0;j<64;++j){z[j]=b1[j]+dot(w1+j*dim,f,dim);h[j]=z[j]>0.0f?z[j]:0.0f;gh[j]=0.0f;}"
    "float pred=tanhf(dot(vw,h,64));"
    "float vg=(yv[s]-pred)*(1.0f-pred*pred)*lr;"
    "for(int j=0;j<64;++j) gh[j]+=vg*vw[j],atomicAdd(vw+j,vg*h[j]);"
    "for(uint j=0;j<counts[s];++j){uint a=acts[offs[s]+j];"
    "float logit=dot(pw+a*64,h,64); float pg=(yt[offs[s]+j]-logit)*lr;"
    "for(int k=0;k<64;++k) gh[k]+=pg*pw[a*64+k],atomicAdd(pw+a*64+k,pg*h[k]);}"
    "for(int j=0;j<64;++j) if(z[j]>0.0f){atomicAdd(b1+j,lr*gh[j]);"
    "for(int i=0;i<dim;++i) atomicAdd(w1+j*dim+i,lr*gh[j]*f[i]);}}";

typedef struct { unsigned action; float target; } SparseLabel;

static unsigned square_id(const char *text) {
    if (text[0] < '1' || text[0] > '9' || text[1] < 'a' || text[1] > 'i') return UINT32_MAX;
    return (unsigned)(text[1] - 'a') * 9U + (unsigned)(9 - (text[0] - '0'));
}

static unsigned action_id(const unsigned char *move) {
    if (move[1] == '*') {
        unsigned type = 0;
        switch (move[0]) { case 'R': type = 0; break; case 'B': type = 1; break;
        case 'G': type = 2; break; case 'S': type = 3; break; case 'N': type = 4; break;
        case 'L': type = 5; break; case 'P': type = 6; break; default: return UINT32_MAX; }
        unsigned to = square_id((const char *)(move + 2));
        return to == UINT32_MAX ? UINT32_MAX : 81U * 81U * 2U + type * 81U + to;
    }
    unsigned from = square_id((const char *)move);
    unsigned to = square_id((const char *)(move + 2));
    if (from == UINT32_MAX || to == UINT32_MAX) return UINT32_MAX;
    unsigned promote = move[4] == '+' ? 1U : 0U;
    return (from * 81U + to) * 2U + promote;
}

static int read_features(const char *path, float **features, unsigned *count) {
    FILE *file = fopen(path, "rb"); if (!file) return 1;
    uint32_t header[4];
    if (fread(header, sizeof(uint32_t), 4, file) != 4 || memcmp(header, "TFE1", 4) != 0 ||
        header[1] != 1 || header[3] != 30) { fclose(file); return 1; }
    *count = header[2];
    size_t amount = (size_t)*count * FEATURE_DIM;
    *features = malloc(amount * sizeof(float));
    if (!*features || fread(*features, sizeof(float), amount, file) != amount) { free(*features); fclose(file); return 1; }
    fclose(file); return 0;
}

static int read_labels(const char *path, float **values, unsigned **offsets, unsigned **counts,
                       SparseLabel **labels, unsigned expected, unsigned *label_count) {
    FILE *file = fopen(path, "rb"); if (!file) return 1;
    unsigned char header[8];
    if (fread(header, 1, 8, file) != 8 || memcmp(header, "TSF1", 4) != 0 || header[4] != 1) { fclose(file); return 1; }
    *values = calloc(expected, sizeof(float)); *offsets = calloc(expected, sizeof(unsigned));
    *counts = calloc(expected, sizeof(unsigned));
    SparseLabel *data = NULL; unsigned data_count = 0, data_capacity = 0;
    unsigned char fixed[99]; unsigned sample = 0;
    while (sample < expected && fread(fixed, 1, sizeof(fixed), file) == sizeof(fixed)) {
        (*values)[sample] = (float)(int8_t)fixed[96];
        unsigned policy_count = (unsigned)fixed[97] | ((unsigned)fixed[98] << 8);
        (*offsets)[sample] = data_count;
        for (unsigned index = 0; index < policy_count; ++index) {
            unsigned char entry[12];
            if (fread(entry, 1, sizeof(entry), file) != sizeof(entry)) goto fail;
            unsigned action = action_id(entry);
            uint32_t visits = (uint32_t)entry[8] | ((uint32_t)entry[9] << 8) |
                              ((uint32_t)entry[10] << 16) | ((uint32_t)entry[11] << 24);
            if (action == UINT32_MAX || action >= ACTION_COUNT) continue;
            if (data_count == data_capacity) {
                unsigned next = data_capacity == 0 ? 1024U : data_capacity * 2U;
                SparseLabel *grown = realloc(data, (size_t)next * sizeof(*data));
                if (!grown) goto fail;
                data = grown; data_capacity = next;
            }
            data[data_count].action = action;
            data[data_count].target = (float)visits;
            ++data_count;
        }
        (*counts)[sample] = data_count - (*offsets)[sample];
        ++sample;
    }
    fclose(file);
    if (sample != expected) goto fail_no_file;
    for (unsigned s = 0; s < expected; ++s) {
        float total = 0.0f;
        for (unsigned j = 0; j < (*counts)[s]; ++j) total += data[(*offsets)[s] + j].target;
        if (total > 0.0f) for (unsigned j = 0; j < (*counts)[s]; ++j) data[(*offsets)[s] + j].target /= total;
    }
    *labels = data; *label_count = data_count; return 0;
fail:
    fclose(file);
fail_no_file:
    free(*values); free(*offsets); free(*counts); free(data); return 1;
}

int main(int argc, char **argv) {
    if (argc < 4 || argc > 5) { fprintf(stderr, "usage: %s data.tsf features.tfe model.tsm [epochs]\n", argv[0]); return 2; }
    unsigned epochs = argc == 5 ? (unsigned)strtoul(argv[4], NULL, 10) : 10U;
    float *host_features = NULL, *host_values = NULL; unsigned count = 0;
    unsigned *host_offsets = NULL, *host_counts = NULL, label_count = 0; SparseLabel *host_labels = NULL;
    if (!epochs || read_features(argv[2], &host_features, &count) != 0 ||
        read_labels(argv[1], &host_values, &host_offsets, &host_counts, &host_labels, count, &label_count) != 0) return 1;
    if (cuewInit(CUEW_INIT_CUDA | CUEW_INIT_NVRTC) != CUEW_SUCCESS || cuInit(0) != CUDA_SUCCESS) return 77;
    CUdevice device; CUcontext context; CUmodule module; CUfunction function;
    if (cuDeviceGet(&device, 0) != CUDA_SUCCESS || cuCtxCreate(&context, 0, device) != CUDA_SUCCESS) return 77;
    nvrtcProgram program = NULL;
    if (nvrtcCreateProgram(&program, kernel_source, "tinyshogi_train.cu", 0, NULL, NULL) != NVRTC_SUCCESS) return 1;
    const char *options[] = {"--std=c++11", "--gpu-architecture=compute_52"};
    if (nvrtcCompileProgram(program, 2, options) != NVRTC_SUCCESS) return 1;
    size_t ptx_size = 0; nvrtcGetPTXSize(program, &ptx_size); char *ptx = malloc(ptx_size);
    if (!ptx || nvrtcGetPTX(program, ptx) != NVRTC_SUCCESS || cuModuleLoadData(&module, ptx) != CUDA_SUCCESS ||
        cuModuleGetFunction(&function, module, "train") != CUDA_SUCCESS) return 1;
    CUdeviceptr dx, dy, doff, dcnt, dact, dtgt, dw1, db1, dvw, dpw;
    size_t xbytes = (size_t)count * FEATURE_DIM * sizeof(float);
    size_t w1bytes = (size_t)HIDDEN_DIM * FEATURE_DIM * sizeof(float);
    size_t pbytes = (size_t)ACTION_COUNT * HIDDEN_DIM * sizeof(float);
    if (cuMemAlloc(&dx, xbytes) != CUDA_SUCCESS || cuMemAlloc(&dy, count * sizeof(float)) != CUDA_SUCCESS ||
        cuMemAlloc(&doff, count * sizeof(unsigned)) != CUDA_SUCCESS || cuMemAlloc(&dcnt, count * sizeof(unsigned)) != CUDA_SUCCESS ||
        cuMemAlloc(&dact, label_count * sizeof(unsigned)) != CUDA_SUCCESS || cuMemAlloc(&dtgt, label_count * sizeof(float)) != CUDA_SUCCESS ||
        cuMemAlloc(&dw1, w1bytes) != CUDA_SUCCESS || cuMemAlloc(&db1, HIDDEN_DIM * sizeof(float)) != CUDA_SUCCESS ||
        cuMemAlloc(&dvw, HIDDEN_DIM * sizeof(float)) != CUDA_SUCCESS || cuMemAlloc(&dpw, pbytes) != CUDA_SUCCESS) return 1;
    if (cuMemcpyHtoD(dx, host_features, xbytes) != CUDA_SUCCESS || cuMemcpyHtoD(dy, host_values, count * sizeof(float)) != CUDA_SUCCESS ||
        cuMemcpyHtoD(doff, host_offsets, count * sizeof(unsigned)) != CUDA_SUCCESS || cuMemcpyHtoD(dcnt, host_counts, count * sizeof(unsigned)) != CUDA_SUCCESS) return 1;
    float *targets = malloc(label_count * sizeof(float));
    unsigned *actions = malloc(label_count * sizeof(unsigned));
    if (!targets || !actions) return 1;
    for (unsigned i = 0; i < label_count; ++i) {
        targets[i] = host_labels[i].target;
        actions[i] = host_labels[i].action;
    }
    if (cuMemcpyHtoD(dact, actions, label_count * sizeof(unsigned)) != CUDA_SUCCESS) return 1;
    float *initial_w1 = malloc(w1bytes);
    if (!initial_w1) return 1;
    for (size_t i = 0; i < (size_t)HIDDEN_DIM * FEATURE_DIM; ++i) {
        uint32_t state = (uint32_t)(i * 747796405U + 2891336453U);
        state ^= state >> 16; initial_w1[i] = ((float)(state & 1023U) / 1023.0f - 0.5f) * 0.01f;
    }
    if (cuMemcpyHtoD(dtgt, targets, label_count * sizeof(float)) != CUDA_SUCCESS ||
        cuMemcpyHtoD(dw1, initial_w1, w1bytes) != CUDA_SUCCESS ||
        cuMemsetD8(db1, 0, HIDDEN_DIM * sizeof(float)) != CUDA_SUCCESS ||
        cuMemsetD8(dvw, 0, HIDDEN_DIM * sizeof(float)) != CUDA_SUCCESS || cuMemsetD8(dpw, 0, pbytes) != CUDA_SUCCESS) return 1;
    float learning_rate = 0.001f; int n = (int)count, dim = FEATURE_DIM;
    void *params[] = {&dx, &dy, &doff, &dcnt, &dact, &dtgt, &dw1, &db1, &dvw, &dpw, &n, &dim, &learning_rate};
    for (unsigned epoch = 0; epoch < epochs; ++epoch) {
        if (cuLaunchKernel(function, (count + 127U) / 128U, 1, 1, 128, 1, 1, 0, NULL, params, NULL) != CUDA_SUCCESS || cuCtxSynchronize() != CUDA_SUCCESS) return 1;
        printf("epoch=%u samples=%u labels=%u\n", epoch + 1, count, label_count);
    }
    float *w1 = malloc(w1bytes), *b1 = malloc(HIDDEN_DIM * sizeof(float));
    float *value_weights = malloc(HIDDEN_DIM * sizeof(float)); float *policy_weights = malloc(pbytes);
    if (!w1 || !b1 || !value_weights || !policy_weights || cuMemcpyDtoH(w1, dw1, w1bytes) != CUDA_SUCCESS ||
        cuMemcpyDtoH(b1, db1, HIDDEN_DIM * sizeof(float)) != CUDA_SUCCESS || cuMemcpyDtoH(value_weights, dvw, HIDDEN_DIM * sizeof(float)) != CUDA_SUCCESS || cuMemcpyDtoH(policy_weights, dpw, pbytes) != CUDA_SUCCESS) return 1;
    FILE *model = fopen(argv[3], "wb"); if (!model) return 1;
    fwrite("TSM2", 1, 4, model); uint32_t metadata[4] = {1, FEATURE_DIM, HIDDEN_DIM, ACTION_COUNT}; fwrite(metadata, sizeof(uint32_t), 4, model);
    fwrite(w1, sizeof(float), (size_t)HIDDEN_DIM * FEATURE_DIM, model); fwrite(b1, sizeof(float), HIDDEN_DIM, model);
    fwrite(value_weights, sizeof(float), HIDDEN_DIM, model); fwrite(policy_weights, sizeof(float), (size_t)ACTION_COUNT * HIDDEN_DIM, model); fclose(model);
    free(w1); free(b1); free(value_weights); free(policy_weights); free(initial_w1); free(targets); free(actions); free(host_features); free(host_values); free(host_offsets); free(host_counts); free(host_labels); free(ptx);
    cuMemFree(dpw); cuMemFree(dvw); cuMemFree(db1); cuMemFree(dw1); cuMemFree(dtgt); cuMemFree(dact); cuMemFree(dcnt); cuMemFree(doff); cuMemFree(dy); cuMemFree(dx); cuModuleUnload(module); cuCtxDestroy(context);
    return 0;
}
