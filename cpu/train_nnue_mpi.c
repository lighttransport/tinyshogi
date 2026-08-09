#define _POSIX_C_SOURCE 200809L

#include "../src/nnue.h"
#include "../src/nnue_data.h"

#include <limits.h>
#include <math.h>
#include <mpi.h>
#include <omp.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#define KING_BUCKETS 81U
#define BOARD_CLASSES (28U * 81U)
#define MAX_ACTIVE (SHOGI_SQUARES + 14U)
#define ROUTE_RECORDS 65536U

typedef struct {
    ShogiNdfRecord *records;
    size_t count;
    size_t capacity;
} RecordVector;

typedef struct {
    uint32_t id;
    uint32_t sample;
} Occurrence;

typedef struct {
    const char *data_path;
    const char *output_path;
    unsigned epochs;
    unsigned global_batch;
    float learning_rate;
    float momentum;
    float muon_learning_rate;
    enum { OPT_MOMENTUM, OPT_NESTEROV, OPT_MUON } optimizer;
    int32_t activation_clip;
    unsigned head_dim;
    uint64_t seed;
} Options;

static void abort_mpi(int rank, const char *message) {
    if (rank == 0) fprintf(stderr, "train_nnue_mpi: %s\n", message);
    MPI_Abort(MPI_COMM_WORLD, 1);
}

static bool parse_unsigned(const char *text, unsigned *value) {
    char *end = NULL;
    unsigned long parsed = strtoul(text, &end, 10);
    if (text[0] == '\0' || *end != '\0' || parsed > UINT_MAX) return false;
    *value = (unsigned)parsed;
    return true;
}

static bool parse_options(int argc, char **argv, Options *options) {
    *options = (Options){NULL, NULL, 5U, 2304U, 0.03f, 0.9f, 0.02f,
                         OPT_MOMENTUM, INT16_MAX, 32U, 7U};
    for (int index = 1; index < argc; ++index) {
        if (index + 1 >= argc) return false;
        const char *key = argv[index], *value = argv[++index];
        if (strcmp(key, "--data") == 0) options->data_path = value;
        else if (strcmp(key, "--output") == 0) options->output_path = value;
        else if (strcmp(key, "--epochs") == 0) {
            if (!parse_unsigned(value, &options->epochs)) return false;
        } else if (strcmp(key, "--global-batch") == 0) {
            if (!parse_unsigned(value, &options->global_batch)) return false;
        } else if (strcmp(key, "--learning-rate") == 0) {
            char *end = NULL; options->learning_rate = strtof(value, &end);
            if (*end != '\0') return false;
        } else if (strcmp(key, "--momentum") == 0) {
            char *end = NULL; options->momentum = strtof(value, &end);
            if (*end != '\0') return false;
        } else if (strcmp(key, "--muon-learning-rate") == 0) {
            char *end = NULL; options->muon_learning_rate = strtof(value, &end);
            if (*end != '\0') return false;
        } else if (strcmp(key, "--optimizer") == 0) {
            if (strcmp(value, "momentum") == 0) options->optimizer = OPT_MOMENTUM;
            else if (strcmp(value, "nesterov") == 0) options->optimizer = OPT_NESTEROV;
            else if (strcmp(value, "muon") == 0) options->optimizer = OPT_MUON;
            else return false;
        } else if (strcmp(key, "--activation-clip") == 0) {
            char *end = NULL; long parsed = strtol(value, &end, 10);
            if (*end != '\0' || parsed < 1 || parsed > INT16_MAX) return false;
            options->activation_clip = (int32_t)parsed;
        } else if (strcmp(key, "--head-dim") == 0) {
            if (!parse_unsigned(value, &options->head_dim)) return false;
        } else if (strcmp(key, "--seed") == 0) {
            char *end = NULL; options->seed = strtoull(value, &end, 10);
            if (*end != '\0') return false;
        } else return false;
    }
    return options->data_path != NULL && options->output_path != NULL &&
           options->epochs > 0 && options->global_batch > 0 &&
           options->learning_rate > 0.0f && options->momentum >= 0.0f &&
           options->momentum < 1.0f && options->muon_learning_rate > 0.0f &&
           options->head_dim == 32U;
}

static unsigned record_bucket(const ShogiNdfRecord *record) {
    unsigned side = record->side;
    for (unsigned square = 0; square < SHOGI_SQUARES; ++square) {
        unsigned piece = record->board[square];
        if (piece != SHOGI_EMPTY && (piece & 0x0fU) == SHOGI_KING &&
            (piece >> 4) == side)
            return side == SHOGI_BLACK ? square : SHOGI_SQUARES - 1U - square;
    }
    return KING_BUCKETS;
}

static bool vector_append(RecordVector *vector, const ShogiNdfRecord *record) {
    if (vector->count == vector->capacity) {
        size_t next = vector->capacity == 0 ? 4096U : vector->capacity * 2U;
        ShogiNdfRecord *records = realloc(vector->records, next * sizeof(*records));
        if (records == NULL) return false;
        vector->records = records;
        vector->capacity = next;
    }
    vector->records[vector->count++] = *record;
    return true;
}

static FILE *open_ndf(const char *path, uint32_t *count) {
    FILE *file = fopen(path, "rb");
    if (file == NULL || !shogi_ndf_read_header(file, count)) {
        if (file != NULL) fclose(file);
        return NULL;
    }
    return file;
}

static void assign_owners(const uint64_t counts[KING_BUCKETS], int ranks,
                          int owners[KING_BUCKETS]) {
    uint64_t loads[KING_BUCKETS] = {0};
    for (unsigned bucket = 0; bucket < KING_BUCKETS; ++bucket) owners[bucket] = -1;
    for (unsigned assigned = 0; assigned < KING_BUCKETS; ++assigned) {
        unsigned bucket = 0;
        for (unsigned candidate = 1; candidate < KING_BUCKETS; ++candidate)
            if (owners[candidate] < 0 &&
                (owners[bucket] >= 0 || counts[candidate] > counts[bucket]))
                bucket = candidate;
        int owner = 0;
        for (int rank = 1; rank < ranks; ++rank)
            if (loads[rank] < loads[owner]) owner = rank;
        owners[bucket] = owner;
        loads[owner] += counts[bucket];
    }
}

static void count_buckets(FILE *file, uint32_t count,
                          uint64_t local[KING_BUCKETS], int rank) {
    ShogiNdfRecord *buffer = malloc(ROUTE_RECORDS * sizeof(*buffer));
    if (buffer == NULL) abort_mpi(rank, "cannot allocate routing buffer");
    uint32_t remaining = count;
    while (remaining != 0) {
        size_t amount = remaining < ROUTE_RECORDS ? remaining : ROUTE_RECORDS;
        if (fread(buffer, sizeof(*buffer), amount, file) != amount)
            abort_mpi(rank, "truncated NDF1 input");
        for (size_t index = 0; index < amount; ++index) {
            unsigned bucket = record_bucket(&buffer[index]);
            if (bucket >= KING_BUCKETS) abort_mpi(rank, "record has no perspective king");
            ++local[bucket];
        }
        remaining -= (uint32_t)amount;
    }
    free(buffer);
}

static void route_records(FILE *file, uint32_t local_count,
                          const int owners[KING_BUCKETS], int rank, int ranks,
                          RecordVector buckets[KING_BUCKETS]) {
    ShogiNdfRecord *input = malloc(ROUTE_RECORDS * sizeof(*input));
    int *send_counts = calloc((size_t)ranks, sizeof(*send_counts));
    int *recv_counts = calloc((size_t)ranks, sizeof(*recv_counts));
    int *send_displs = calloc((size_t)ranks, sizeof(*send_displs));
    int *recv_displs = calloc((size_t)ranks, sizeof(*recv_displs));
    if (input == NULL || send_counts == NULL || recv_counts == NULL ||
        send_displs == NULL || recv_displs == NULL)
        abort_mpi(rank, "cannot allocate routing metadata");
    MPI_Datatype record_type;
    MPI_Type_contiguous((int)sizeof(ShogiNdfRecord), MPI_BYTE, &record_type);
    MPI_Type_commit(&record_type);
    uint32_t rounds = (local_count + ROUTE_RECORDS - 1U) / ROUTE_RECORDS, max_rounds;
    MPI_Allreduce(&rounds, &max_rounds, 1, MPI_UNSIGNED, MPI_MAX, MPI_COMM_WORLD);
    uint32_t remaining = local_count;
    for (uint32_t round = 0; round < max_rounds; ++round) {
        size_t amount = remaining < ROUTE_RECORDS ? remaining : ROUTE_RECORDS;
        if (amount != 0 && fread(input, sizeof(*input), amount, file) != amount)
            abort_mpi(rank, "truncated NDF1 during routing");
        memset(send_counts, 0, (size_t)ranks * sizeof(*send_counts));
        for (size_t index = 0; index < amount; ++index)
            ++send_counts[owners[record_bucket(&input[index])]];
        int send_total = 0;
        for (int peer = 0; peer < ranks; ++peer) {
            send_displs[peer] = send_total;
            send_total += send_counts[peer];
        }
        ShogiNdfRecord *send = malloc((size_t)(send_total == 0 ? 1 : send_total) * sizeof(*send));
        int *cursor = malloc((size_t)ranks * sizeof(*cursor));
        if (send == NULL || cursor == NULL) abort_mpi(rank, "cannot allocate send buffer");
        memcpy(cursor, send_displs, (size_t)ranks * sizeof(*cursor));
        for (size_t index = 0; index < amount; ++index) {
            int owner = owners[record_bucket(&input[index])];
            send[cursor[owner]++] = input[index];
        }
        MPI_Alltoall(send_counts, 1, MPI_INT, recv_counts, 1, MPI_INT, MPI_COMM_WORLD);
        int recv_total = 0;
        for (int peer = 0; peer < ranks; ++peer) {
            recv_displs[peer] = recv_total;
            recv_total += recv_counts[peer];
        }
        ShogiNdfRecord *recv = malloc((size_t)(recv_total == 0 ? 1 : recv_total) * sizeof(*recv));
        if (recv == NULL) abort_mpi(rank, "cannot allocate receive buffer");
        MPI_Alltoallv(send, send_counts, send_displs, record_type,
                      recv, recv_counts, recv_displs, record_type, MPI_COMM_WORLD);
        for (int index = 0; index < recv_total; ++index) {
            unsigned bucket = record_bucket(&recv[index]);
            if (owners[bucket] != rank || !vector_append(&buckets[bucket], &recv[index]))
                abort_mpi(rank, "cannot retain routed record");
        }
        free(recv); free(cursor); free(send);
        remaining -= (uint32_t)amount;
    }
    MPI_Type_free(&record_type);
    free(recv_displs); free(send_displs); free(recv_counts); free(send_counts); free(input);
}

static uint64_t random_next(uint64_t *state) {
    uint64_t value = (*state += UINT64_C(0x9e3779b97f4a7c15));
    value = (value ^ (value >> 30)) * UINT64_C(0xbf58476d1ce4e5b9);
    value = (value ^ (value >> 27)) * UINT64_C(0x94d049bb133111eb);
    return value ^ (value >> 31);
}

static float initial_weight(uint64_t index, uint64_t seed) {
    uint64_t state = index ^ (seed * UINT64_C(0xd6e8feb86659fd93));
    uint64_t value = random_next(&state);
    return ((float)((value >> 40) & 0xffffffU) / 16777216.0f * 2.0f - 1.0f) * 0.01f;
}

static void shuffle_bucket(RecordVector *bucket, uint64_t seed) {
    for (size_t index = bucket->count; index > 1; --index) {
        size_t other = (size_t)(random_next(&seed) % index);
        ShogiNdfRecord temporary = bucket->records[index - 1U];
        bucket->records[index - 1U] = bucket->records[other];
        bucket->records[other] = temporary;
    }
}

static void make_position(const ShogiNdfRecord *record, ShogiPosition *position) {
    memset(position, 0, sizeof(*position));
    memcpy(position->board, record->board, sizeof(record->board));
    memcpy(position->hand, record->hand, sizeof(record->hand));
    position->side = (ShogiColor)record->side;
    position->king_square[0] = position->king_square[1] = SHOGI_SQ_NONE;
    for (uint8_t square = 0; square < SHOGI_SQUARES; ++square) {
        uint8_t piece = position->board[square];
        if (piece != SHOGI_EMPTY && (piece & 0x0fU) == SHOGI_KING)
            position->king_square[piece >> 4] = square;
    }
}

static void radix_sort_occurrences(Occurrence *values, Occurrence *scratch,
                                   size_t count) {
    enum { RADIX_BITS = 11, RADIX = 1 << RADIX_BITS };
    size_t bins[RADIX];
    Occurrence *source = values, *target = scratch;
    for (unsigned shift = 0; shift < 22; shift += RADIX_BITS) {
        memset(bins, 0, sizeof(bins));
        for (size_t i = 0; i < count; ++i)
            ++bins[(source[i].id >> shift) & (RADIX - 1U)];
        size_t offset = 0;
        for (unsigned bin = 0; bin < RADIX; ++bin) {
            size_t amount = bins[bin]; bins[bin] = offset; offset += amount;
        }
        for (size_t i = 0; i < count; ++i)
            target[bins[(source[i].id >> shift) & (RADIX - 1U)]++] = source[i];
        Occurrence *temporary = source; source = target; target = temporary;
    }
    if (source != values) memcpy(values, source, count * sizeof(*values));
}

static int16_t quantize(float value, float scale) {
    long rounded = lroundf(value * scale);
    if (rounded > INT16_MAX) rounded = INT16_MAX;
    if (rounded < INT16_MIN) rounded = INT16_MIN;
    return (int16_t)rounded;
}

static bool save_model(const char *path, const float *features, const float *head,
                       const float *head_bias, const float *final,
                       const float *final_bias, int32_t activation_clip) {
    ShogiNnueModel model;
    shogi_nnue_model_init(&model);
    model.feature_count = SHOGI_NNUE_FEATURE_COUNT;
    model.hidden_dim = SHOGI_NNUE_DEFAULT_HIDDEN;
    model.head_dim = 32U;
    model.format_version = SHOGI_NNUE3_FORMAT_VERSION;
    model.feature_scale = 256;
    model.output_scale = 1024;
    model.activation_clip = activation_clip;
    model.head_clip = INT16_MAX;
    model.head_shift = 8;
    size_t feature_count = (size_t)model.feature_count * model.hidden_dim;
    size_t head_count = 2U * model.head_dim * model.hidden_dim;
    model.feature_weights = malloc(feature_count * sizeof(*model.feature_weights));
    model.head_weights = malloc(head_count * sizeof(*model.head_weights));
    model.head_bias = malloc(2U * model.head_dim * sizeof(*model.head_bias));
    model.final_weights = malloc(2U * model.head_dim * sizeof(*model.final_weights));
    model.final_bias = malloc(2U * sizeof(*model.final_bias));
    if (model.feature_weights == NULL || model.head_weights == NULL ||
        model.head_bias == NULL || model.final_weights == NULL || model.final_bias == NULL) {
        shogi_nnue_model_destroy(&model);
        return false;
    }
    for (size_t i = 0; i < feature_count; ++i)
        model.feature_weights[i] = quantize(features[i], 256.0f);
    for (size_t i = 0; i < head_count; ++i)
        model.head_weights[i] = quantize(head[i], 256.0f);
    for (size_t i = 0; i < 64U; ++i) {
        model.head_bias[i] = (int64_t)llround((double)head_bias[i] * 65536.0);
        model.final_weights[i] = quantize(final[i], 1024.0f);
    }
    for (size_t i = 0; i < 2U; ++i)
        model.final_bias[i] = (int64_t)llround((double)final_bias[i] * 262144.0);
    bool ok = shogi_nnue_model_save(&model, path);
    shogi_nnue_model_destroy(&model);
    return ok;
}

static void lazy_momentum(float *weight, float *velocity, uint64_t *last_step,
                          const float *gradient, uint64_t step, float rate,
                          float momentum, size_t count, bool nesterov) {
    uint64_t skipped = step - *last_step - 1U;
    if (skipped != 0 && momentum != 0.0f) {
        float decay = powf(momentum, (float)skipped);
        float drift = (nesterov ? momentum * momentum : momentum) *
                      (1.0f - decay) / (1.0f - momentum);
        for (size_t unit = 0; unit < count; ++unit) {
            weight[unit] -= rate * velocity[unit] * drift;
            velocity[unit] *= decay;
        }
    }
    for (size_t unit = 0; unit < count; ++unit) {
        velocity[unit] = momentum * velocity[unit] + gradient[unit];
        float update = nesterov ? gradient[unit] + momentum * velocity[unit]
                                : velocity[unit];
        weight[unit] -= rate * update;
    }
    *last_step = step;
}

static void flush_momentum(float *weight, float *velocity, uint64_t *last_step,
                           uint64_t step, float rate, float momentum, size_t count,
                           bool nesterov) {
    uint64_t skipped = step - *last_step;
    if (skipped != 0 && momentum != 0.0f) {
        float decay = powf(momentum, (float)skipped);
        float drift = (nesterov ? momentum * momentum : momentum) *
                      (1.0f - decay) / (1.0f - momentum);
        for (size_t unit = 0; unit < count; ++unit) {
            weight[unit] -= rate * velocity[unit] * drift;
            velocity[unit] *= decay;
        }
    }
    *last_step = step;
}

/* Orthogonalize a rows x cols update with Muon's quintic Newton-Schulz map. */
static void muon_step(float *weight, float *velocity, const float *gradient,
                      unsigned rows, unsigned cols, float rate, float momentum,
                      float *workspace) {
    size_t count = (size_t)rows * cols;
    float norm2 = 1.0e-14f;
#pragma omp parallel for schedule(static)
    for (size_t i = 0; i < count; ++i) {
        velocity[i] = momentum * velocity[i] + (1.0f - momentum) * gradient[i];
    }
    size_t square = (size_t)rows * rows;
    float *x = workspace;
    float *y = x + count;
    float *a = y + count;
    float *b = a + square;
#pragma omp parallel for schedule(static) reduction(+:norm2)
    for (size_t i = 0; i < count; ++i) {
        x[i] = (1.0f - momentum) * gradient[i] + momentum * velocity[i];
        norm2 += x[i] * x[i];
    }
    float inverse_norm = 1.0f / sqrtf(norm2);
#pragma omp parallel for schedule(static)
    for (size_t i = 0; i < count; ++i) x[i] *= inverse_norm;
    for (unsigned iteration = 0; iteration < 5; ++iteration) {
#pragma omp parallel for schedule(static)
        for (unsigned i = 0; i < rows; ++i)
            for (unsigned j = 0; j <= i; ++j) {
                float sum = 0.0f;
                for (unsigned k = 0; k < cols; ++k) sum += x[(size_t)i * cols + k] * x[(size_t)j * cols + k];
                a[(size_t)i * rows + j] = sum;
                a[(size_t)j * rows + i] = sum;
            }
#pragma omp parallel for schedule(static)
        for (unsigned i = 0; i < rows; ++i)
            for (unsigned j = 0; j <= i; ++j) {
                float sum = 0.0f;
                for (unsigned k = 0; k < rows; ++k) sum += a[(size_t)i * rows + k] * a[(size_t)k * rows + j];
                float value = -4.7750f * a[(size_t)i * rows + j] + 2.0315f * sum;
                b[(size_t)i * rows + j] = value;
                b[(size_t)j * rows + i] = value;
            }
#pragma omp parallel for schedule(static)
        for (unsigned i = 0; i < rows; ++i)
        {
            float *output = y + (size_t)i * cols;
            const float *input_row = x + (size_t)i * cols;
#pragma omp simd
            for (unsigned k = 0; k < cols; ++k)
                output[k] = 3.4445f * input_row[k];
            for (unsigned j = 0; j < rows; ++j) {
                float coefficient = b[(size_t)i * rows + j];
                const float *source = x + (size_t)j * cols;
#pragma omp simd
                for (unsigned k = 0; k < cols; ++k)
                    output[k] += coefficient * source[k];
            }
        }
        float *temporary = x; x = y; y = temporary;
    }
#pragma omp parallel for schedule(static)
    for (size_t i = 0; i < count; ++i) weight[i] -= rate * x[i];
}

int main(int argc, char **argv) {
    int provided;
    MPI_Init_thread(&argc, &argv, MPI_THREAD_FUNNELED, &provided);
    int rank, ranks;
    MPI_Comm_rank(MPI_COMM_WORLD, &rank);
    MPI_Comm_size(MPI_COMM_WORLD, &ranks);
    if (provided < MPI_THREAD_FUNNELED) abort_mpi(rank, "MPI thread support is insufficient");
    Options options;
    if (!parse_options(argc, argv, &options))
        abort_mpi(rank, "usage: --data PATH --output PATH [--epochs N --global-batch N --optimizer momentum|nesterov|muon --learning-rate F --muon-learning-rate F --momentum F --activation-clip N --head-dim 32 --seed N]");

    uint32_t local_count;
    FILE *input = open_ndf(options.data_path, &local_count);
    if (input == NULL) abort_mpi(rank, "cannot open local NDF1 input");
    uint64_t local_buckets[KING_BUCKETS] = {0}, global_buckets[KING_BUCKETS];
    count_buckets(input, local_count, local_buckets, rank);
    MPI_Allreduce(local_buckets, global_buckets, KING_BUCKETS, MPI_UINT64_T,
                  MPI_SUM, MPI_COMM_WORLD);
    uint64_t global_count = 0;
    for (unsigned bucket = 0; bucket < KING_BUCKETS; ++bucket)
        global_count += global_buckets[bucket];
    if (global_count == 0) abort_mpi(rank, "training set is empty");
    int owners[KING_BUCKETS];
    assign_owners(global_buckets, ranks, owners);
    if (rank == 0) {
        uint64_t *owner_loads = calloc((size_t)ranks, sizeof(*owner_loads));
        if (owner_loads == NULL) abort_mpi(rank, "cannot allocate owner diagnostics");
        unsigned nonempty = 0;
        for (unsigned bucket = 0; bucket < KING_BUCKETS; ++bucket) {
            owner_loads[owners[bucket]] += global_buckets[bucket];
            if (global_buckets[bucket] != 0) ++nonempty;
        }
        uint64_t maximum = owner_loads[0];
        for (int owner = 1; owner < ranks; ++owner)
            if (owner_loads[owner] > maximum) maximum = owner_loads[owner];
        double balance = maximum == 0 ? 1.0 :
            (double)global_count / ((double)ranks * (double)maximum);
        fprintf(stderr,
                "nnue-mpi data records=%llu nonempty-king-buckets=%u "
                "maximum-owner-load=%llu owner-balance=%.1f%%\n",
                (unsigned long long)global_count, nonempty,
                (unsigned long long)maximum, balance * 100.0);
        free(owner_loads);
    }
    rewind(input);
    if (!shogi_ndf_read_header(input, &local_count)) abort_mpi(rank, "cannot rewind NDF1");
    RecordVector buckets[KING_BUCKETS] = {{0}};
    for (unsigned bucket = 0; bucket < KING_BUCKETS; ++bucket) {
        if (owners[bucket] != rank || global_buckets[bucket] == 0) continue;
        if (global_buckets[bucket] > SIZE_MAX / sizeof(ShogiNdfRecord))
            abort_mpi(rank, "owned bucket is too large");
        buckets[bucket].capacity = (size_t)global_buckets[bucket];
        buckets[bucket].records = malloc(buckets[bucket].capacity *
                                          sizeof(*buckets[bucket].records));
        if (buckets[bucket].records == NULL)
            abort_mpi(rank, "cannot preallocate owned bucket");
    }
    route_records(input, local_count, owners, rank, ranks, buckets);
    fclose(input);
    uint64_t routed = 0;
    for (unsigned bucket = 0; bucket < KING_BUCKETS; ++bucket) routed += buckets[bucket].count;
    uint64_t routed_global;
    MPI_Allreduce(&routed, &routed_global, 1, MPI_UINT64_T, MPI_SUM, MPI_COMM_WORLD);
    if (routed_global != global_count) abort_mpi(rank, "routed record count mismatch");

    enum { HIDDEN = SHOGI_NNUE_DEFAULT_HIDDEN, HEAD = 32 };
    size_t feature_values = (size_t)SHOGI_NNUE_FEATURE_COUNT * HIDDEN;
    size_t board_values = (size_t)SHOGI_NNUE_BOARD_FEATURES * HIDDEN;
    size_t head_values = 2U * HEAD * HIDDEN;
    float *weights = calloc(feature_values, sizeof(*weights));
    float *velocity = calloc(feature_values, sizeof(*velocity));
    float *feature_gradient = calloc(feature_values, sizeof(*feature_gradient));
    uint64_t *last_step = calloc(SHOGI_NNUE_FEATURE_COUNT, sizeof(*last_step));
    float *head = malloc(head_values * sizeof(*head));
    float *head_velocity = calloc(head_values, sizeof(*head_velocity));
    float *head_gradient = calloc(head_values, sizeof(*head_gradient));
    float *head_bias = calloc(64U, sizeof(*head_bias));
    float *head_bias_velocity = calloc(64U, sizeof(*head_bias_velocity));
    float *head_bias_gradient = calloc(64U, sizeof(*head_bias_gradient));
    float *final = malloc(64U * sizeof(*final));
    float *final_velocity = calloc(64U, sizeof(*final_velocity));
    float *final_gradient = calloc(64U, sizeof(*final_gradient));
    float *final_bias = calloc(2U, sizeof(*final_bias));
    float *final_bias_velocity = calloc(2U, sizeof(*final_bias_velocity));
    float *final_bias_gradient = calloc(2U, sizeof(*final_bias_gradient));
    size_t muon_workspace_values = 2U * HEAD * HIDDEN + 2U * HEAD * HEAD;
    float *muon_workspace = malloc(muon_workspace_values * sizeof(*muon_workspace));
    if (weights == NULL || velocity == NULL || feature_gradient == NULL || last_step == NULL ||
        head == NULL || head_velocity == NULL || head_gradient == NULL || head_bias == NULL ||
        head_bias_velocity == NULL || head_bias_gradient == NULL || final == NULL ||
        final_velocity == NULL || final_gradient == NULL || final_bias == NULL ||
        final_bias_velocity == NULL || final_bias_gradient == NULL ||
        muon_workspace == NULL)
        abort_mpi(rank, "cannot allocate model and optimizer");

#pragma omp parallel for schedule(static)
    for (unsigned bucket = 0; bucket < KING_BUCKETS; ++bucket) {
        if (owners[bucket] != rank) continue;
        size_t first = (size_t)bucket * BOARD_CLASSES * HIDDEN;
        size_t count = (size_t)BOARD_CLASSES * HIDDEN;
        for (size_t index = 0; index < count; ++index)
            weights[first + index] = initial_weight(first + index, options.seed);
    }
    for (size_t index = board_values; index < feature_values; ++index)
        weights[index] = initial_weight(index, options.seed);
    for (size_t index = 0; index < head_values; ++index)
        head[index] = initial_weight(feature_values + index, options.seed);
    for (size_t index = 0; index < 64U; ++index)
        final[index] = initial_weight(feature_values + head_values + index, options.seed);

    size_t max_local_batch = options.global_batch;
    ShogiNdfRecord *batch = malloc(max_local_batch * sizeof(*batch));
    float *hidden = malloc(max_local_batch * HIDDEN * sizeof(*hidden));
    float *dhidden = malloc(max_local_batch * HIDDEN * sizeof(*dhidden));
    float *head_raw = malloc(max_local_batch * HEAD * sizeof(*head_raw));
    float *head_act = malloc(max_local_batch * HEAD * sizeof(*head_act));
    float *dhead = malloc(max_local_batch * HEAD * sizeof(*dhead));
    uint32_t *ids = malloc(max_local_batch * MAX_ACTIVE * sizeof(*ids));
    uint16_t *active = malloc(max_local_batch * sizeof(*active));
    Occurrence *occurrences = malloc(max_local_batch * MAX_ACTIVE * sizeof(*occurrences));
    Occurrence *occurrence_scratch = malloc(max_local_batch * MAX_ACTIVE *
                                             sizeof(*occurrence_scratch));
    size_t *group_starts = malloc((max_local_batch * MAX_ACTIVE + 1U) *
                                  sizeof(*group_starts));
    size_t hand_values = (size_t)SHOGI_NNUE_HAND_FEATURES * HIDDEN;
    size_t sync_count = hand_values + head_values + 64U + 64U + 2U;
    float *sync = malloc(sync_count * sizeof(*sync));
    if (batch == NULL || hidden == NULL || dhidden == NULL || head_raw == NULL ||
        head_act == NULL || dhead == NULL || ids == NULL || active == NULL ||
        occurrences == NULL || occurrence_scratch == NULL || group_starts == NULL ||
        sync == NULL)
        abort_mpi(rank, "cannot allocate minibatch workspace");

    shogi_init();
    uint64_t steps_per_epoch = (global_count + options.global_batch - 1U) /
                               options.global_batch;
    uint64_t step_number = 0;
    for (unsigned epoch = 0; epoch < options.epochs; ++epoch) {
        size_t offsets[KING_BUCKETS] = {0};
        for (unsigned bucket = 0; bucket < KING_BUCKETS; ++bucket)
            if (owners[bucket] == rank)
                shuffle_bucket(&buckets[bucket], options.seed ^
                    ((uint64_t)epoch << 32) ^ bucket);
        double epoch_loss = 0.0;
        uint64_t epoch_samples = 0;
        double epoch_start = MPI_Wtime(), communication = 0.0;
        for (uint64_t step = 0; step < steps_per_epoch; ++step) {
            uint64_t start = step * options.global_batch;
            uint64_t end = start + options.global_batch;
            if (end > global_count) end = global_count;
            size_t local_batch = 0;
            for (unsigned bucket = 0; bucket < KING_BUCKETS; ++bucket) {
                if (owners[bucket] != rank) continue;
                uint64_t begin_quota = start * global_buckets[bucket] / global_count;
                uint64_t end_quota = end * global_buckets[bucket] / global_count;
                size_t amount = (size_t)(end_quota - begin_quota);
                if (offsets[bucket] + amount > buckets[bucket].count ||
                    local_batch + amount > max_local_batch)
                    abort_mpi(rank, "stratified minibatch overflow");
                memcpy(batch + local_batch, buckets[bucket].records + offsets[bucket],
                       amount * sizeof(*batch));
                offsets[bucket] += amount;
                local_batch += amount;
            }
            uint64_t actual_global;
            uint64_t local_batch_u64 = local_batch;
            MPI_Allreduce(&local_batch_u64, &actual_global, 1, MPI_UINT64_T,
                          MPI_SUM, MPI_COMM_WORLD);
            if (actual_global == 0) continue;
            memset(head_gradient, 0, head_values * sizeof(*head_gradient));
            memset(head_bias_gradient, 0, 64U * sizeof(*head_bias_gradient));
            memset(final_gradient, 0, 64U * sizeof(*final_gradient));
            memset(final_bias_gradient, 0, 2U * sizeof(*final_bias_gradient));
            size_t occurrence_count = 0;
            double local_loss = 0.0;
#pragma omp parallel for schedule(static) reduction(+:local_loss)
            for (size_t sample = 0; sample < local_batch; ++sample) {
                ShogiPosition position;
                make_position(&batch[sample], &position);
                uint32_t *sample_ids = ids + sample * MAX_ACTIVE;
                size_t count = shogi_nnue_feature_ids(&position, position.side,
                                                       sample_ids, MAX_ACTIVE);
                active[sample] = (uint16_t)count;
                float *sample_hidden = hidden + sample * HIDDEN;
                memset(sample_hidden, 0, HIDDEN * sizeof(*sample_hidden));
                for (size_t item = 0; item < count; ++item) {
                    const float *row = weights + (size_t)sample_ids[item] * HIDDEN;
                    for (unsigned unit = 0; unit < HIDDEN; ++unit)
                        sample_hidden[unit] += row[unit];
                }
                for (unsigned unit = 0; unit < HIDDEN; ++unit) {
                    if (sample_hidden[unit] < 0.0f) sample_hidden[unit] = 0.0f;
                    float clip = (float)options.activation_clip / 256.0f;
                    if (sample_hidden[unit] > clip) sample_hidden[unit] = clip;
                }
                unsigned side = batch[sample].side;
                float prediction = final_bias[side];
                for (unsigned h = 0; h < HEAD; ++h) {
                    float value = head_bias[side * HEAD + h];
                    const float *row = head + ((size_t)side * HEAD + h) * HIDDEN;
                    for (unsigned unit = 0; unit < HIDDEN; ++unit)
                        value += sample_hidden[unit] * row[unit];
                    head_raw[sample * HEAD + h] = value;
                    float activation = value > 0.0f ? value : 0.0f;
                    head_act[sample * HEAD + h] = activation;
                    prediction += activation * final[side * HEAD + h];
                }
                prediction = tanhf(prediction);
                float target = (float)batch[sample].value / 1000.0f;
                float error = target - prediction;
                local_loss += (double)error * error;
                float gradient = -2.0f * error * (1.0f - prediction * prediction);
                float *sample_dhidden = dhidden + sample * HIDDEN;
                memset(sample_dhidden, 0, HIDDEN * sizeof(*sample_dhidden));
                for (unsigned h = 0; h < HEAD; ++h) {
                    float dh = head_raw[sample * HEAD + h] > 0.0f ?
                        gradient * final[side * HEAD + h] : 0.0f;
                    dhead[sample * HEAD + h] = dh;
                    const float *row = head + ((size_t)side * HEAD + h) * HIDDEN;
                    for (unsigned unit = 0; unit < HIDDEN; ++unit)
                        sample_dhidden[unit] += dh * row[unit];
                }
                for (unsigned unit = 0; unit < HIDDEN; ++unit)
                    if (sample_hidden[unit] <= 0.0f ||
                        sample_hidden[unit] >= (float)options.activation_clip / 256.0f)
                        sample_dhidden[unit] = 0.0f;
            }
            for (size_t sample = 0; sample < local_batch; ++sample)
                for (unsigned item = 0; item < active[sample]; ++item)
                    occurrences[occurrence_count++] =
                        (Occurrence){ids[sample * MAX_ACTIVE + item], (uint32_t)sample};
            radix_sort_occurrences(occurrences, occurrence_scratch, occurrence_count);
            size_t group_count = 0;
            for (size_t index = 0; index < occurrence_count;) {
                uint32_t id = occurrences[index].id;
                size_t next = index + 1U;
                while (next < occurrence_count && occurrences[next].id == id) ++next;
                ++group_count;
                index = next;
            }
            size_t group = 0;
            for (size_t index = 0; index < occurrence_count;) {
                group_starts[group++] = index;
                uint32_t id = occurrences[index].id;
                do { ++index; } while (index < occurrence_count && occurrences[index].id == id);
            }
            group_starts[group_count] = occurrence_count;
#pragma omp parallel for schedule(dynamic, 8)
            for (size_t g = 0; g < group_count; ++g) {
                size_t first = group_starts[g], last = group_starts[g + 1U];
                uint32_t id = occurrences[first].id;
                float *gradient = feature_gradient + (size_t)id * HIDDEN;
                memset(gradient, 0, HIDDEN * sizeof(*gradient));
                for (size_t item = first; item < last; ++item) {
                    const float *sample_gradient = dhidden +
                        (size_t)occurrences[item].sample * HIDDEN;
                    for (unsigned unit = 0; unit < HIDDEN; ++unit)
                        gradient[unit] += sample_gradient[unit];
                }
            }
#pragma omp parallel for collapse(2) schedule(static)
            for (unsigned side = 0; side < 2; ++side)
                for (unsigned h = 0; h < HEAD; ++h) {
                    float bias_sum = 0.0f;
                    for (size_t sample = 0; sample < local_batch; ++sample) {
                        if (batch[sample].side != side) continue;
                        float dh = dhead[sample * HEAD + h];
                        bias_sum += dh;
                        for (unsigned unit = 0; unit < HIDDEN; ++unit)
                            head_gradient[((size_t)side * HEAD + h) * HIDDEN + unit] +=
                                dh * hidden[sample * HIDDEN + unit];
                    }
                    head_bias_gradient[side * HEAD + h] = bias_sum;
                }
            /* Final-layer gradients need the prediction derivative. Reconstruct it
             * from dhead/final when possible and evaluate directly for stability. */
            for (size_t sample = 0; sample < local_batch; ++sample) {
                unsigned side = batch[sample].side;
                float prediction = final_bias[side];
                for (unsigned h = 0; h < HEAD; ++h)
                    prediction += head_act[sample * HEAD + h] * final[side * HEAD + h];
                prediction = tanhf(prediction);
                float target = (float)batch[sample].value / 1000.0f;
                float gradient = -2.0f * (target - prediction) *
                                 (1.0f - prediction * prediction);
                final_bias_gradient[side] += gradient;
                for (unsigned h = 0; h < HEAD; ++h)
                    final_gradient[side * HEAD + h] +=
                        gradient * head_act[sample * HEAD + h];
            }
            float inverse = 1.0f / (float)actual_global;
            size_t hand_first = SHOGI_NNUE_BOARD_FEATURES;
            size_t cursor = 0;
            memcpy(sync + cursor, feature_gradient + hand_first * HIDDEN,
                   hand_values * sizeof(*sync)); cursor += hand_values;
            memcpy(sync + cursor, head_gradient, head_values * sizeof(*sync)); cursor += head_values;
            memcpy(sync + cursor, head_bias_gradient, 64U * sizeof(*sync)); cursor += 64U;
            memcpy(sync + cursor, final_gradient, 64U * sizeof(*sync)); cursor += 64U;
            memcpy(sync + cursor, final_bias_gradient, 2U * sizeof(*sync));
            double communication_start = MPI_Wtime();
            MPI_Allreduce(MPI_IN_PLACE, sync, (int)sync_count, MPI_FLOAT, MPI_SUM,
                          MPI_COMM_WORLD);
            communication += MPI_Wtime() - communication_start;
            cursor = 0;
            memcpy(feature_gradient + hand_first * HIDDEN, sync + cursor,
                   hand_values * sizeof(*sync)); cursor += hand_values;
            memcpy(head_gradient, sync + cursor, head_values * sizeof(*sync)); cursor += head_values;
            memcpy(head_bias_gradient, sync + cursor, 64U * sizeof(*sync)); cursor += 64U;
            memcpy(final_gradient, sync + cursor, 64U * sizeof(*sync)); cursor += 64U;
            memcpy(final_bias_gradient, sync + cursor, 2U * sizeof(*sync));
            ++step_number;
            bool nesterov = options.optimizer == OPT_NESTEROV;
#pragma omp parallel for schedule(dynamic, 8)
            for (size_t g = 0; g < group_count; ++g) {
                uint32_t id = occurrences[group_starts[g]].id;
                if (id >= SHOGI_NNUE_BOARD_FEATURES) continue;
                float *gradient = feature_gradient + (size_t)id * HIDDEN;
                for (unsigned unit = 0; unit < HIDDEN; ++unit) gradient[unit] *= inverse;
                lazy_momentum(weights + (size_t)id * HIDDEN,
                              velocity + (size_t)id * HIDDEN, &last_step[id],
                              gradient, step_number, options.learning_rate,
                              options.momentum, HIDDEN, nesterov);
                memset(gradient, 0, HIDDEN * sizeof(*gradient));
            }
#pragma omp parallel for schedule(static)
            for (unsigned feature = 0; feature < SHOGI_NNUE_HAND_FEATURES; ++feature) {
                uint32_t id = SHOGI_NNUE_BOARD_FEATURES + feature;
                float *gradient = feature_gradient + (size_t)id * HIDDEN;
                for (unsigned unit = 0; unit < HIDDEN; ++unit) gradient[unit] *= inverse;
                lazy_momentum(weights + (size_t)id * HIDDEN,
                              velocity + (size_t)id * HIDDEN, &last_step[id], gradient,
                              step_number, options.learning_rate, options.momentum,
                              HIDDEN, nesterov);
                memset(gradient, 0, HIDDEN * sizeof(*gradient));
            }
            if (options.optimizer == OPT_MUON) {
                for (unsigned side = 0; side < 2; ++side) {
                    float *gradient = head_gradient + (size_t)side * HEAD * HIDDEN;
                    for (size_t index = 0; index < (size_t)HEAD * HIDDEN; ++index)
                        gradient[index] *= inverse;
                    int matrix_owner = (int)side % ranks;
                    if (rank == matrix_owner)
                        muon_step(head + (size_t)side * HEAD * HIDDEN,
                                  head_velocity + (size_t)side * HEAD * HIDDEN,
                                  gradient, HEAD, HIDDEN,
                                  options.muon_learning_rate, options.momentum,
                                  muon_workspace);
                    double broadcast_start = MPI_Wtime();
                    MPI_Bcast(head + (size_t)side * HEAD * HIDDEN,
                              HEAD * HIDDEN, MPI_FLOAT, matrix_owner, MPI_COMM_WORLD);
                    communication += MPI_Wtime() - broadcast_start;
                }
            } else {
#pragma omp parallel for schedule(static)
                for (size_t index = 0; index < head_values; ++index) {
                    float gradient = head_gradient[index] * inverse;
                    head_velocity[index] = options.momentum * head_velocity[index] + gradient;
                    float update = nesterov ? gradient + options.momentum * head_velocity[index]
                                            : head_velocity[index];
                    head[index] -= options.learning_rate * update;
                }
            }
            for (unsigned index = 0; index < 64U; ++index) {
                head_bias_velocity[index] = options.momentum * head_bias_velocity[index] +
                                            head_bias_gradient[index] * inverse;
                head_bias[index] -= options.learning_rate *
                    (nesterov ? head_bias_gradient[index] * inverse +
                     options.momentum * head_bias_velocity[index] : head_bias_velocity[index]);
                final_velocity[index] = options.momentum * final_velocity[index] +
                                        final_gradient[index] * inverse;
                final[index] -= options.learning_rate *
                    (nesterov ? final_gradient[index] * inverse +
                     options.momentum * final_velocity[index] : final_velocity[index]);
            }
            for (unsigned index = 0; index < 2U; ++index) {
                final_bias_velocity[index] = options.momentum * final_bias_velocity[index] +
                                             final_bias_gradient[index] * inverse;
                final_bias[index] -= options.learning_rate *
                    (nesterov ? final_bias_gradient[index] * inverse +
                     options.momentum * final_bias_velocity[index] : final_bias_velocity[index]);
            }
            double global_loss;
            MPI_Allreduce(&local_loss, &global_loss, 1, MPI_DOUBLE, MPI_SUM, MPI_COMM_WORLD);
            epoch_loss += global_loss;
            epoch_samples += actual_global;
        }
        double elapsed = MPI_Wtime() - epoch_start, max_elapsed, max_comm;
        MPI_Reduce(&elapsed, &max_elapsed, 1, MPI_DOUBLE, MPI_MAX, 0, MPI_COMM_WORLD);
        MPI_Reduce(&communication, &max_comm, 1, MPI_DOUBLE, MPI_MAX, 0, MPI_COMM_WORLD);
        if (rank == 0)
            fprintf(stderr, "nnue-mpi epoch=%u samples=%llu mse=%.8f seconds=%.3f samples/s=%.0f communication=%.3f\n",
                    epoch + 1U, (unsigned long long)epoch_samples,
                    epoch_samples == 0 ? 0.0 : epoch_loss / epoch_samples,
                    max_elapsed, epoch_samples / max_elapsed, max_comm);
    }

    /* Materialize momentum updates deferred after a sparse row's last use. */
#pragma omp parallel for schedule(static)
    for (unsigned bucket = 0; bucket < KING_BUCKETS; ++bucket) {
        if (owners[bucket] != rank) continue;
        uint32_t first = bucket * BOARD_CLASSES;
        uint32_t last = first + BOARD_CLASSES;
        for (uint32_t id = first; id < last; ++id)
            flush_momentum(weights + (size_t)id * HIDDEN,
                           velocity + (size_t)id * HIDDEN, &last_step[id],
                           step_number, options.learning_rate, options.momentum,
                           HIDDEN, options.optimizer == OPT_NESTEROV);
    }
    float *gathered = rank == 0 ? malloc(feature_values * sizeof(*gathered)) : NULL;
    if (rank == 0 && gathered == NULL) abort_mpi(rank, "cannot gather model");
    MPI_Reduce(weights, gathered, (int)board_values, MPI_FLOAT, MPI_SUM, 0, MPI_COMM_WORLD);
    int saved = 1;
    if (rank == 0) {
        memcpy(gathered + board_values,
               weights + board_values,
               (feature_values - board_values) * sizeof(*weights));
        saved = save_model(options.output_path, gathered, head, head_bias, final,
                           final_bias, options.activation_clip) ? 1 : 0;
    }
    MPI_Bcast(&saved, 1, MPI_INT, 0, MPI_COMM_WORLD);
    if (!saved) abort_mpi(rank, "cannot save NNUE3 checkpoint");
    if (rank == 0) fprintf(stderr, "saved %s\n", options.output_path);

    free(gathered); free(sync); free(group_starts); free(occurrence_scratch);
    free(occurrences); free(active); free(ids); free(dhead);
    free(head_act); free(head_raw); free(dhidden); free(hidden); free(batch);
    free(muon_workspace); free(final_bias_gradient); free(final_bias_velocity); free(final_bias);
    free(final_gradient); free(final_velocity); free(final);
    free(head_bias_gradient); free(head_bias_velocity); free(head_bias);
    free(head_gradient); free(head_velocity); free(head);
    free(last_step); free(feature_gradient); free(velocity); free(weights);
    for (unsigned bucket = 0; bucket < KING_BUCKETS; ++bucket) free(buckets[bucket].records);
    MPI_Finalize();
    return 0;
}
