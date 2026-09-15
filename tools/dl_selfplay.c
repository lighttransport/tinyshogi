/* SPDX-License-Identifier: Apache-2.0 */
#define _POSIX_C_SOURCE 200809L
#include "dl_eval.h"
#include "dl_features.h"
#include "gn_replay.h"
#include "search.h"
#include <errno.h>
#include <pthread.h>
#include <signal.h>
#include <stdatomic.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>
#include <unistd.h>
typedef struct {
    float features[SHOGI_DL_FEATURES];
    uint32_t ids[SHOGI_MAX_MOVES], visits[SHOGI_MAX_MOVES];
    size_t count;
    ShogiColor side;
    ShogiMove move;
} Sample;
typedef struct {
    ShogiDlModel *model;
    FILE *replay, *trace;
    gn_replay_schema schema;
    unsigned games, nodes, threads, max_plies, seed, generation;
    atomic_uint next_game;
    atomic_bool failed;
    pthread_mutex_t writer;
} Selfplay;
static volatile sig_atomic_t stopped;
static void stop(int signum) {
    (void)signum;
    stopped = 1;
}
static uint64_t rng_next_dl(uint64_t *s) {
    *s ^= *s << 13;
    *s ^= *s >> 7;
    *s ^= *s << 17;
    return *s;
}
static unsigned number(const char *s) {
    char *e;
    errno = 0;
    unsigned long n = strtoul(s, &e, 10);
    if (errno || *e || !n || n > 10000000) {
        fprintf(stderr, "invalid number %s\n", s);
        exit(2);
    }
    return (unsigned)n;
}
static bool canceled(Selfplay *s) { return stopped || atomic_load(&s->failed); }
static bool play(Selfplay *s, unsigned game, Sample *samples) {
    ShogiPosition position;
    shogi_position_start(&position);
    uint64_t game_id = ((uint64_t)s->seed << 32) | (game + 1);
    uint64_t rng = game_id;
    ShogiResult outcome = SHOGI_RESULT_ONGOING;
    size_t length = 0;
    while (length < s->max_plies && !canceled(s)) {
        outcome = shogi_game_result(&position);
        if (outcome != SHOGI_RESULT_ONGOING)
            break;
        SearchOptions options = search_default_options();
        options.mode = SEARCH_MODE_PUCT;
        options.policy_value = shogi_dl_evaluator(s->model);
        options.threads = s->threads;
        options.seed = rng_next_dl(&rng);
        options.seed_auto = false;
        options.root_noise = 0.25f;
        options.max_tree_nodes = (size_t)s->nodes * 2 + 1000;
        SearchLimits limits = {.nodes = s->nodes};
        SearchJob *job = search_start(&position, &limits, &options);
        if (!job)
            return false;
        while (!search_is_done(job)) {
            if (canceled(s))
                search_request_stop(job);
            struct timespec pause = {0, 1000000};
            nanosleep(&pause, NULL);
        }
        SearchResult result;
        search_join(job, &result);
        if (canceled(s)) {
            search_destroy(job);
            return true;
        }
        if (result.failed) {
            search_destroy(job);
            return false;
        }
        if (result.declaration_win) {
            outcome =
                position.side == SHOGI_BLACK ? SHOGI_RESULT_BLACK_WIN : SHOGI_RESULT_WHITE_WIN;
            search_destroy(job);
            break;
        }
        if (!result.has_move) {
            search_destroy(job);
            return false;
        }
        Sample *sample = &samples[length];
        sample->side = position.side;
        shogi_dl_encode(&position, sample->features);
        SearchPolicyEntry policy[SHOGI_MAX_MOVES];
        sample->count = search_get_root_policy(job, policy, SHOGI_MAX_MOVES);
        search_destroy(job);
        uint64_t total = 0;
        size_t best = 0;
        for (size_t i = 0; i < sample->count; i++) {
            int id = shogi_dl_action(&position, policy[i].move);
            if (id < 0 || policy[i].visits > UINT32_MAX)
                return false;
            sample->ids[i] = (uint32_t)id;
            sample->visits[i] = (uint32_t)policy[i].visits;
            total += policy[i].visits;
            if (policy[i].visits > policy[best].visits)
                best = i;
        }
        if (!total)
            return false;
        if (length < 30) {
            uint64_t choice = rng_next_dl(&rng) % total;
            for (size_t i = 0; i < sample->count; i++) {
                if (choice < policy[i].visits) {
                    best = i;
                    break;
                }
                choice -= policy[i].visits;
            }
        }
        sample->move = policy[best].move;
        if (!shogi_make_move(&position, sample->move))
            return false;
        length++;
    }
    if (canceled(s))
        return true;
    if (outcome == SHOGI_RESULT_ONGOING)
        outcome = shogi_game_result(&position);
    if (outcome == SHOGI_RESULT_ONGOING)
        outcome = SHOGI_RESULT_DRAW;
    pthread_mutex_lock(&s->writer);
    bool ok = true;
    fprintf(s->trace,
            "{\"game\":%llu,\"generation\":%u,\"initial\":\"startpos\",\"outcome\":%d,\"moves\":[",
            (unsigned long long)game_id, s->generation, outcome);
    for (size_t i = 0; i < length && ok; i++) {
        Sample *sample = &samples[i];
        uint32_t label = outcome == SHOGI_RESULT_DRAW ? 1
                         : outcome == (sample->side == SHOGI_BLACK ? SHOGI_RESULT_BLACK_WIN
                                                                   : SHOGI_RESULT_WHITE_WIN)
                             ? 0
                             : 2;
        gn_replay_record record = {game_id, s->generation, (uint32_t)i, (uint32_t)sample->count,
                                   label};
        ok = gnr_write(s->replay, &s->schema, &record, sample->features, sample->ids,
                       sample->visits);
        char move[16];
        ok = ok && shogi_move_to_usi(sample->move, move, sizeof(move));
        if (ok)
            fprintf(s->trace, "%s\"%s\"", i ? "," : "", move);
    }
    fputs("]}\n", s->trace);
    ok = ok && !fflush(s->trace) && !ferror(s->replay);
    fprintf(stderr, "{\"game\":%llu,\"plies\":%zu,\"outcome\":%d}\n", (unsigned long long)game_id,
            length, outcome);
    pthread_mutex_unlock(&s->writer);
    return ok;
}
static void *worker(void *opaque) {
    Selfplay *s = opaque;
    Sample *samples = calloc(s->max_plies, sizeof(*samples));
    if (!samples) {
        atomic_store(&s->failed, true);
        return NULL;
    }
    while (!canceled(s)) {
        unsigned game = atomic_fetch_add(&s->next_game, 1);
        if (game >= s->games)
            break;
        if (!play(s, game, samples)) {
            atomic_store(&s->failed, true);
            break;
        }
    }
    free(samples);
    return NULL;
}
int main(int argc, char **argv) {
    if (argc != 10 && argc != 11) {
        fprintf(stderr, "usage: dl-selfplay MODEL OUTPUT GAMES NODES THREADS MAX_PLIES SEED "
                        "BACKEND GENERATION [PARALLEL_GAMES]\n");
        return 2;
    }
    Selfplay s = {0};
    s.games = number(argv[3]);
    s.nodes = number(argv[4]);
    s.threads = number(argv[5]);
    s.max_plies = number(argv[6]);
    s.seed = number(argv[7]);
    s.generation = number(argv[9]);
    unsigned parallel = argc == 11 ? number(argv[10]) : 1;
    const char *path = argv[2];
    if (s.max_plies > 512 || s.threads > 64 || s.nodes <= s.threads || parallel > 32 ||
        s.threads * parallel > 64 || strlen(path) > 3500)
        return 2;
    if (access(path, F_OK) == 0) {
        fprintf(stderr, "refusing to overwrite replay: %s\n", path);
        return 2;
    }
    shogi_init();
    s.model = shogi_dl_open(argv[1], argv[8], 0, 32);
    if (!s.model) {
        fprintf(stderr, "DL load failed: %s\n", shogi_dl_error(NULL));
        return 1;
    }
    atomic_init(&s.next_game, 0);
    atomic_init(&s.failed, false);
    if (pthread_mutex_init(&s.writer, NULL)) {
        shogi_dl_close(s.model);
        return 1;
    }
    char temporary[4096], trace_path[4120];
    snprintf(temporary, sizeof(temporary), "%s.partial.%ld", path, (long)getpid());
    snprintf(trace_path, sizeof(trace_path), "%s.games.jsonl", temporary);
    s.replay = fopen(temporary, "wb");
    s.trace = fopen(trace_path, "w");
    int rc = 1;
    if (!s.replay || !s.trace)
        goto done;
    s.schema = (gn_replay_schema){9, 80, 139, {0}};
    for (int c = 56; c < 78; c++)
        s.schema.planes[c] = 1;
    s.schema.planes[78] = 2;
    s.schema.planes[79] = 3;
    if (!gnr_write_header(s.replay, &s.schema))
        goto done;
    signal(SIGINT, stop);
    signal(SIGTERM, stop);
    pthread_t workers[32];
    unsigned launched = 0;
    for (; launched < parallel; launched++)
        if (pthread_create(&workers[launched], NULL, worker, &s)) {
            atomic_store(&s.failed, true);
            break;
        }
    for (unsigned i = 0; i < launched; i++)
        pthread_join(workers[i], NULL);
    if (atomic_load(&s.failed)) {
        fprintf(stderr, "self-play discarded: search/inference/writer failed (%s)\n",
                shogi_dl_error(s.model));
        goto done;
    }
    if (fflush(s.replay) || fflush(s.trace) || ferror(s.replay) || ferror(s.trace) ||
        fsync(fileno(s.replay)) || fsync(fileno(s.trace)))
        goto done;
    rc = 0;
done:
    if (s.replay && fclose(s.replay))
        rc = 1;
    if (s.trace && fclose(s.trace))
        rc = 1;
    if (!rc) {
        char final_trace[4096];
        snprintf(final_trace, sizeof(final_trace), "%s.games.jsonl", path);
        if (rename(trace_path, final_trace) || rename(temporary, path))
            rc = 1;
    }
    pthread_mutex_destroy(&s.writer);
    shogi_dl_close(s.model);
    return rc;
}
