#define _POSIX_C_SOURCE 200809L

#include "../src/search.h"

#include <stdbool.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

static double seconds(void) {
    struct timespec now;
    clock_gettime(CLOCK_MONOTONIC, &now);
    return (double)now.tv_sec + (double)now.tv_nsec * 1.0e-9;
}

typedef struct {
    double elapsed;
    uint64_t nodes;
    char move[16];
} RunResult;

static RunResult run_search(bool perpetual_check, uint64_t nodes) {
    ShogiPosition position;
    shogi_position_start(&position);
    SearchOptions options;
    memset(&options, 0, sizeof(options));
    options.mode = SEARCH_MODE_MCTS;
    options.threads = 1;
    options.seed = 7;
    options.seed_auto = false;
    options.max_tree_nodes = 1000000;
    /* A short rollout makes the incremental make path a large share of the
     * cost, which is where the PerpetualCheck bookkeeping lives. */
    options.rollout_depth = 4;
    options.quiescence_depth = 0;
    options.exploration_milli = SEARCH_DEFAULT_EXPLORATION_MILLI;
    options.perpetual_check = perpetual_check;

    SearchLimits limits;
    memset(&limits, 0, sizeof(limits));
    limits.nodes = nodes;

    double begin = seconds();
    SearchJob *job = search_start(&position, &limits, &options);
    if (job == NULL) return (RunResult){0.0, 0, {0}};
    SearchResult result;
    search_join(job, &result);
    double elapsed = seconds() - begin;

    RunResult out;
    out.elapsed = elapsed;
    out.nodes = result.simulations;
    out.move[0] = '\0';
    if (result.has_move) shogi_move_to_usi(result.move, out.move, sizeof(out.move));
    search_destroy(job);
    return out;
}

int main(int argc, char **argv) {
    uint64_t nodes = argc > 1 ? strtoull(argv[1], NULL, 10) : 300000;
    if (nodes == 0) nodes = 300000;
    shogi_init();

    RunResult on = run_search(true, nodes);
    RunResult off = run_search(false, nodes);
    double nps_on = on.elapsed > 0.0 ? (double)on.nodes / on.elapsed : 0.0;
    double nps_off = off.elapsed > 0.0 ? (double)off.nodes / off.elapsed : 0.0;

    printf("perpetual-check bench nodes=%llu\n", (unsigned long long)nodes);
    printf("  on : seconds=%.6f nodes=%llu nps=%.0f bestmove=%s\n",
           on.elapsed, (unsigned long long)on.nodes, nps_on, on.move);
    printf("  off: seconds=%.6f nodes=%llu nps=%.0f bestmove=%s\n",
           off.elapsed, (unsigned long long)off.nodes, nps_off, off.move);
    if (strcmp(on.move, off.move) != 0)
        printf("  note: on/off bestmove differ (expected only near perpetual-check positions)\n");

    if (on.nodes == 0 || off.nodes == 0 || on.move[0] == '\0' || off.move[0] == '\0') {
        fprintf(stderr, "perpetual-check bench: empty search result\n");
        return 1;
    }
    return 0;
}
