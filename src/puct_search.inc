/* SPDX-License-Identifier: Apache-2.0
 * Included in search.c: uses its job lifecycle, deadline and publication API.
 * Worker-local trees intentionally do not merge history-dependent positions.
 * The evaluator coalesces requests across independent workers/games. */
typedef struct PvNode PvNode;
typedef struct {
    ShogiMove move;
    PvNode *child;
    float prior;
    double value;
    uint64_t visits;
} PvEdge;
struct PvNode {
    PvEdge *edges;
    size_t count;
    uint64_t visits;
    float value;
    bool ready, terminal;
};
static double pv_uniform(uint64_t *rng) {
    return ((double)(rng_next(rng) >> 11) + 0.5) * (1.0 / 9007199254740992.0);
}
static double pv_gamma(double shape, uint64_t *rng) {
    if (shape < 1)
        return pv_gamma(shape + 1, rng) * pow(pv_uniform(rng), 1 / shape);
    double d = shape - 1.0 / 3, c = 1 / sqrt(9 * d);
    for (;;) {
        double x = sqrt(-2 * log(pv_uniform(rng))) * cos(6.283185307179586 * pv_uniform(rng));
        double v = 1 + c * x;
        if (v <= 0)
            continue;
        v = v * v * v;
        double u = pv_uniform(rng);
        if (u < 1 - 0.0331 * x * x * x * x || log(u) < 0.5 * x * x + d * (1 - v + log(v)))
            return d * v;
    }
}
static bool pv_expand(SearchJob *job, PvNode *node, ShogiPosition *position, bool root,
                      uint64_t *rng, size_t *bytes, size_t limit) {
    ShogiMove moves[SHOGI_MAX_MOVES];
    size_t count = 0;
    ShogiResult result = shogi_game_result_with_moves_mut(position, moves, SHOGI_MAX_MOVES, &count);
    if (result != SHOGI_RESULT_ONGOING) {
        node->ready = true;
        node->terminal = true;
        node->value = result == SHOGI_RESULT_DRAW ? 0
                      : result == (position->side == SHOGI_BLACK ? SHOGI_RESULT_BLACK_WIN
                                                                 : SHOGI_RESULT_WHITE_WIN)
                          ? 1
                          : -1;
        return true;
    }
    if (root) {
        count = job->root->move_count;
        for (size_t i = 0; i < count; i++)
            moves[i] = job->root->children[i].move;
    }
    if (!count)
        return false;
    if (count * sizeof(PvEdge) > limit - *bytes)
        return true; /* arena full: retain neutral leaf */
    float logits[SHOGI_MAX_MOVES], wdl[3];
    const ShogiPosition *positions[] = {position};
    const ShogiMove *legal[] = {moves};
    float *outputs[] = {logits};
    const ShogiPolicyValueEvaluator *e = job->options.policy_value;
    if (!e->evaluate_batch(e->userdata, positions, legal, &count, 1, outputs, wdl))
        return false;
    double total = 0;
    for (int i = 0; i < 3; i++) {
        if (!isfinite(wdl[i]) || wdl[i] < 0 || wdl[i] > 1)
            return false;
        total += wdl[i];
    }
    if (fabs(total - 1) > 1e-4)
        return false;
    float top = -INFINITY;
    for (size_t i = 0; i < count; i++) {
        if (!isfinite(logits[i]))
            return false;
        if (logits[i] > top)
            top = logits[i];
    }
    total = 0;
    for (size_t i = 0; i < count; i++) {
        logits[i] = expf(logits[i] - top);
        total += logits[i];
    }
    node->edges = calloc(count, sizeof(*node->edges));
    if (!node->edges)
        return false;
    *bytes += count * sizeof(PvEdge);
    node->count = count;
    node->ready = true;
    node->value = wdl[0] - wdl[2];
    double noise[SHOGI_MAX_MOVES], noise_sum = 0;
    float epsilon = job->options.root_noise;
    if (root && epsilon > 0) {
        for (size_t i = 0; i < count; i++) {
            noise[i] = pv_gamma(10.0 / count, rng);
            noise_sum += noise[i];
        }
    }
    for (size_t i = 0; i < count; i++) {
        node->edges[i].move = moves[i];
        node->edges[i].prior = (float)(logits[i] / total);
        if (root && epsilon > 0 && noise_sum > 0)
            node->edges[i].prior =
                (1 - epsilon) * node->edges[i].prior + (float)(epsilon * noise[i] / noise_sum);
    }
    return true;
}
static void run_puct(WorkerContext *worker) {
    SearchJob *job = worker->job;
    size_t capacity = job->options.max_tree_nodes / job->worker_count;
    if (capacity < 2)
        capacity = 2;
    /* Include edge storage in the worker budget (approximately 512 bytes per
     * requested node), and never create an unevaluated transposition alias. */
    size_t limit = capacity * 512, bytes = capacity * sizeof(PvNode), used = 1;
    PvNode *nodes = calloc(capacity, sizeof(*nodes));
    ShogiPosition *position = malloc(sizeof(*position));
    if (!nodes || !position) {
        free(nodes);
        free(position);
        atomic_store(&job->pv_failed, true);
        atomic_store(&job->stop, true);
        return;
    }
    uint64_t rng = job->options.seed + worker->id + 1;
    float cpuct = job->options.puct_constant > 0 ? job->options.puct_constant : 1.5f;
    while (!should_stop(job) && claim_simulation_batch(job, 1)) {
        shogi_position_copy_active(position, &job->root_position);
        PvNode *node = &nodes[0], *parents[SEARCH_MAX_PATH];
        PvEdge *path[SEARCH_MAX_PATH];
        size_t length = 0;
        while (node->ready && !node->terminal && node->count && length < SEARCH_MAX_PATH) {
            size_t best = 0;
            double best_score = -INFINITY, scale = cpuct * sqrt((double)node->visits + 1);
            for (size_t i = 0; i < node->count; i++) {
                PvEdge *edge = &node->edges[i];
                double q = edge->visits ? edge->value / edge->visits : node->value;
                double score = q + scale * edge->prior / (1 + (double)edge->visits);
                if (score > best_score) {
                    best_score = score;
                    best = i;
                }
            }
            PvEdge *edge = &node->edges[best];
            if (!edge->child) {
                if (used == capacity)
                    break;
                edge->child = &nodes[used++];
            }
            if (!shogi_make_move(position, edge->move)) {
                atomic_store(&job->pv_failed, true);
                break;
            }
            parents[length] = node;
            path[length++] = edge;
            node = edge->child;
        }
        if (atomic_load(&job->pv_failed))
            break;
        if (!node->ready && !pv_expand(job, node, position, length == 0, &rng, &bytes, limit)) {
            atomic_store(&job->pv_failed, true);
            break;
        }
        double value = node->value;
        node->visits++;
        for (size_t d = length; d-- > 0;) {
            value = -value;
            path[d]->visits++;
            path[d]->value += value;
            parents[d]->visits++;
        }
        if (length) {
            size_t root_index = (size_t)(path[0] - nodes[0].edges);
            TreeChild *published = &job->root->children[root_index];
            __atomic_fetch_add(&published->visits, 1, __ATOMIC_RELAXED);
            __atomic_fetch_add(&published->value, (uint64_t)((value + 1) * 0.5 * VALUE_SCALE),
                               __ATOMIC_RELAXED);
        }
    }
    if (atomic_load(&job->pv_failed))
        atomic_store(&job->stop, true);
    for (size_t i = 0; i < used; i++)
        free(nodes[i].edges);
    free(nodes);
    free(position);
}
