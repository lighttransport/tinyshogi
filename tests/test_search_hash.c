/* Exercise collision and replacement semantics without depending on a game's
 * accidental Zobrist collisions. This executable owns its search translation unit. */
#ifdef NDEBUG
#undef NDEBUG
#endif
#include "../src/search.c"
#include <assert.h>

int main(void) {
    SearchJob *job = calloc(1, sizeof(*job));
    assert(job != NULL);
    AlphaBetaHashEntry entries[4] = {0};
    job->ab_hash = entries;
    job->ab_hash_capacity = 4;
    job->ab_generation = 1;
    job->options.ab_bucket_hash = true;
    job->options.ab_completed_results = true;
    ShogiMove move = {SHOGI_SQ_NONE, 0, SHOGI_PAWN, 0, 0};
    for (unsigned i = 0; i < 4; ++i)
        ab_store(job, 1 + 4 * i, 99, 10 + (int)i, (int)i + 1, AB_EXACT, move, 0);
    for (unsigned i = 0; i < 4; ++i)
        assert(ab_entry(job, 1 + 4 * i)->score == 10 + (int)i);
    /* A fifth colliding position displaces the weakest bound, not all four. */
    ab_store(job, 17, 99, 30, 8, AB_EXACT, move, 0);
    assert(ab_entry(job, 1) == NULL && ab_entry(job, 17)->score == 30);
    for (unsigned i = 1; i < 4; ++i) assert(ab_entry(job, 1 + 4 * i) != NULL);
    /* A qsearch or weaker same-depth bound cannot erase deeper exact work. */
    ab_store(job, 17, 99, 200, -2, AB_LOWER, move, 0);
    ab_store(job, 17, 99, 200, 8, AB_UPPER, move, 0);
    assert(ab_entry(job, 17)->score == 30 && job->ab_diagnostics.tt_retained == 2);
    job->ab_aborted = true;
    ab_store(job, 17, 99, 300, 9, AB_EXACT, move, 0);
    assert(ab_entry(job, 17)->score == 30);
    job->ab_aborted = false;
    /* Stale entries yield to the current search even when formerly deeper. */
    ++job->ab_generation;
    ab_store(job, 17, 99, AB_MATE - 7, 1, AB_EXACT, move, 5);
    assert(ab_score_from_hash(ab_entry(job, 17)->score, 3) == AB_MATE - 5);
    assert(job->ab_diagnostics.tt_replacements == 1);
    /* Selective qsearch depends on the previous destination. Different
     * histories may share a shallow bound only with the same qsearch context. */
    job->options.ab_shallow_transpositions = true;
    job->options.ab_quiescence_pruning = true;
    job->ab_history_unique[1] = true;
    job->ab_path_to[0] = 10;
    ab_store(job, 21, 123, 40, 0, AB_EXACT, move, 1);
    AlphaBetaHashEntry *context_entry = ab_entry(job, 21);
    assert(context_entry && context_entry->previous_to == 10);
    assert(ab_compatible_history(job, context_entry, 456, 1));
    job->ab_path_to[0] = 11;
    assert(!ab_compatible_history(job, context_entry, 456, 1));
    assert(ab_compatible_history(job, context_entry, 123, 1));
    context_entry->depth = 1;
    assert(ab_compatible_history(job, context_entry, 456, 1));
    free(job);
    return 0;
}
