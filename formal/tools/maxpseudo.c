/* M1 probe: maximum pseudo-move count over reachable positions.
 * Line mode:  echo "<sfen>" | maxpseudo        -> "<count> <sfen>" or "REJECT <sfen>"
 * Walk mode:  maxpseudo walk <seed> <games> <plies> <greedy>
 *             -> one "GMAX <count> <sfen>" line per game (best position seen).
 * Greedy walks pick, each ply, the legal move whose child position has the
 * largest pseudo count (hill climbing toward drop-heavy / max-material
 * configurations). Included shogi.c so the static generator is callable. */
#include "../../src/shogi.c"
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

static uint64_t rng_state;
static uint64_t rng_next(void) {
    rng_state ^= rng_state << 13;
    rng_state ^= rng_state >> 7;
    rng_state ^= rng_state << 17;
    return rng_state;
}

static size_t pseudo_count(const ShogiPosition *p) {
    ShogiMove moves[SHOGI_MAX_MOVES];
    return shogi_generate_pseudo(p, moves, SHOGI_MAX_MOVES);
}

struct Best { size_t count; char sfen[512]; };

static void consider(struct Best *best, const ShogiPosition *p) {
    size_t n = pseudo_count(p);
    if (n > best->count) {
        best->count = n;
        if (!shogi_position_to_sfen(p, best->sfen, sizeof(best->sfen)))
            best->sfen[0] = '\0';
    }
}

static void walk(uint64_t seed, int plies, int greedy, struct Best *best) {
    static ShogiPosition stack[8];
    ShogiPosition *p = &stack[0];
    rng_state = seed ? seed : 0x9e3779b97f4a7c15ull;
    shogi_position_start(p);
    consider(best, p);
    for (int ply = 0; ply < plies; ++ply) {
        ShogiMove moves[SHOGI_MAX_MOVES];
        size_t count = shogi_generate_legal(p, moves, SHOGI_MAX_MOVES);
        if (count == 0) break;
        size_t pick;
        if (greedy) {
            size_t best_child = 0;
            size_t best_n = 0;
            for (size_t i = 0; i < count; ++i) {
                ShogiPosition *child = &stack[1];
                shogi_position_copy_active(child, p);
                if (!shogi_make_move(child, moves[i])) continue;
                size_t n = pseudo_count(child);
                if (n > best_n || (n == best_n && (rng_next() & 1))) {
                    best_n = n;
                    best_child = i;
                }
            }
            pick = best_child;
        } else {
            pick = (size_t)(rng_next() % count);
        }
        if (!shogi_make_move(p, moves[pick])) break;
        consider(best, p);
        /* Stop on terminal results (repetition/mate/declaration). */
        ShogiResult r = shogi_game_result(p);
        if (r != SHOGI_RESULT_ONGOING) break;
    }
}

int main(int argc, char **argv) {
    static char line[16384];
    static ShogiPosition position;
    shogi_init();
    if (argc >= 2 && strcmp(argv[1], "walk") == 0) {
        uint64_t seed = strtoull(argv[2], NULL, 10);
        int games = atoi(argv[3]);
        int plies = atoi(argv[4]);
        int greedy = argc >= 6 ? atoi(argv[5]) : 1;
        for (int g = 0; g < games; ++g) {
            struct Best best = {0, ""};
            walk(seed + (uint64_t)g * 0x2545f4914f6cdd1dull, plies, greedy, &best);
            printf("GMAX %zu %s\n", best.count, best.sfen);
            fflush(stdout);
        }
        return 0;
    }
    while (fgets(line, sizeof(line), stdin)) {
        size_t n = strcspn(line, "\r\n");
        line[n] = '\0';
        if (n == 0) continue;
        if (shogi_position_from_sfen(&position, line))
            printf("%zu %s\n", pseudo_count(&position), line);
        else
            printf("REJECT %s\n", line);
        fflush(stdout);
    }
    return 0;
}
