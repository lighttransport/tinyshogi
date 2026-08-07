#ifndef TINYSHOGI_BRUTE_H
#define TINYSHOGI_BRUTE_H

#include "shogi.h"

#include <stdbool.h>
#include <stdint.h>

typedef struct {
    bool has_move;
    ShogiMove move;
    int score_cp;
    uint64_t nodes;
} ShogiBruteResult;

ShogiBruteResult shogi_brute_search(const ShogiPosition *position,
                                    unsigned depth, uint64_t node_limit);

#endif
