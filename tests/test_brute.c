#include "../src/brute.h"

#include <stdio.h>

int main(void) {
    shogi_init();
    ShogiPosition position;
    shogi_position_start(&position);
    ShogiBruteResult result = shogi_brute_search(&position, 2, 1000);
    if (!result.has_move || result.nodes == 0) {
        fprintf(stderr, "brute search did not produce a move\n");
        return 1;
    }
    ShogiMove legal[SHOGI_MAX_MOVES];
    size_t count = shogi_generate_legal(&position, legal, SHOGI_MAX_MOVES);
    bool found = false;
    for (size_t index = 0; index < count; ++index)
        if (legal[index].from == result.move.from && legal[index].to == result.move.to &&
            legal[index].promote == result.move.promote && legal[index].drop == result.move.drop)
            found = true;
    return found ? 0 : 1;
}
