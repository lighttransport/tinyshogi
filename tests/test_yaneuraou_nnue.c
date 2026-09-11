#include "../src/eval.h"
#include "../src/shogi.h"

#include <stdio.h>
#include <stdlib.h>
#include <string.h>

const TinyShogiEvalPlugin *tinyshogi_eval_plugin(void);

int main(void) {
    shogi_init();
    const TinyShogiEvalPlugin *plugin = tinyshogi_eval_plugin();
    if (plugin == NULL || plugin->create == NULL || plugin->evaluate == NULL)
        return 1;
    if (plugin->create("0") != NULL || plugin->create("129") != NULL ||
        plugin->create("invalid") != NULL) return 1;
    void *state = plugin->create(NULL);
    if (state == NULL) {
        /* The model is an external fixture; preserve a useful build without
         * it while making configured CI fail through the explicit env check. */
        const char *path = getenv("YANEURAOU_NN_BIN");
        return path == NULL || path[0] == '\0' ? 0 : 1;
    }
    ShogiPosition position;
    shogi_position_start(&position);
    int black = plugin->evaluate(state, &position, SHOGI_BLACK);
    int white = plugin->evaluate(state, &position, SHOGI_WHITE);
    if (black != -white) {
        if (plugin->destroy != NULL) plugin->destroy(state);
        return 1;
    }
    printf("startpos black=%d white=%d\n", black, white);
    if (black == 125) {
        if (plugin->destroy != NULL) plugin->destroy(state);
        return 1;
    }

    if (plugin->struct_size >= sizeof(*plugin) && plugin->state_create != NULL) {
        static const char *moves[] = {
            "7g7f", "8c8d", "2g2f", "8d8e", "8h7g", "4a3b",
            "2f2e", "3c3d", "7i8h", "2b7g+", "8h7g", "3a2b",
            "2e2d", "2c2d", "2h2d", "B*3e", "2d2h", "3e5g+",
            "P*5b", "5a5b", "6i6h"
        };
        ShogiUndo undos[sizeof(moves) / sizeof(moves[0])];
        void *incremental = plugin->state_create(state, &position, SHOGI_BLACK);
        if (incremental == NULL) return 1;
        size_t count = sizeof(moves) / sizeof(moves[0]);
        for (size_t index = 0; index < count; ++index) {
            ShogiMove move;
            if (!shogi_parse_usi_move(moves[index], &move) ||
                !shogi_make_move_undo_fast(&position, move, &undos[index]) ||
                !plugin->state_make(incremental, &position, &undos[index]) ||
                plugin->state_score(incremental) !=
                    plugin->evaluate(state, &position, SHOGI_BLACK)) {
                plugin->state_destroy(incremental);
                return 1;
            }
        }
        for (size_t index = count; index-- > 0;) {
            if (!shogi_unmake_move(&position, &undos[index]) ||
                !plugin->state_unmake(incremental, &position, &undos[index]) ||
                plugin->state_score(incremental) !=
                    plugin->evaluate(state, &position, SHOGI_BLACK)) {
                plugin->state_destroy(incremental);
                return 1;
            }
        }
        plugin->state_destroy(incremental);

        /* Exercise both accumulator perspectives through 1,024 legal moves,
         * then unwind every path. The external oracle checks the same full
         * evaluator separately; equality here tests sparse updates/restoration. */
        uint64_t random = 7;
        unsigned checked = 0;
        for (unsigned game = 0; game < 16; ++game) {
            shogi_position_start(&position);
            void *states[2] = {plugin->state_create(state, &position, SHOGI_BLACK),
                               plugin->state_create(state, &position, SHOGI_WHITE)};
            if (states[0] == NULL || states[1] == NULL) return 1;
            ShogiUndo history[64];
            size_t length = 0;
            for (; length < 64; ++length) {
                ShogiMove legal[SHOGI_MAX_MOVES];
                size_t count = shogi_generate_legal_mut(&position, legal, SHOGI_MAX_MOVES);
                if (count == 0) break;
                random ^= random << 13;
                random ^= random >> 7;
                random ^= random << 17;
                if (!shogi_make_move_undo_fast(&position, legal[random % count], &history[length])) return 1;
                for (unsigned side = 0; side < 2; ++side) {
                    if (!plugin->state_make(states[side], &position, &history[length]) ||
                        plugin->state_score(states[side]) !=
                        plugin->evaluate(state, &position, (ShogiColor)side)) return 1;
                }
                ++checked;
            }
            while (length > 0) {
                --length;
                if (!shogi_unmake_move(&position, &history[length])) return 1;
                for (unsigned side = 0; side < 2; ++side) {
                    if (!plugin->state_unmake(states[side], &position, &history[length]) ||
                        plugin->state_score(states[side]) !=
                        plugin->evaluate(state, &position, (ShogiColor)side)) return 1;
                }
            }
            plugin->state_destroy(states[0]);
            plugin->state_destroy(states[1]);
        }
        printf("incremental NNUE verified %u moves, both perspectives and undo\n", checked);
        if (checked < 1000) return 1;
    }
    if (plugin->destroy != NULL) plugin->destroy(state);
    return 0;
}
