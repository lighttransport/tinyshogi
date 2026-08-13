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
    }
    if (plugin->destroy != NULL) plugin->destroy(state);
    return 0;
}
