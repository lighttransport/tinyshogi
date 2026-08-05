#include "eval.h"

/* Small ABI smoke-test plugin. Replace evaluate() with an NNUE lookup. */
static int evaluate(void *userdata, const ShogiPosition *position,
                   ShogiColor perspective) {
    (void)userdata;
    int score = 0;
    for (size_t square = 0; square < SHOGI_SQUARES; ++square) {
        uint8_t piece = position->board[square];
        ShogiPieceType type = (ShogiPieceType)(piece & 0x0fU);
        if (piece == SHOGI_EMPTY || type == SHOGI_KING) continue;
        int value = (int)type * 100;
        ShogiColor color = (piece & 0x10U) != 0 ? SHOGI_WHITE : SHOGI_BLACK;
        score += color == perspective ? value : -value;
    }
    return score;
}

static const TinyShogiEvalPlugin plugin = {
    TINYSHOGI_EVAL_ABI_VERSION,
    sizeof(TinyShogiEvalPlugin),
    "example-material-plugin",
    NULL,
    NULL,
    evaluate
};

const TinyShogiEvalPlugin *tinyshogi_eval_plugin(void) {
    return &plugin;
}
