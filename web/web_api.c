#include "../src/shogi.h"
#include "../src/search.h"

#include <stddef.h>

/* A deliberately small, single-position API for the browser demo. */
static ShogiPosition position;
#define WEB_MAX_UNDO 512
static ShogiUndo undo_stack[WEB_MAX_UNDO];
static size_t undo_count;
static ShogiMove redo_stack[WEB_MAX_UNDO];
static size_t redo_count;

static void web_clear_history(void) {
    undo_count = 0;
    redo_count = 0;
}

void web_reset(void) {
    shogi_position_start(&position);
    web_clear_history();
}

/* Black pieces are positive, white pieces are negative, and empty is zero. */
int web_piece_at(int square) {
    if (square < 0 || square >= SHOGI_SQUARES) return 0;
    uint8_t piece = position.board[square];
    if (piece == SHOGI_EMPTY) return 0;
    int type = (int)shogi_piece_type(piece);
    return shogi_piece_color(piece) == SHOGI_BLACK ? type : -type;
}

int web_side_to_move(void) {
    return (int)position.side;
}

int web_hand_count(int color, int hand_index) {
    if (color < 0 || color > 1 || hand_index < 0 || hand_index >= 7) return 0;
    return (int)position.hand[color][hand_index];
}

int web_legal_move_count(void) {
    ShogiMove moves[SHOGI_MAX_MOVES];
    return (int)shogi_generate_legal(&position, moves, SHOGI_MAX_MOVES);
}

static bool web_get_move(int index, ShogiMove *move) {
    if (index < 0 || index >= SHOGI_MAX_MOVES) return false;
    ShogiMove moves[SHOGI_MAX_MOVES];
    size_t count = shogi_generate_legal(&position, moves, SHOGI_MAX_MOVES);
    if ((size_t)index >= count) return false;
    *move = moves[index];
    return true;
}

int web_move_from(int index) {
    ShogiMove move;
    return web_get_move(index, &move) ? (int)move.from : SHOGI_SQ_NONE;
}

int web_move_to(int index) {
    ShogiMove move;
    return web_get_move(index, &move) ? (int)move.to : SHOGI_SQ_NONE;
}

int web_move_promotes(int index) {
    ShogiMove move;
    return web_get_move(index, &move) ? (int)move.promote : 0;
}

int web_move_drop(int index) {
    ShogiMove move;
    return web_get_move(index, &move) ? (int)move.drop : 0;
}

int web_play_move(int index) {
    ShogiMove move;
    if (!web_get_move(index, &move) || undo_count >= WEB_MAX_UNDO ||
        !shogi_make_move_undo(&position, move, &undo_stack[undo_count])) return 0;
    ++undo_count;
    redo_count = 0;
    return 1;
}

int web_play_usi(const char *text) {
    ShogiMove wanted;
    if (text == NULL || !shogi_parse_usi_move(text, &wanted)) return 0;
    ShogiMove move;
    for (int index = 0; index < SHOGI_MAX_MOVES; ++index) {
        if (!web_get_move(index, &move)) break;
        if (move.from == wanted.from && move.to == wanted.to &&
            move.promote == wanted.promote && move.drop == wanted.drop) {
            return web_play_move(index);
        }
    }
    return 0;
}

int web_can_undo(void) { return undo_count != 0; }
int web_can_redo(void) { return redo_count != 0; }

int web_undo(void) {
    if (undo_count == 0) return 0;
    ShogiUndo *undo = &undo_stack[undo_count - 1];
    if (!shogi_unmake_move(&position, undo)) return 0;
    if (redo_count < WEB_MAX_UNDO) redo_stack[redo_count++] = undo->move;
    --undo_count;
    return 1;
}

int web_redo(void) {
    if (redo_count == 0 || undo_count >= WEB_MAX_UNDO) return 0;
    ShogiMove move = redo_stack[--redo_count];
    if (!shogi_make_move_undo(&position, move, &undo_stack[undo_count])) {
        ++redo_count;
        return 0;
    }
    ++undo_count;
    return 1;
}

const char *web_get_sfen(void) {
    static char sfen[512];
    return shogi_position_to_sfen(&position, sfen, sizeof(sfen)) ? sfen : "";
}

int web_set_sfen(const char *sfen) {
    ShogiPosition next;
    if (sfen == NULL || !shogi_position_from_sfen(&next, sfen)) return 0;
    position = next;
    web_clear_history();
    return 1;
}

const char *web_engine_move(unsigned nodes) {
    static char move_text[16];
    SearchLimits limits = {0};
    SearchOptions options = {1, 1, false, 50000, 64,
                             SEARCH_DEFAULT_QUIESCENCE_DEPTH,
                             SEARCH_DEFAULT_EXPLORATION_MILLI, 1, NULL};
    limits.nodes = nodes == 0 ? 64 : nodes;
    SearchJob *job = search_start(&position, &limits, &options);
    if (job == NULL) return "";
    SearchResult result;
    search_join(job, &result);
    bool ok = result.has_move && shogi_move_to_usi(result.move, move_text, sizeof(move_text));
    if (ok) ok = web_play_usi(move_text);
    search_destroy(job);
    return ok ? move_text : "";
}

int web_game_result(void) {
    return (int)shogi_game_result(&position);
}

void web_init(void) {
    shogi_init();
    web_reset();
}
