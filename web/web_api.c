#include "../src/shogi.h"

#include <stddef.h>

/* A deliberately small, single-position API for the browser demo. */
static ShogiPosition position;

void web_reset(void) {
    shogi_position_start(&position);
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
    return web_get_move(index, &move) && shogi_make_move(&position, move) ? 1 : 0;
}

int web_game_result(void) {
    return (int)shogi_game_result(&position);
}

void web_init(void) {
    shogi_init();
    web_reset();
}
