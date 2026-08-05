#ifndef TINYSHOGI_SHOGI_H
#define TINYSHOGI_SHOGI_H

#include <stdbool.h>
#include <stddef.h>
#include <stdint.h>

#define SHOGI_BOARD_SIZE 9
#define SHOGI_SQUARES 81
#define SHOGI_MAX_MOVES 600
#define SHOGI_MAX_HISTORY 4096
#define SHOGI_SQ_NONE 255

typedef enum {
    SHOGI_BLACK = 0,
    SHOGI_WHITE = 1
} ShogiColor;

typedef enum {
    SHOGI_EMPTY = 0,
    SHOGI_PAWN = 1,
    SHOGI_LANCE = 2,
    SHOGI_KNIGHT = 3,
    SHOGI_SILVER = 4,
    SHOGI_GOLD = 5,
    SHOGI_BISHOP = 6,
    SHOGI_ROOK = 7,
    SHOGI_KING = 8,
    SHOGI_PRO_PAWN = 9,
    SHOGI_PRO_LANCE = 10,
    SHOGI_PRO_KNIGHT = 11,
    SHOGI_PRO_SILVER = 12,
    SHOGI_HORSE = 13,
    SHOGI_DRAGON = 14
} ShogiPieceType;

typedef enum {
    SHOGI_RESULT_ONGOING = 0,
    SHOGI_RESULT_BLACK_WIN,
    SHOGI_RESULT_WHITE_WIN,
    SHOGI_RESULT_DRAW
} ShogiResult;

typedef struct {
    uint8_t from;
    uint8_t to;
    uint8_t piece;
    uint8_t promote;
    uint8_t drop;
} ShogiMove;

typedef struct {
    ShogiMove move;
    uint8_t moving_piece;
    uint8_t captured_piece;
    uint8_t color;
    uint8_t hand_index;
    uint8_t hand_before;
    uint8_t hand_touched;
    uint8_t valid;
    ShogiColor previous_side;
    unsigned previous_move_number;
    uint64_t previous_hash;
    size_t previous_history_length;
    uint8_t previous_king_square[2];
} ShogiUndo;

typedef struct {
    uint8_t board[SHOGI_SQUARES];
    uint8_t hand[2][7];
    ShogiColor side;
    unsigned move_number;
    uint64_t hash;
    uint8_t king_square[2];
    uint64_t history[SHOGI_MAX_HISTORY];
    uint8_t history_mover[SHOGI_MAX_HISTORY];
    uint8_t history_check[SHOGI_MAX_HISTORY];
    size_t history_length;
} ShogiPosition;

void shogi_init(void);
void shogi_position_start(ShogiPosition *position);
bool shogi_position_from_sfen(ShogiPosition *position, const char *sfen);
bool shogi_position_to_sfen(const ShogiPosition *position, char *out, size_t out_size);

bool shogi_make_move(ShogiPosition *position, ShogiMove move);
bool shogi_make_move_undo(ShogiPosition *position, ShogiMove move, ShogiUndo *undo);
bool shogi_unmake_move(ShogiPosition *position, const ShogiUndo *undo);
bool shogi_parse_usi_move(const char *text, ShogiMove *move);
bool shogi_move_to_usi(ShogiMove move, char *out, size_t out_size);
bool shogi_parse_and_make_move(ShogiPosition *position, const char *text);

size_t shogi_generate_legal(const ShogiPosition *position,
                            ShogiMove *moves,
                            size_t capacity);
size_t shogi_generate_pseudo(const ShogiPosition *position,
                              ShogiMove *moves,
                              size_t capacity);
ShogiResult shogi_game_result_with_moves(const ShogiPosition *position,
                                         ShogiMove *moves,
                                         size_t capacity,
                                         size_t *move_count);
bool shogi_is_in_check(const ShogiPosition *position, ShogiColor color);
ShogiResult shogi_game_result(const ShogiPosition *position);
bool shogi_is_declaration_win(const ShogiPosition *position, ShogiColor color);

uint8_t shogi_piece(ShogiColor color, ShogiPieceType type);
ShogiColor shogi_piece_color(uint8_t piece);
ShogiPieceType shogi_piece_type(uint8_t piece);
ShogiPieceType shogi_unpromoted_type(ShogiPieceType type);
bool shogi_is_promoted(ShogiPieceType type);
bool shogi_can_promote(ShogiPieceType type);

void shogi_print_position(const ShogiPosition *position);

#endif
