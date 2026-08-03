#define _POSIX_C_SOURCE 200809L

#include "shogi.h"

#include <ctype.h>
#include <limits.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#define HISTORY_MOVER_NONE 2

static uint64_t zobrist_board[SHOGI_SQUARES][32];
static uint64_t zobrist_hand[2][7][19];
static uint64_t zobrist_side;
static bool zobrist_ready;

static uint64_t splitmix64(uint64_t *state) {
    uint64_t value = (*state += UINT64_C(0x9e3779b97f4a7c15));
    value = (value ^ (value >> 30)) * UINT64_C(0xbf58476d1ce4e5b9);
    value = (value ^ (value >> 27)) * UINT64_C(0x94d049bb133111eb);
    return value ^ (value >> 31);
}

void shogi_init(void) {
    if (zobrist_ready) {
        return;
    }

    uint64_t state = UINT64_C(0x7a6f676963686f6c);
    for (size_t square = 0; square < SHOGI_SQUARES; ++square) {
        for (size_t piece = 0; piece < 32; ++piece) {
            zobrist_board[square][piece] = splitmix64(&state);
        }
    }
    for (size_t color = 0; color < 2; ++color) {
        for (size_t type = 0; type < 7; ++type) {
            for (size_t count = 0; count < 19; ++count) {
                zobrist_hand[color][type][count] = splitmix64(&state);
            }
        }
    }
    zobrist_side = splitmix64(&state);
    zobrist_ready = true;
}

uint8_t shogi_piece(ShogiColor color, ShogiPieceType type) {
    return (uint8_t)type | (uint8_t)((unsigned)color << 4);
}

ShogiColor shogi_piece_color(uint8_t piece) {
    return (piece & 0x10U) != 0 ? SHOGI_WHITE : SHOGI_BLACK;
}

ShogiPieceType shogi_piece_type(uint8_t piece) {
    return (ShogiPieceType)(piece & 0x0fU);
}

bool shogi_is_promoted(ShogiPieceType type) {
    return type >= SHOGI_PRO_PAWN && type <= SHOGI_DRAGON;
}

ShogiPieceType shogi_unpromoted_type(ShogiPieceType type) {
    switch (type) {
    case SHOGI_PRO_PAWN: return SHOGI_PAWN;
    case SHOGI_PRO_LANCE: return SHOGI_LANCE;
    case SHOGI_PRO_KNIGHT: return SHOGI_KNIGHT;
    case SHOGI_PRO_SILVER: return SHOGI_SILVER;
    case SHOGI_HORSE: return SHOGI_BISHOP;
    case SHOGI_DRAGON: return SHOGI_ROOK;
    default: return type;
    }
}

bool shogi_can_promote(ShogiPieceType type) {
    return type >= SHOGI_PAWN && type <= SHOGI_ROOK;
}

static ShogiPieceType promoted_type(ShogiPieceType type) {
    switch (type) {
    case SHOGI_PAWN: return SHOGI_PRO_PAWN;
    case SHOGI_LANCE: return SHOGI_PRO_LANCE;
    case SHOGI_KNIGHT: return SHOGI_PRO_KNIGHT;
    case SHOGI_SILVER: return SHOGI_PRO_SILVER;
    case SHOGI_BISHOP: return SHOGI_HORSE;
    case SHOGI_ROOK: return SHOGI_DRAGON;
    default: return type;
    }
}

static int row_of(uint8_t square) {
    return (int)square / SHOGI_BOARD_SIZE;
}

static int col_of(uint8_t square) {
    return (int)square % SHOGI_BOARD_SIZE;
}

static bool on_board(int row, int col) {
    return row >= 0 && row < SHOGI_BOARD_SIZE && col >= 0 && col < SHOGI_BOARD_SIZE;
}

static uint8_t square_at(int row, int col) {
    return (uint8_t)(row * SHOGI_BOARD_SIZE + col);
}

static bool in_promotion_zone(ShogiColor color, int row) {
    return color == SHOGI_BLACK ? row <= 2 : row >= 6;
}

static bool forced_promotion(ShogiColor color, ShogiPieceType type, int to_row) {
    if (color == SHOGI_BLACK) {
        return ((type == SHOGI_PAWN || type == SHOGI_LANCE) && to_row == 0) ||
               (type == SHOGI_KNIGHT && to_row <= 1);
    }
    return ((type == SHOGI_PAWN || type == SHOGI_LANCE) && to_row == 8) ||
           (type == SHOGI_KNIGHT && to_row >= 7);
}

static bool valid_drop_rank(ShogiColor color, ShogiPieceType type, int row) {
    if (color == SHOGI_BLACK) {
        if ((type == SHOGI_PAWN || type == SHOGI_LANCE) && row == 0) return false;
        if (type == SHOGI_KNIGHT && row <= 1) return false;
    } else {
        if ((type == SHOGI_PAWN || type == SHOGI_LANCE) && row == 8) return false;
        if (type == SHOGI_KNIGHT && row >= 7) return false;
    }
    return true;
}

static int hand_index(ShogiPieceType type) {
    switch (type) {
    case SHOGI_PAWN: return 0;
    case SHOGI_LANCE: return 1;
    case SHOGI_KNIGHT: return 2;
    case SHOGI_SILVER: return 3;
    case SHOGI_GOLD: return 4;
    case SHOGI_BISHOP: return 5;
    case SHOGI_ROOK: return 6;
    default: return -1;
    }
}

static uint64_t position_hash(const ShogiPosition *position) {
    uint64_t hash = 0;
    for (size_t square = 0; square < SHOGI_SQUARES; ++square) {
        uint8_t piece = position->board[square];
        if (piece != SHOGI_EMPTY) {
            hash ^= zobrist_board[square][piece];
        }
    }
    for (size_t color = 0; color < 2; ++color) {
        for (size_t type = 0; type < 7; ++type) {
            unsigned count = position->hand[color][type];
            if (count > 18) count = 18;
            hash ^= zobrist_hand[color][type][count];
        }
    }
    if (position->side == SHOGI_WHITE) {
        hash ^= zobrist_side;
    }
    return hash;
}

static void reset_history(ShogiPosition *position) {
    position->hash = position_hash(position);
    position->history_length = 1;
    position->history[0] = position->hash;
    position->history_mover[0] = HISTORY_MOVER_NONE;
    position->history_check[0] = 0;
}

void shogi_position_start(ShogiPosition *position) {
    shogi_init();
    memset(position, 0, sizeof(*position));
    for (size_t square = 0; square < SHOGI_SQUARES; ++square) {
        position->board[square] = SHOGI_EMPTY;
    }

    static const char *const rows[9] = {
        "lnsgkgsnl",
        ".r.....b.",
        "ppppppppp",
        ".........",
        ".........",
        ".........",
        "PPPPPPPPP",
        ".B.....R.",
        "LNSGKGSNL"
    };
    for (int row = 0; row < 9; ++row) {
        for (int col = 0; col < 9; ++col) {
            char letter = rows[row][col];
            if (letter == '.') continue;
            ShogiColor color = isupper((unsigned char)letter) ? SHOGI_BLACK : SHOGI_WHITE;
            char lower = (char)tolower((unsigned char)letter);
            ShogiPieceType type = SHOGI_EMPTY;
            switch (lower) {
            case 'p': type = SHOGI_PAWN; break;
            case 'l': type = SHOGI_LANCE; break;
            case 'n': type = SHOGI_KNIGHT; break;
            case 's': type = SHOGI_SILVER; break;
            case 'g': type = SHOGI_GOLD; break;
            case 'b': type = SHOGI_BISHOP; break;
            case 'r': type = SHOGI_ROOK; break;
            case 'k': type = SHOGI_KING; break;
            default: break;
            }
            position->board[row * 9 + col] = shogi_piece(color, type);
        }
    }
    position->side = SHOGI_BLACK;
    position->move_number = 1;
    reset_history(position);
}

static bool parse_sfen_board(ShogiPosition *position, const char *text) {
    int row = 0;
    int col = 0;
    bool promoted = false;
    for (const char *cursor = text; *cursor != '\0'; ++cursor) {
        char letter = *cursor;
        if (letter == '/') {
            if (col != 9 || row >= 8 || promoted) return false;
            ++row;
            col = 0;
            continue;
        }
        if (letter == '+') {
            if (promoted || col >= 9) return false;
            promoted = true;
            continue;
        }
        if (isdigit((unsigned char)letter)) {
            int empty = letter - '0';
            if (empty < 1 || empty > 9 || promoted || col + empty > 9) return false;
            col += empty;
            continue;
        }
        ShogiColor color = isupper((unsigned char)letter) ? SHOGI_BLACK : SHOGI_WHITE;
        char lower = (char)tolower((unsigned char)letter);
        ShogiPieceType type;
        switch (lower) {
        case 'p': type = SHOGI_PAWN; break;
        case 'l': type = SHOGI_LANCE; break;
        case 'n': type = SHOGI_KNIGHT; break;
        case 's': type = SHOGI_SILVER; break;
        case 'g': type = SHOGI_GOLD; break;
        case 'b': type = SHOGI_BISHOP; break;
        case 'r': type = SHOGI_ROOK; break;
        case 'k': type = SHOGI_KING; break;
        default: return false;
        }
        if (row >= 9 || col >= 9) return false;
        if (promoted) {
            if (!shogi_can_promote(type)) return false;
            type = promoted_type(type);
        }
        position->board[row * 9 + col] = shogi_piece(color, type);
        ++col;
        promoted = false;
    }
    return row == 8 && col == 9 && !promoted;
}

static bool parse_sfen_hands(ShogiPosition *position, const char *text) {
    if (strcmp(text, "-") == 0) return true;
    size_t index = 0;
    while (text[index] != '\0') {
        unsigned count = 0;
        while (isdigit((unsigned char)text[index])) {
            count = count * 10U + (unsigned)(text[index] - '0');
            if (count > 18) return false;
            ++index;
        }
        char letter = text[index++];
        ShogiColor color = isupper((unsigned char)letter) ? SHOGI_BLACK : SHOGI_WHITE;
        char lower = (char)tolower((unsigned char)letter);
        ShogiPieceType type;
        switch (lower) {
        case 'p': type = SHOGI_PAWN; break;
        case 'l': type = SHOGI_LANCE; break;
        case 'n': type = SHOGI_KNIGHT; break;
        case 's': type = SHOGI_SILVER; break;
        case 'g': type = SHOGI_GOLD; break;
        case 'b': type = SHOGI_BISHOP; break;
        case 'r': type = SHOGI_ROOK; break;
        default: return false;
        }
        int hand = hand_index(type);
        if (hand < 0 || count == 0) count = 1;
        if (position->hand[color][hand] + count > 18) return false;
        position->hand[color][hand] = (uint8_t)(position->hand[color][hand] + count);
    }
    return true;
}

bool shogi_position_from_sfen(ShogiPosition *position, const char *sfen) {
    shogi_init();
    if (position == NULL || sfen == NULL) return false;
    char buffer[512];
    size_t length = strlen(sfen);
    if (length >= sizeof(buffer)) return false;
    memcpy(buffer, sfen, length + 1);

    char *fields[4] = {0};
    char *save = NULL;
    char *token = strtok_r(buffer, " \t\r\n", &save);
    for (size_t index = 0; index < 4 && token != NULL; ++index) {
        fields[index] = token;
        token = strtok_r(NULL, " \t\r\n", &save);
    }
    if (fields[0] == NULL || fields[1] == NULL || fields[2] == NULL || fields[3] == NULL ||
        token != NULL || (strcmp(fields[1], "b") != 0 && strcmp(fields[1], "w") != 0)) {
        return false;
    }

    ShogiPosition parsed;
    memset(&parsed, 0, sizeof(parsed));
    if (!parse_sfen_board(&parsed, fields[0]) || !parse_sfen_hands(&parsed, fields[2])) return false;
    for (int color = 0; color < 2; ++color) {
        unsigned kings = 0;
        for (size_t square = 0; square < SHOGI_SQUARES; ++square) {
            if (parsed.board[square] == shogi_piece((ShogiColor)color, SHOGI_KING)) ++kings;
        }
        if (kings != 1) return false;
    }
    char *end = NULL;
    unsigned long move_number = strtoul(fields[3], &end, 10);
    if (*fields[3] == '\0' || *end != '\0' || move_number == 0 || move_number > UINT_MAX) return false;
    parsed.side = strcmp(fields[1], "b") == 0 ? SHOGI_BLACK : SHOGI_WHITE;
    parsed.move_number = (unsigned)move_number;
    reset_history(&parsed);
    *position = parsed;
    return true;
}

static char piece_letter(ShogiPieceType type) {
    switch (shogi_unpromoted_type(type)) {
    case SHOGI_PAWN: return 'p';
    case SHOGI_LANCE: return 'l';
    case SHOGI_KNIGHT: return 'n';
    case SHOGI_SILVER: return 's';
    case SHOGI_GOLD: return 'g';
    case SHOGI_BISHOP: return 'b';
    case SHOGI_ROOK: return 'r';
    case SHOGI_KING: return 'k';
    default: return '?';
    }
}

bool shogi_position_to_sfen(const ShogiPosition *position, char *out, size_t out_size) {
    if (position == NULL || out == NULL || out_size == 0) return false;
    size_t used = 0;
    for (int row = 0; row < 9; ++row) {
        int empty = 0;
        for (int col = 0; col < 9; ++col) {
            uint8_t piece = position->board[row * 9 + col];
            if (piece == SHOGI_EMPTY) {
                ++empty;
                continue;
            }
            if (empty > 0) {
                if (used + 1 >= out_size) return false;
                out[used++] = (char)('0' + empty);
                empty = 0;
            }
            ShogiPieceType type = shogi_piece_type(piece);
            if (shogi_is_promoted(type)) {
                if (used + 1 >= out_size) return false;
                out[used++] = '+';
            }
            char letter = piece_letter(type);
            if (shogi_piece_color(piece) == SHOGI_BLACK) letter = (char)toupper((unsigned char)letter);
            if (used + 1 >= out_size) return false;
            out[used++] = letter;
        }
        if (empty > 0) {
            if (used + 1 >= out_size) return false;
            out[used++] = (char)('0' + empty);
        }
        if (row != 8) {
            if (used + 1 >= out_size) return false;
            out[used++] = '/';
        }
    }
    if (used + 2 >= out_size) return false;
    out[used++] = ' ';
    out[used++] = position->side == SHOGI_BLACK ? 'b' : 'w';
    out[used++] = ' ';
    bool any_hand = false;
    static const ShogiPieceType hand_types[7] = {
        SHOGI_ROOK, SHOGI_BISHOP, SHOGI_GOLD, SHOGI_SILVER,
        SHOGI_KNIGHT, SHOGI_LANCE, SHOGI_PAWN
    };
    for (size_t color = 0; color < 2; ++color) {
        for (size_t i = 0; i < 7; ++i) {
            int index = hand_index(hand_types[i]);
            unsigned count = position->hand[color][index];
            if (count == 0) continue;
            any_hand = true;
            if (count > 1) {
                int written = snprintf(out + used, out_size - used, "%u", count);
                if (written < 0 || (size_t)written >= out_size - used) return false;
                used += (size_t)written;
            }
            char letter = piece_letter(hand_types[i]);
            if (color == SHOGI_BLACK) letter = (char)toupper((unsigned char)letter);
            if (used + 1 >= out_size) return false;
            out[used++] = letter;
        }
    }
    if (!any_hand) {
        if (used + 1 >= out_size) return false;
        out[used++] = '-';
    }
    int written = snprintf(out + used, out_size - used, " %u", position->move_number);
    if (written < 0 || (size_t)written >= out_size - used) return false;
    return true;
}

static bool square_attacked(const ShogiPosition *position, uint8_t target, ShogiColor attacker) {
    int target_row = row_of(target);
    int target_col = col_of(target);
    for (uint8_t square = 0; square < SHOGI_SQUARES; ++square) {
        uint8_t piece = position->board[square];
        if (piece == SHOGI_EMPTY || shogi_piece_color(piece) != attacker) continue;
        ShogiPieceType type = shogi_piece_type(piece);
        int row = row_of(square);
        int col = col_of(square);
        int forward = attacker == SHOGI_BLACK ? -1 : 1;
        int dr = target_row - row;
        int dc = target_col - col;

        if (type == SHOGI_PAWN && dr == forward && dc == 0) return true;
        if (type == SHOGI_KNIGHT && dr == 2 * forward && (dc == -1 || dc == 1)) return true;
        if (type == SHOGI_SILVER &&
            ((dr == forward && (dc >= -1 && dc <= 1)) || (dr == -forward && (dc == -1 || dc == 1)))) return true;
        if ((type == SHOGI_GOLD || type == SHOGI_PRO_PAWN || type == SHOGI_PRO_LANCE ||
             type == SHOGI_PRO_KNIGHT || type == SHOGI_PRO_SILVER) &&
            ((dr == forward && (dc >= -1 && dc <= 1)) || (dr == 0 && (dc == -1 || dc == 1)) ||
             (dr == -forward && dc == 0))) return true;
        if (type == SHOGI_KING && dr >= -1 && dr <= 1 && dc >= -1 && dc <= 1 && (dr != 0 || dc != 0)) return true;

        bool bishop_like = type == SHOGI_BISHOP || type == SHOGI_HORSE;
        bool rook_like = type == SHOGI_ROOK || type == SHOGI_DRAGON;
        if (bishop_like && abs(dr) == abs(dc) && dr != 0) {
            int step_row = dr > 0 ? 1 : -1;
            int step_col = dc > 0 ? 1 : -1;
            bool clear = true;
            for (int r = row + step_row, c = col + step_col; r != target_row; r += step_row, c += step_col) {
                if (position->board[r * 9 + c] != SHOGI_EMPTY) clear = false;
            }
            if (clear) return true;
        }
        if (rook_like && ((dr == 0) != (dc == 0)) && (dr == 0 || dc == 0)) {
            int step_row = dr == 0 ? 0 : (dr > 0 ? 1 : -1);
            int step_col = dc == 0 ? 0 : (dc > 0 ? 1 : -1);
            bool clear = true;
            for (int r = row + step_row, c = col + step_col; r != target_row || c != target_col;
                 r += step_row, c += step_col) {
                if (position->board[r * 9 + c] != SHOGI_EMPTY) clear = false;
            }
            if (clear) return true;
        }
        if (type == SHOGI_HORSE && abs(dr) + abs(dc) == 1) return true;
        if (type == SHOGI_DRAGON && abs(dr) == 1 && abs(dc) == 1) return true;
    }
    return false;
}

static bool find_king(const ShogiPosition *position, ShogiColor color, uint8_t *square) {
    uint8_t king = shogi_piece(color, SHOGI_KING);
    for (uint8_t index = 0; index < SHOGI_SQUARES; ++index) {
        if (position->board[index] == king) {
            *square = index;
            return true;
        }
    }
    return false;
}

bool shogi_is_in_check(const ShogiPosition *position, ShogiColor color) {
    uint8_t king;
    return find_king(position, color, &king) && square_attacked(position, king, (ShogiColor)(color ^ 1));
}

static void add_move(ShogiMove *moves, size_t *count, size_t capacity, ShogiMove move) {
    if (*count < capacity) moves[(*count)++] = move;
}

static void add_normal_move(const ShogiPosition *position, uint8_t from, uint8_t to,
                            ShogiMove *moves, size_t *count, size_t capacity) {
    uint8_t piece = position->board[from];
    ShogiColor color = shogi_piece_color(piece);
    ShogiPieceType type = shogi_piece_type(piece);
    int from_row = row_of(from);
    int to_row = row_of(to);
    bool promotion_possible = shogi_can_promote(type) &&
        (in_promotion_zone(color, from_row) || in_promotion_zone(color, to_row));
    bool mandatory = forced_promotion(color, type, to_row);
    if (mandatory) {
        add_move(moves, count, capacity, (ShogiMove){from, to, piece, 1, 0});
    } else {
        add_move(moves, count, capacity, (ShogiMove){from, to, piece, 0, 0});
        if (promotion_possible) add_move(moves, count, capacity, (ShogiMove){from, to, piece, 1, 0});
    }
}

static void add_step(const ShogiPosition *position, int row, int col, int dr, int dc,
                     ShogiMove *moves, size_t *count, size_t capacity) {
    if (!on_board(row + dr, col + dc)) return;
    uint8_t from = square_at(row, col);
    uint8_t to = square_at(row + dr, col + dc);
    uint8_t target = position->board[to];
    if (target != SHOGI_EMPTY && shogi_piece_color(target) == shogi_piece_color(position->board[from])) return;
    if (target != SHOGI_EMPTY && shogi_piece_type(target) == SHOGI_KING) return;
    add_normal_move(position, from, to, moves, count, capacity);
}

static void add_slide(const ShogiPosition *position, int row, int col, int dr, int dc,
                      ShogiMove *moves, size_t *count, size_t capacity) {
    uint8_t from = square_at(row, col);
    ShogiColor color = shogi_piece_color(position->board[from]);
    for (int r = row + dr, c = col + dc; on_board(r, c); r += dr, c += dc) {
        uint8_t to = square_at(r, c);
        uint8_t target = position->board[to];
        if (target != SHOGI_EMPTY) {
            if (shogi_piece_color(target) != color && shogi_piece_type(target) != SHOGI_KING) {
                add_normal_move(position, from, to, moves, count, capacity);
            }
            break;
        }
        add_normal_move(position, from, to, moves, count, capacity);
    }
}

static bool has_unpromoted_pawn_on_file(const ShogiPosition *position, ShogiColor color, int col) {
    uint8_t pawn = shogi_piece(color, SHOGI_PAWN);
    for (int row = 0; row < 9; ++row) {
        if (position->board[row * 9 + col] == pawn) return true;
    }
    return false;
}

static void add_pseudo_drops(const ShogiPosition *position, ShogiMove *moves,
                             size_t *count, size_t capacity) {
    ShogiColor color = position->side;
    for (int row = 0; row < 9; ++row) {
        for (int col = 0; col < 9; ++col) {
            uint8_t to = square_at(row, col);
            if (position->board[to] != SHOGI_EMPTY) continue;
            for (int hand = 0; hand < 7; ++hand) {
                if (position->hand[color][hand] == 0) continue;
                ShogiPieceType type = (ShogiPieceType)(hand + 1);
                if (!valid_drop_rank(color, type, row)) continue;
                if (type == SHOGI_PAWN && has_unpromoted_pawn_on_file(position, color, col)) continue;
                add_move(moves, count, capacity, (ShogiMove){SHOGI_SQ_NONE, to, 0, 0, (uint8_t)type});
            }
        }
    }
}

static void generate_pseudo(const ShogiPosition *position, ShogiMove *moves,
                            size_t *count, size_t capacity) {
    ShogiColor color = position->side;
    int forward = color == SHOGI_BLACK ? -1 : 1;
    for (uint8_t from = 0; from < SHOGI_SQUARES; ++from) {
        uint8_t piece = position->board[from];
        if (piece == SHOGI_EMPTY || shogi_piece_color(piece) != color) continue;
        ShogiPieceType type = shogi_piece_type(piece);
        int row = row_of(from);
        int col = col_of(from);
        switch (type) {
        case SHOGI_PAWN:
            add_step(position, row, col, forward, 0, moves, count, capacity);
            break;
        case SHOGI_LANCE:
            add_slide(position, row, col, forward, 0, moves, count, capacity);
            break;
        case SHOGI_KNIGHT:
            add_step(position, row, col, 2 * forward, -1, moves, count, capacity);
            add_step(position, row, col, 2 * forward, 1, moves, count, capacity);
            break;
        case SHOGI_SILVER:
            add_step(position, row, col, forward, -1, moves, count, capacity);
            add_step(position, row, col, forward, 0, moves, count, capacity);
            add_step(position, row, col, forward, 1, moves, count, capacity);
            add_step(position, row, col, -forward, -1, moves, count, capacity);
            add_step(position, row, col, -forward, 1, moves, count, capacity);
            break;
        case SHOGI_GOLD:
        case SHOGI_PRO_PAWN:
        case SHOGI_PRO_LANCE:
        case SHOGI_PRO_KNIGHT:
        case SHOGI_PRO_SILVER:
            add_step(position, row, col, forward, -1, moves, count, capacity);
            add_step(position, row, col, forward, 0, moves, count, capacity);
            add_step(position, row, col, forward, 1, moves, count, capacity);
            add_step(position, row, col, 0, -1, moves, count, capacity);
            add_step(position, row, col, 0, 1, moves, count, capacity);
            add_step(position, row, col, -forward, 0, moves, count, capacity);
            break;
        case SHOGI_KING:
            for (int dr = -1; dr <= 1; ++dr) {
                for (int dc = -1; dc <= 1; ++dc) {
                    if (dr != 0 || dc != 0) add_step(position, row, col, dr, dc, moves, count, capacity);
                }
            }
            break;
        case SHOGI_BISHOP:
            add_slide(position, row, col, -1, -1, moves, count, capacity);
            add_slide(position, row, col, -1, 1, moves, count, capacity);
            add_slide(position, row, col, 1, -1, moves, count, capacity);
            add_slide(position, row, col, 1, 1, moves, count, capacity);
            break;
        case SHOGI_ROOK:
            add_slide(position, row, col, -1, 0, moves, count, capacity);
            add_slide(position, row, col, 1, 0, moves, count, capacity);
            add_slide(position, row, col, 0, -1, moves, count, capacity);
            add_slide(position, row, col, 0, 1, moves, count, capacity);
            break;
        case SHOGI_HORSE:
            add_slide(position, row, col, -1, -1, moves, count, capacity);
            add_slide(position, row, col, -1, 1, moves, count, capacity);
            add_slide(position, row, col, 1, -1, moves, count, capacity);
            add_slide(position, row, col, 1, 1, moves, count, capacity);
            add_step(position, row, col, -1, 0, moves, count, capacity);
            add_step(position, row, col, 1, 0, moves, count, capacity);
            add_step(position, row, col, 0, -1, moves, count, capacity);
            add_step(position, row, col, 0, 1, moves, count, capacity);
            break;
        case SHOGI_DRAGON:
            add_slide(position, row, col, -1, 0, moves, count, capacity);
            add_slide(position, row, col, 1, 0, moves, count, capacity);
            add_slide(position, row, col, 0, -1, moves, count, capacity);
            add_slide(position, row, col, 0, 1, moves, count, capacity);
            add_step(position, row, col, -1, -1, moves, count, capacity);
            add_step(position, row, col, -1, 1, moves, count, capacity);
            add_step(position, row, col, 1, -1, moves, count, capacity);
            add_step(position, row, col, 1, 1, moves, count, capacity);
            break;
        default:
            break;
        }
    }
    add_pseudo_drops(position, moves, count, capacity);
}

bool shogi_make_move(ShogiPosition *position, ShogiMove move) {
    if (position == NULL || move.to >= SHOGI_SQUARES) return false;
    ShogiColor color = position->side;
    bool is_drop = move.from == SHOGI_SQ_NONE;
    uint8_t moving_piece;
    if (is_drop) {
        if (move.promote != 0) return false;
        ShogiPieceType drop_type = (ShogiPieceType)move.drop;
        int hand = hand_index(drop_type);
        if (hand < 0 || position->hand[color][hand] == 0 || position->board[move.to] != SHOGI_EMPTY) return false;
        moving_piece = shogi_piece(color, drop_type);
        --position->hand[color][hand];
    } else {
        if (move.from >= SHOGI_SQUARES) return false;
        moving_piece = position->board[move.from];
        if (moving_piece == SHOGI_EMPTY || shogi_piece_color(moving_piece) != color) return false;
        if (move.piece != 0 && moving_piece != move.piece) return false;
        ShogiPieceType moving_type = shogi_piece_type(moving_piece);
        if (move.promote && (!shogi_can_promote(moving_type) ||
                             (!in_promotion_zone(color, row_of(move.from)) &&
                              !in_promotion_zone(color, row_of(move.to))))) return false;
        uint8_t captured = position->board[move.to];
        if (captured != SHOGI_EMPTY) {
            if (shogi_piece_color(captured) == color || shogi_piece_type(captured) == SHOGI_KING) return false;
            int hand = hand_index(shogi_unpromoted_type(shogi_piece_type(captured)));
            if (hand >= 0 && position->hand[color][hand] < 18) ++position->hand[color][hand];
        }
        position->board[move.from] = SHOGI_EMPTY;
    }
    if (move.promote) {
        ShogiPieceType type = shogi_piece_type(moving_piece);
        if (!shogi_can_promote(type)) return false;
        moving_piece = shogi_piece(color, promoted_type(type));
    }
    position->board[move.to] = moving_piece;
    position->side = (ShogiColor)(position->side ^ 1);
    ++position->move_number;
    position->hash = position_hash(position);
    if (position->history_length < SHOGI_MAX_HISTORY) {
        size_t index = position->history_length++;
        position->history[index] = position->hash;
        position->history_mover[index] = (uint8_t)color;
        position->history_check[index] = shogi_is_in_check(position, position->side) ? 1 : 0;
    }
    return true;
}

static bool same_move(ShogiMove a, ShogiMove b) {
    return a.from == b.from && a.to == b.to && a.promote == b.promote && a.drop == b.drop;
}

static size_t generate_legal_internal(const ShogiPosition *position, ShogiMove *moves,
                                      size_t capacity, bool enforce_uchifuzume) {
    ShogiMove pseudo[SHOGI_MAX_MOVES];
    size_t pseudo_count = 0;
    generate_pseudo(position, pseudo, &pseudo_count, SHOGI_MAX_MOVES);
    size_t count = 0;
    for (size_t index = 0; index < pseudo_count; ++index) {
        ShogiMove move = pseudo[index];
        ShogiPosition next = *position;
        if (!shogi_make_move(&next, move) || shogi_is_in_check(&next, position->side)) continue;
        if (enforce_uchifuzume && move.from == SHOGI_SQ_NONE && move.drop == SHOGI_PAWN &&
            shogi_is_in_check(&next, next.side)) {
            ShogiMove replies[SHOGI_MAX_MOVES];
            size_t reply_count = generate_legal_internal(&next, replies, SHOGI_MAX_MOVES, true);
            if (reply_count == 0) continue;
        }
        add_move(moves, &count, capacity, move);
    }
    return count;
}

size_t shogi_generate_legal(const ShogiPosition *position, ShogiMove *moves, size_t capacity) {
    if (position == NULL || moves == NULL) return 0;
    return generate_legal_internal(position, moves, capacity, true);
}

static bool repeated_position(const ShogiPosition *position, ShogiResult *result) {
    size_t count = 0;
    for (size_t index = 0; index < position->history_length; ++index) {
        if (position->history[index] == position->hash) ++count;
    }
    if (count < 4) return false;

    size_t occurrences[4] = {0};
    size_t found = 0;
    for (size_t index = position->history_length; index-- > 0 && found < 4;) {
        if (position->history[index] == position->hash) occurrences[found++] = index;
    }
    if (found < 4) return false;
    size_t start = occurrences[3];
    for (int candidate = 0; candidate < 2; ++candidate) {
        bool has_check = false;
        bool all_checks = true;
        for (size_t index = start + 1; index < position->history_length; ++index) {
            if (position->history_mover[index] == (uint8_t)candidate) {
                has_check = true;
                if (position->history_check[index] == 0) all_checks = false;
            }
        }
        if (has_check && all_checks) {
            *result = candidate == SHOGI_BLACK ? SHOGI_RESULT_WHITE_WIN : SHOGI_RESULT_BLACK_WIN;
            return true;
        }
    }
    *result = SHOGI_RESULT_DRAW;
    return false;
}

static int declaration_points(const ShogiPosition *position, ShogiColor color, int *camp_count) {
    int points = 0;
    int count = 0;
    for (int row = 0; row < 9; ++row) {
        bool in_camp = color == SHOGI_BLACK ? row <= 2 : row >= 6;
        if (!in_camp) continue;
        for (int col = 0; col < 9; ++col) {
            uint8_t piece = position->board[row * 9 + col];
            if (piece == SHOGI_EMPTY || shogi_piece_color(piece) != color) continue;
            ShogiPieceType type = shogi_piece_type(piece);
            if (type == SHOGI_KING) continue;
            ++count;
            points += (type == SHOGI_BISHOP || type == SHOGI_ROOK || type == SHOGI_HORSE || type == SHOGI_DRAGON) ? 5 : 1;
        }
    }
    for (int hand = 0; hand < 7; ++hand) {
        unsigned amount = position->hand[color][hand];
        points += (hand == 5 || hand == 6) ? (int)(amount * 5U) : (int)amount;
    }
    *camp_count = count;
    return points;
}

bool shogi_is_declaration_win(const ShogiPosition *position, ShogiColor color) {
    uint8_t king;
    if (!find_king(position, color, &king) || shogi_is_in_check(position, color)) return false;
    int row = row_of(king);
    bool in_camp = color == SHOGI_BLACK ? row <= 2 : row >= 6;
    if (!in_camp) return false;
    int camp_count = 0;
    int points = declaration_points(position, color, &camp_count);
    int required = color == SHOGI_BLACK ? 28 : 27;
    return camp_count >= 10 && points >= required;
}

ShogiResult shogi_game_result_with_moves(const ShogiPosition *position,
                                         ShogiMove *moves,
                                         size_t capacity,
                                         size_t *move_count) {
    if (move_count != NULL) *move_count = 0;
    if (position == NULL || moves == NULL || capacity == 0) return SHOGI_RESULT_ONGOING;
    ShogiResult repetition;
    if (repeated_position(position, &repetition)) return repetition;
    size_t repetition_count = 0;
    for (size_t index = 0; index < position->history_length; ++index) {
        if (position->history[index] == position->hash) ++repetition_count;
    }
    if (repetition_count >= 4) return SHOGI_RESULT_DRAW;
    if (shogi_is_declaration_win(position, position->side)) {
        return position->side == SHOGI_BLACK ? SHOGI_RESULT_BLACK_WIN : SHOGI_RESULT_WHITE_WIN;
    }
    size_t count = shogi_generate_legal(position, moves, capacity);
    if (move_count != NULL) *move_count = count;
    if (count == 0) {
        return position->side == SHOGI_BLACK ? SHOGI_RESULT_WHITE_WIN : SHOGI_RESULT_BLACK_WIN;
    }
    return SHOGI_RESULT_ONGOING;
}

ShogiResult shogi_game_result(const ShogiPosition *position) {
    ShogiMove moves[SHOGI_MAX_MOVES];
    return shogi_game_result_with_moves(position, moves, SHOGI_MAX_MOVES, NULL);
}

static bool square_from_text(const char *text, uint8_t *square) {
    if (text == NULL || text[0] < '1' || text[0] > '9' || text[1] < 'a' || text[1] > 'i' || text[2] != '\0') return false;
    int col = 9 - (text[0] - '0');
    int row = text[1] - 'a';
    *square = square_at(row, col);
    return true;
}

static bool square_from_chars(char file, char rank, uint8_t *square) {
    if (file < '1' || file > '9' || rank < 'a' || rank > 'i') return false;
    *square = square_at(rank - 'a', 9 - (file - '0'));
    return true;
}

bool shogi_parse_usi_move(const char *text, ShogiMove *move) {
    if (text == NULL || move == NULL) return false;
    size_t length = strlen(text);
    if (length == 4 && text[1] == '*') {
        ShogiPieceType type;
        switch (text[0]) {
        case 'P': type = SHOGI_PAWN; break;
        case 'L': type = SHOGI_LANCE; break;
        case 'N': type = SHOGI_KNIGHT; break;
        case 'S': type = SHOGI_SILVER; break;
        case 'G': type = SHOGI_GOLD; break;
        case 'B': type = SHOGI_BISHOP; break;
        case 'R': type = SHOGI_ROOK; break;
        default: return false;
        }
        if (!square_from_text(text + 2, &move->to)) return false;
        move->from = SHOGI_SQ_NONE;
        move->piece = 0;
        move->promote = 0;
        move->drop = (uint8_t)type;
        return true;
    }
    if (length == 4 || length == 5) {
        if (!square_from_chars(text[0], text[1], &move->from) || !square_from_chars(text[2], text[3], &move->to)) return false;
        move->piece = 0;
        move->drop = 0;
        move->promote = length == 5 && text[4] == '+';
        return length == 4 || move->promote;
    }
    return false;
}

bool shogi_move_to_usi(ShogiMove move, char *out, size_t out_size) {
    if (out == NULL || out_size < 6 || move.to >= SHOGI_SQUARES) return false;
    int to_col = col_of(move.to);
    int to_row = row_of(move.to);
    if (move.from == SHOGI_SQ_NONE) {
        char letter;
        switch ((ShogiPieceType)move.drop) {
        case SHOGI_PAWN: letter = 'P'; break;
        case SHOGI_LANCE: letter = 'L'; break;
        case SHOGI_KNIGHT: letter = 'N'; break;
        case SHOGI_SILVER: letter = 'S'; break;
        case SHOGI_GOLD: letter = 'G'; break;
        case SHOGI_BISHOP: letter = 'B'; break;
        case SHOGI_ROOK: letter = 'R'; break;
        default: return false;
        }
        return snprintf(out, out_size, "%c*%d%c", letter, 9 - to_col, 'a' + to_row) > 0;
    }
    if (move.from >= SHOGI_SQUARES) return false;
    int from_col = col_of(move.from);
    int from_row = row_of(move.from);
    int written = snprintf(out, out_size, "%d%c%d%c%s", 9 - from_col, 'a' + from_row,
                           9 - to_col, 'a' + to_row, move.promote ? "+" : "");
    return written > 0 && (size_t)written < out_size;
}

bool shogi_parse_and_make_move(ShogiPosition *position, const char *text) {
    ShogiMove requested;
    if (!shogi_parse_usi_move(text, &requested)) return false;
    ShogiMove legal[SHOGI_MAX_MOVES];
    size_t count = shogi_generate_legal(position, legal, SHOGI_MAX_MOVES);
    for (size_t index = 0; index < count; ++index) {
        if (same_move(requested, legal[index])) return shogi_make_move(position, legal[index]);
    }
    return false;
}

static char display_piece(uint8_t piece) {
    if (piece == SHOGI_EMPTY) return '.';
    char letter = piece_letter(shogi_piece_type(piece));
    if (shogi_is_promoted(shogi_piece_type(piece))) {
        return '*';
    }
    return shogi_piece_color(piece) == SHOGI_BLACK ? (char)toupper((unsigned char)letter) : letter;
}

void shogi_print_position(const ShogiPosition *position) {
    char sfen[512];
    for (int row = 0; row < 9; ++row) {
        for (int col = 0; col < 9; ++col) {
            printf("%c ", display_piece(position->board[row * 9 + col]));
        }
        putchar('\n');
    }
    printf("side: %s\n", position->side == SHOGI_BLACK ? "black" : "white");
    if (shogi_position_to_sfen(position, sfen, sizeof(sfen))) printf("sfen: %s\n", sfen);
}
