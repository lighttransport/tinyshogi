#include "brute.h"

#include <limits.h>

typedef struct {
    uint64_t nodes;
    uint64_t limit;
} BruteContext;

static int piece_value(ShogiPieceType type) {
    switch (type) {
    case SHOGI_PAWN: return 100;
    case SHOGI_LANCE: return 300;
    case SHOGI_KNIGHT: return 320;
    case SHOGI_SILVER: return 450;
    case SHOGI_GOLD: return 550;
    case SHOGI_BISHOP: return 800;
    case SHOGI_ROOK: return 1000;
    case SHOGI_PRO_PAWN:
    case SHOGI_PRO_LANCE:
    case SHOGI_PRO_KNIGHT:
    case SHOGI_PRO_SILVER: return 550;
    case SHOGI_HORSE: return 950;
    case SHOGI_DRAGON: return 1200;
    default: return 0;
    }
}

static int evaluate(const ShogiPosition *position, ShogiColor perspective) {
    int score = 0;
    for (size_t square = 0; square < SHOGI_SQUARES; ++square) {
        uint8_t piece = position->board[square];
        if (piece == SHOGI_EMPTY || shogi_piece_type(piece) == SHOGI_KING) continue;
        int value = piece_value(shogi_piece_type(piece));
        score += shogi_piece_color(piece) == perspective ? value : -value;
    }
    for (unsigned hand = 0; hand < 7; ++hand) {
        int value = piece_value((ShogiPieceType)(hand + 1));
        score += (int)position->hand[perspective][hand] * value;
        score -= (int)position->hand[perspective ^ 1][hand] * value;
    }
    return score;
}

static int move_order(const ShogiPosition *position, ShogiMove move) {
    int score = move.promote ? 300 : 0;
    if (move.drop) score += piece_value((ShogiPieceType)move.drop) / 2;
    else if (move.to < SHOGI_SQUARES && position->board[move.to] != SHOGI_EMPTY)
        score += 1000 + piece_value(shogi_piece_type(position->board[move.to]));
    return score;
}

static int negamax(ShogiPosition *position, unsigned depth, int alpha, int beta,
                   BruteContext *context, unsigned ply) {
    if (context->limit != 0 && context->nodes >= context->limit) return evaluate(position, position->side);
    ++context->nodes;
    ShogiMove moves[SHOGI_MAX_MOVES];
    size_t count = shogi_generate_legal(position, moves, SHOGI_MAX_MOVES);
    ShogiResult result = shogi_game_result_with_moves(position, moves, SHOGI_MAX_MOVES, &count);
    if (result != SHOGI_RESULT_ONGOING) {
        if (result == SHOGI_RESULT_DRAW) return 0;
        bool side_won = (result == SHOGI_RESULT_BLACK_WIN && position->side == SHOGI_BLACK) ||
                        (result == SHOGI_RESULT_WHITE_WIN && position->side == SHOGI_WHITE);
        return side_won ? 100000 - (int)ply : -100000 + (int)ply;
    }
    if (depth == 0 || count == 0) return evaluate(position, position->side);
    for (size_t index = 1; index < count; ++index) {
        ShogiMove move = moves[index];
        size_t insert = index;
        int order = move_order(position, move);
        while (insert > 0 && move_order(position, moves[insert - 1]) < order) {
            moves[insert] = moves[insert - 1]; --insert;
        }
        moves[insert] = move;
    }
    int best = INT_MIN / 2;
    for (size_t index = 0; index < count; ++index) {
        ShogiPosition next = *position;
        if (!shogi_make_move(&next, moves[index])) continue;
        int score = -negamax(&next, depth - 1, -beta, -alpha, context, ply + 1);
        if (score > best) best = score;
        if (score > alpha) alpha = score;
        if (alpha >= beta) break;
        if (context->limit != 0 && context->nodes >= context->limit) break;
    }
    return best == INT_MIN / 2 ? evaluate(position, position->side) : best;
}

ShogiBruteResult shogi_brute_search(const ShogiPosition *position,
                                    unsigned depth, uint64_t node_limit) {
    ShogiBruteResult result = {0};
    if (position == NULL || depth == 0) depth = 1;
    ShogiMove moves[SHOGI_MAX_MOVES];
    size_t count = shogi_generate_legal(position, moves, SHOGI_MAX_MOVES);
    if (count == 0) return result;
    BruteContext context = {0, node_limit};
    int alpha = INT_MIN / 2;
    int best = INT_MIN / 2;
    for (size_t index = 0; index < count; ++index) {
        ShogiPosition next = *position;
        if (!shogi_make_move(&next, moves[index])) continue;
        int score = -negamax(&next, depth - 1, -INT_MAX / 2, -alpha, &context, 1);
        if (!result.has_move || score > best) {
            result.has_move = true; result.move = moves[index]; best = score;
        }
        if (score > alpha) alpha = score;
        if (node_limit != 0 && context.nodes >= node_limit) break;
    }
    result.score_cp = result.has_move ? best : 0;
    result.nodes = context.nodes;
    return result;
}
