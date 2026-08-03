#include "../src/shogi.h"

#include <stdio.h>
#include <string.h>

static int fail(const char *message) {
    fprintf(stderr, "rules test failed: %s\n", message);
    return 1;
}

static uint64_t perft(const ShogiPosition *position, int depth) {
    if (depth == 0) return 1;
    ShogiMove moves[SHOGI_MAX_MOVES];
    size_t count = shogi_generate_legal(position, moves, SHOGI_MAX_MOVES);
    uint64_t total = 0;
    for (size_t index = 0; index < count; ++index) {
        ShogiPosition next = *position;
        if (shogi_make_move(&next, moves[index])) total += perft(&next, depth - 1);
    }
    return total;
}

int main(void) {
    shogi_init();
    ShogiPosition position;
    shogi_position_start(&position);
    ShogiMove moves[SHOGI_MAX_MOVES];
    size_t count = shogi_generate_legal(&position, moves, SHOGI_MAX_MOVES);
    if (count != 30) return fail("initial position move count");
    if (perft(&position, 2) != 900) return fail("initial perft depth 2");
    if (perft(&position, 3) != 25470) return fail("initial perft depth 3");
    if (!shogi_parse_and_make_move(&position, "7g7f")) return fail("initial pawn move");

    char sfen[512];
    if (!shogi_position_to_sfen(&position, sfen, sizeof(sfen))) return fail("SFEN serialization");
    if (strcmp(sfen, "lnsgkgsnl/1r5b1/ppppppppp/9/9/2P6/PP1PPPPPP/1B5R1/LNSGKGSNL w - 2") != 0) {
        return fail("SFEN after pawn move");
    }

    ShogiPosition parsed;
    if (!shogi_position_from_sfen(&parsed, sfen)) return fail("SFEN parsing");
    char roundtrip[512];
    if (!shogi_position_to_sfen(&parsed, roundtrip, sizeof(roundtrip)) || strcmp(sfen, roundtrip) != 0) {
        return fail("SFEN roundtrip");
    }

    ShogiMove drop;
    if (!shogi_parse_usi_move("P*7f", &drop) || drop.from != SHOGI_SQ_NONE) return fail("drop notation");
    if (shogi_parse_and_make_move(&position, "7g7f+")) return fail("invalid pawn promotion acceptance");
    if (shogi_game_result(&position) != SHOGI_RESULT_ONGOING) return fail("premature terminal result");

    if (!shogi_position_from_sfen(&parsed, "4k4/9/4P4/9/9/9/9/9/4K4 b - 1")) return fail("promotion SFEN");
    if (!shogi_parse_and_make_move(&parsed, "5c5b+")) return fail("promotion move");
    if (shogi_piece_type(parsed.board[1 * 9 + 4]) != SHOGI_PRO_PAWN) return fail("promotion piece");

    if (!shogi_position_from_sfen(&parsed, "4k4/9/9/9/9/9/9/9/4K4 b P 1")) return fail("drop SFEN");
    if (!shogi_parse_and_make_move(&parsed, "P*5e")) return fail("pawn drop");

    if (!shogi_position_from_sfen(&parsed, "4k4/9/9/9/4P4/9/9/9/4K4 b P 1")) return fail("nifu SFEN");
    if (shogi_parse_and_make_move(&parsed, "P*5d")) return fail("nifu rejection");
    if (!shogi_position_from_sfen(&parsed, "4k4/9/9/9/9/9/9/9/4K4 b N 1")) return fail("dead drop SFEN");
    if (shogi_parse_and_make_move(&parsed, "N*5a")) return fail("dead-rank drop rejection");

    if (!shogi_position_from_sfen(&parsed, "4r3k/9/9/9/9/9/9/4R4/4K4 b - 1")) return fail("pin SFEN");
    if (shogi_parse_and_make_move(&parsed, "5h4h")) return fail("self-check rejection");

    if (!shogi_position_from_sfen(&parsed, "4k4/9/2NG1GN2/9/9/9/9/9/4K4 b P 1")) return fail("uchifuzume SFEN");
    if (shogi_parse_and_make_move(&parsed, "P*5b")) return fail("uchifuzume rejection");

    if (!shogi_position_from_sfen(&parsed, "4k4/9/9/9/9/9/9/9/4K4 b - 1")) return fail("repetition SFEN");
    const char *cycle[] = {"5i5h", "5a5b", "5h5i", "5b5a"};
    for (int repetition = 0; repetition < 3; ++repetition) {
        for (size_t move = 0; move < sizeof(cycle) / sizeof(cycle[0]); ++move) {
            if (!shogi_parse_and_make_move(&parsed, cycle[move])) return fail("repetition move");
        }
    }
    if (shogi_game_result(&parsed) != SHOGI_RESULT_DRAW) return fail("fourfold repetition draw");
    return 0;
}
