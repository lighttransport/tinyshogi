#include "../src/shogi.h"

#include <stdio.h>
#include <string.h>

static int fail(const char *message) {
    fprintf(stderr, "rules test failed: %s\n", message);
    return 1;
}

static int check_undo_roundtrip(ShogiPosition *position, ShogiMove move, const char *label) {
    ShogiPosition before = *position;
    ShogiUndo undo;
    if (!shogi_make_move_undo(position, move, &undo) || !shogi_unmake_move(position, &undo)) {
        fprintf(stderr, "rules test failed: %s operation\n", label);
        return 1;
    }
    if (memcmp(before.board, position->board, sizeof(before.board)) != 0 ||
        memcmp(before.hand, position->hand, sizeof(before.hand)) != 0 ||
        before.side != position->side || before.move_number != position->move_number ||
        before.hash != position->hash || before.history_length != position->history_length ||
        memcmp(before.king_square, position->king_square, sizeof(before.king_square)) != 0 ||
        memcmp(before.history, position->history, before.history_length * sizeof(before.history[0])) != 0 ||
        memcmp(before.history_mover, position->history_mover,
               before.history_length * sizeof(before.history_mover[0])) != 0 ||
        memcmp(before.history_check, position->history_check,
               before.history_length * sizeof(before.history_check[0])) != 0) {
        fprintf(stderr, "rules test failed: %s state mismatch\n", label);
        return 1;
    }
    return 0;
}

static int check_hash_roundtrip(const ShogiPosition *position, const char *label) {
    char sfen[512];
    ShogiPosition parsed;
    if (!shogi_position_to_sfen(position, sfen, sizeof(sfen)) ||
        !shogi_position_from_sfen(&parsed, sfen) || parsed.hash != position->hash) {
        fprintf(stderr, "rules test failed: %s hash mismatch\n", label);
        return 1;
    }
    return 0;
}

static bool same_active_position(const ShogiPosition *left,
                                 const ShogiPosition *right) {
    return memcmp(left->board, right->board, sizeof(left->board)) == 0 &&
        memcmp(left->hand, right->hand, sizeof(left->hand)) == 0 &&
        left->side == right->side && left->move_number == right->move_number &&
        left->hash == right->hash && left->history_length == right->history_length &&
        memcmp(left->king_square, right->king_square, sizeof(left->king_square)) == 0 &&
        memcmp(left->history, right->history,
               left->history_length * sizeof(left->history[0])) == 0 &&
        memcmp(left->history_mover, right->history_mover,
               left->history_length * sizeof(left->history_mover[0])) == 0 &&
        memcmp(left->history_check, right->history_check,
               left->history_length * sizeof(left->history_check[0])) == 0;
}

static int check_fast_generated_moves(const ShogiPosition *position,
                                      const char *label) {
    ShogiMove moves[SHOGI_MAX_MOVES];
    size_t count = shogi_generate_legal(position, moves, SHOGI_MAX_MOVES);
    for (size_t index = 0; index < count; ++index) {
        ShogiPosition checked = *position, fast = *position;
        ShogiUndo checked_undo, fast_undo;
        if (!shogi_make_move_undo(&checked, moves[index], &checked_undo) ||
            !shogi_make_move_undo_fast(&fast, moves[index], &fast_undo))
            return fail(label);
        /* The fast path records the same active state and check bookkeeping
         * as the trusted path, so the two must match exactly. */
        if (!same_active_position(&checked, &fast)) return fail(label);
        if (!shogi_unmake_move(&checked, &checked_undo) ||
            !shogi_unmake_move(&fast, &fast_undo) ||
            !same_active_position(&checked, position) ||
            !same_active_position(&fast, position)) return fail(label);
    }
    return 0;
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
    if (check_fast_generated_moves(&position, "fast initial moves") != 0) return 1;
    if (perft(&position, 2) != 900) return fail("initial perft depth 2");
    if (perft(&position, 3) != 25470) return fail("initial perft depth 3");
    if (!shogi_parse_and_make_move(&position, "7g7f")) return fail("initial pawn move");
    if (check_hash_roundtrip(&position, "normal move") != 0) return 1;

    ShogiPosition undo_position;
    ShogiMove undo_move;
    shogi_position_start(&undo_position);
    if (!shogi_parse_usi_move("7g7f", &undo_move) ||
        check_undo_roundtrip(&undo_position, undo_move, "normal move") != 0) return 1;

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

    /* Both serialization entry points must preserve both hands. */
    {
        char standard[512], full[512];
        if (!shogi_position_from_sfen(&parsed, "4k4/9/9/9/9/9/9/9/4K4 b 1R1r 1"))
            return fail("dual-hand SFEN parse");
        if (!shogi_position_to_sfen(&parsed, standard, sizeof(standard)) ||
            strcmp(standard, "4k4/9/9/9/9/9/9/9/4K4 b Rr 1") != 0)
            return fail("standard SFEN both hands");
        if (check_hash_roundtrip(&parsed, "both hands, black to move")) return 1;
        if (!shogi_position_to_sfen_full(&parsed, full, sizeof(full)) ||
            strcmp(full, "4k4/9/9/9/9/9/9/9/4K4 b Rr 1") != 0)
            return fail("dual-hand SFEN lists both sides");
        if (!shogi_position_from_sfen(&parsed, "4k4/9/9/9/9/9/9/9/4K4 w 1R1r 2"))
            return fail("dual-hand SFEN parse (gote)");
        if (!shogi_position_to_sfen(&parsed, standard, sizeof(standard)) ||
            strcmp(standard, "4k4/9/9/9/9/9/9/9/4K4 w Rr 2") != 0)
            return fail("standard SFEN both hands (gote)");
        if (check_hash_roundtrip(&parsed, "both hands, white to move")) return 1;
        if (!shogi_position_to_sfen_full(&parsed, full, sizeof(full)) ||
            strcmp(full, "4k4/9/9/9/9/9/9/9/4K4 w Rr 2") != 0)
            return fail("dual-hand SFEN lists both sides (gote)");
    }

    if (!shogi_position_from_sfen(&parsed, "4k4/9/9/9/9/9/9/9/4K4 b S2Pb3p 1") ||
        check_hash_roundtrip(&parsed, "USI specification hand example")) return 1;

    ShogiMove drop;
    /* White's lance must not inherit Black's forward ray mask. */
    if (!shogi_position_from_sfen(&parsed, "4k4/9/4K4/9/4l4/9/9/9/9 b - 1") ||
        shogi_is_in_check(&parsed, SHOGI_BLACK)) return fail("white lance cannot attack backwards");
    if (!shogi_position_from_sfen(&parsed, "4k4/9/4l4/9/4K4/9/9/9/9 b - 1") ||
        !shogi_is_in_check(&parsed, SHOGI_BLACK)) return fail("white lance attacks forwards");
    if (!shogi_position_from_sfen(&parsed, "9/9/4k4/9/4L4/9/9/9/4K4 w - 1") ||
        !shogi_is_in_check(&parsed, SHOGI_WHITE)) return fail("black lance attacks forwards");
    if (!shogi_position_from_sfen(&parsed, "9/9/4L4/9/4k4/9/9/9/4K4 w - 1") ||
        shogi_is_in_check(&parsed, SHOGI_WHITE)) return fail("black lance cannot attack backwards");
    if (!shogi_parse_usi_move("P*7f", &drop) || drop.from != SHOGI_SQ_NONE) return fail("drop notation");
    if (shogi_parse_and_make_move(&position, "7g7f+")) return fail("invalid pawn promotion acceptance");
    if (shogi_game_result(&position) != SHOGI_RESULT_ONGOING) return fail("premature terminal result");

    if (!shogi_position_from_sfen(&parsed, "4k4/9/4P4/9/9/9/9/9/4K4 b - 1")) return fail("promotion SFEN");
    if (!shogi_parse_and_make_move(&parsed, "5c5b+")) return fail("promotion move");
    if (shogi_piece_type(parsed.board[1 * 9 + 4]) != SHOGI_PRO_PAWN) return fail("promotion piece");
    if (check_hash_roundtrip(&parsed, "promotion move") != 0) return 1;
    if (!shogi_position_from_sfen(&undo_position, "4k4/9/4P4/9/9/9/9/9/4K4 b - 1") ||
        !shogi_parse_usi_move("5c5b+", &undo_move) ||
        check_undo_roundtrip(&undo_position, undo_move, "promotion move") != 0) return 1;

    if (!shogi_position_from_sfen(&parsed, "4k4/9/9/9/9/9/9/9/4K4 b P 1")) return fail("drop SFEN");
    if (check_fast_generated_moves(&parsed, "fast drop moves") != 0) return 1;
    if (!shogi_parse_and_make_move(&parsed, "P*5e")) return fail("pawn drop");
    if (check_hash_roundtrip(&parsed, "drop move") != 0) return 1;
    if (!shogi_position_from_sfen(&undo_position, "4k4/9/9/9/9/9/9/9/4K4 b P 1") ||
        !shogi_parse_usi_move("P*5e", &undo_move) ||
        check_undo_roundtrip(&undo_position, undo_move, "drop move") != 0) return 1;

    if (!shogi_position_from_sfen(&parsed, "4k4/9/9/9/4P4/9/9/9/4K4 b P 1")) return fail("nifu SFEN");
    if (shogi_parse_and_make_move(&parsed, "P*5d")) return fail("nifu rejection");
    if (!shogi_position_from_sfen(&parsed, "4k4/9/9/9/9/9/9/9/4K4 b N 1")) return fail("dead drop SFEN");
    if (shogi_parse_and_make_move(&parsed, "N*5a")) return fail("dead-rank drop rejection");

    /* Material validation: reject impossible piece counts. */
    if (shogi_position_from_sfen(&parsed, "3RRR3/9/9/9/4k4/9/9/9/4K4 b - 1"))
        return fail("material: three rooks accepted");
    if (!shogi_position_from_sfen(&parsed, "1+R2+R4/9/9/9/4k4/9/9/9/4K4 b - 1"))
        return fail("material: two dragons are legal");
    if (!shogi_position_from_sfen(&parsed, "1+B2+B4/9/9/9/4k4/9/9/9/4K4 b - 1"))
        return fail("material: two horses are legal");
    if (shogi_position_from_sfen(&parsed, "1R2R4/9/9/9/4k4/9/9/9/4K4 b r 1"))
        return fail("material: global rook limit");
    if (shogi_position_from_sfen(&parsed, "1+R2+R4/9/9/9/4k4/9/9/9/4K4 b 3R 1"))
        return fail("material: rook hand overflow accepted");
    if (shogi_can_promote(SHOGI_GOLD) || shogi_can_promote(SHOGI_KING))
        return fail("gold and king cannot promote");
    if (!shogi_position_from_sfen(&parsed, "4k4/G8/9/9/9/9/9/9/4K4 b - 1") ||
        shogi_parse_and_make_move(&parsed, "9b8a+")) return fail("gold promotion rejection");
    if (shogi_position_from_sfen(&parsed, "4k4/+G8/9/9/9/9/9/9/4K4 b - 1"))
        return fail("promoted gold SFEN rejection");

    if (!shogi_position_from_sfen(&parsed, "4r3k/9/9/9/9/9/9/4R4/4K4 b - 1")) return fail("pin SFEN");
    if (check_fast_generated_moves(&parsed, "fast pinned moves") != 0) return 1;
    if (shogi_parse_and_make_move(&parsed, "5h4h")) return fail("self-check rejection");

    if (!shogi_position_from_sfen(&parsed,
            "4k4/9/9/9/9/5+b3/4R4/3K5/9 b - 1"))
        return fail("diagonal pin SFEN");
    if (shogi_parse_and_make_move(&parsed, "5g5i"))
        return fail("opposite-ray pinned move rejection");

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

    /* Perpetual check: the position repeats four times while Black gives check
     * on every one of its moves (rook 5a/5b checks the cornered white king, which
     * can only shuttle 1a/1b), so the repetition is a win for the non-checking
     * side (White) rather than a draw. */
    if (!shogi_position_from_sfen(&parsed, "4R3k/9/9/9/9/9/9/9/K8 w - 1"))
        return fail("perpetual-check SFEN");
    const char *perpetual[] = {"1a1b", "5a5b", "1b1a", "5b5a"};
    for (int cycle = 0; cycle < 3; ++cycle) {
        for (size_t move = 0; move < sizeof(perpetual) / sizeof(perpetual[0]); ++move) {
            if (!shogi_parse_and_make_move(&parsed, perpetual[move])) return fail("perpetual-check move");
        }
    }
    if (shogi_game_result(&parsed) != SHOGI_RESULT_WHITE_WIN)
        return fail("perpetual check is a win for the non-checking side");

    /* The fast make path records check bookkeeping only when enabled (the
     * PerpetualCheck option); verify both states directly. */
    {
        ShogiPosition gate_position;
        ShogiMove gate_move;
        ShogiUndo gate_undo;
        if (!shogi_position_from_sfen(&gate_position, "R3k4/9/9/9/9/9/9/9/4K4 b - 1"))
            return fail("perpetual-check gate SFEN");
        if (!shogi_parse_usi_move("9a6a", &gate_move)) return fail("perpetual-check gate move");
        shogi_set_fast_check_bookkeeping(true);
        if (!shogi_make_move_undo_fast(&gate_position, gate_move, &gate_undo))
            return fail("perpetual-check gate make (on)");
        if (gate_position.history_check[gate_position.history_length - 1U] != 1)
            return fail("fast path records check when enabled");
        if (!shogi_unmake_move(&gate_position, &gate_undo)) return fail("perpetual-check gate unmake");
        shogi_set_fast_check_bookkeeping(false);
        if (!shogi_make_move_undo_fast(&gate_position, gate_move, &gate_undo))
            return fail("perpetual-check gate make (off)");
        if (gate_position.history_check[gate_position.history_length - 1U] != 0)
            return fail("fast path defers check when disabled");
        if (!shogi_unmake_move(&gate_position, &gate_undo)) return fail("perpetual-check gate unmake");
        shogi_set_fast_check_bookkeeping(true);
    }
    return 0;
}
