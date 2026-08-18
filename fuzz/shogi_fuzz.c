#include "shogi.h"

#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

static void try_sfen(const uint8_t *data, size_t size) {
    char text[1024];
    size_t length = size < sizeof(text) - 1 ? size : sizeof(text) - 1;
    memcpy(text, data, length);
    text[length] = '\0';

    ShogiPosition position;
    if (!shogi_position_from_sfen(&position, text)) return;

    /* Roundtrip through the lossless dual-hand form to check hash integrity
     * (the standard form only carries the side-to-move hand and is lossy when
     * the opponent also holds pieces). */
    char roundtrip[512];
    if (!shogi_position_to_sfen_full(&position, roundtrip, sizeof(roundtrip))) abort();
    ShogiPosition parsed;
    if (!shogi_position_from_sfen(&parsed, roundtrip)) abort();
    if (parsed.hash != position.hash) abort();

    char standard[512];
    if (!shogi_position_to_sfen(&position, standard, sizeof(standard))) abort();
    ShogiPosition standard_parsed;
    if (!shogi_position_from_sfen(&standard_parsed, standard)) abort();

    ShogiMove moves[SHOGI_MAX_MOVES];
    size_t count = shogi_generate_legal(&position, moves, SHOGI_MAX_MOVES);
    if (count != 0) {
        size_t choice = data[0] % count;
        ShogiPosition next = position;
        ShogiUndo undo;
        if (!shogi_make_move_undo(&next, moves[choice], &undo) ||
            !shogi_unmake_move(&next, &undo) ||
            memcmp(next.board, position.board, sizeof(next.board)) != 0 ||
            memcmp(next.hand, position.hand, sizeof(next.hand)) != 0 ||
            next.side != position.side || next.move_number != position.move_number ||
            next.hash != position.hash || next.history_length != position.history_length ||
            memcmp(next.king_square, position.king_square, sizeof(next.king_square)) != 0 ||
            memcmp(next.history, position.history, next.history_length * sizeof(next.history[0])) != 0 ||
            memcmp(next.history_mover, position.history_mover, next.history_length * sizeof(next.history_mover[0])) != 0 ||
            memcmp(next.history_check, position.history_check, next.history_length * sizeof(next.history_check[0])) != 0) abort();
    }
    (void)shogi_game_result_with_moves(&position, moves, SHOGI_MAX_MOVES, &count);
}

static void exercise_game(const uint8_t *data, size_t size) {
    ShogiPosition position;
    shogi_position_start(&position);
    size_t offset = 0;
    for (unsigned ply = 0; ply < 64 && offset < size; ++ply) {
        ShogiMove moves[SHOGI_MAX_MOVES];
        size_t count = shogi_generate_legal(&position, moves, SHOGI_MAX_MOVES);
        if (count == 0) break;

        unsigned selector = data[offset++];
        size_t choice = selector % count;
        char usi[16];
        if (!shogi_move_to_usi(moves[choice], usi, sizeof(usi))) abort();

        /* Exercise both the direct parser and the legal move application path. */
        ShogiMove parsed;
        if (!shogi_parse_usi_move(usi, &parsed) ||
            !shogi_parse_and_make_move(&position, usi)) abort();
        if (parsed.from != moves[choice].from || parsed.to != moves[choice].to ||
            parsed.promote != moves[choice].promote || parsed.drop != moves[choice].drop) abort();

        if (offset < size && (data[offset++] & 7U) == 0) {
            char arbitrary[32];
            size_t length = size - offset;
            if (length > sizeof(arbitrary) - 1) length = sizeof(arbitrary) - 1;
            memcpy(arbitrary, data + offset, length);
            arbitrary[length] = '\0';
            (void)shogi_parse_usi_move(arbitrary, &parsed);
            offset += length;
        }
        (void)shogi_game_result(&position);
    }
}

static void exercise_undo_sequence(const uint8_t *data, size_t size) {
    ShogiPosition position;
    ShogiPosition original;
    ShogiUndo undos[64];
    shogi_position_start(&position);
    original = position;
    size_t length = 0;
    for (size_t offset = 0; offset < size && length < 64; ++offset) {
        ShogiMove moves[SHOGI_MAX_MOVES];
        size_t count = shogi_generate_legal(&position, moves, SHOGI_MAX_MOVES);
        if (count == 0) break;
        if (!shogi_make_move_undo(&position, moves[data[offset] % count], &undos[length])) abort();
        ++length;
        char sfen[512];
        ShogiPosition parsed;
        if (!shogi_position_to_sfen_full(&position, sfen, sizeof(sfen)) ||
            !shogi_position_from_sfen(&parsed, sfen) || parsed.hash != position.hash) abort();
        if (shogi_game_result(&position) != SHOGI_RESULT_ONGOING) break;
    }
    while (length > 0) {
        --length;
        if (!shogi_unmake_move(&position, &undos[length])) abort();
    }
    if (memcmp(position.board, original.board, sizeof(position.board)) != 0 ||
        memcmp(position.hand, original.hand, sizeof(position.hand)) != 0 ||
        position.side != original.side || position.move_number != original.move_number ||
        position.hash != original.hash || position.history_length != original.history_length ||
        memcmp(position.king_square, original.king_square, sizeof(position.king_square)) != 0 ||
        memcmp(position.history, original.history,
               original.history_length * sizeof(original.history[0])) != 0 ||
        memcmp(position.history_mover, original.history_mover,
               original.history_length * sizeof(original.history_mover[0])) != 0 ||
        memcmp(position.history_check, original.history_check,
               original.history_length * sizeof(original.history_check[0])) != 0) abort();
}

int LLVMFuzzerTestOneInput(const uint8_t *data, size_t size) {
    if (data == NULL || size == 0) return 0;
    shogi_init();
    try_sfen(data, size);
    exercise_game(data, size);
    exercise_undo_sequence(data, size);
    return 0;
}
