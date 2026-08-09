#include "../src/nnue.h"

#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

typedef struct {
    uint8_t board[SHOGI_SQUARES];
    uint8_t hand[14];
    uint8_t padding;
    int16_t value;
    uint8_t side;
    uint8_t source;
} Record;

static int compare_unsigned(const void *left, const void *right) {
    unsigned a = *(const unsigned *)left, b = *(const unsigned *)right;
    return (a > b) - (a < b);
}

static int read_data(const char *path, Record **records, uint32_t *count) {
    FILE *file = fopen(path, "rb");
    char magic[4];
    uint32_t header[3];
    if (file == NULL || fread(magic, 1, 4, file) != 4 ||
        memcmp(magic, "NDF1", 4) != 0 ||
        fread(header, sizeof(*header), 3, file) != 3 || header[0] != 1 ||
        header[2] != sizeof(Record)) {
        if (file != NULL) fclose(file);
        return 1;
    }
    *records = malloc((size_t)header[1] * sizeof(**records));
    if (*records == NULL ||
        fread(*records, sizeof(**records), header[1], file) != header[1]) {
        free(*records);
        fclose(file);
        return 1;
    }
    fclose(file);
    *count = header[1];
    return 0;
}

static void make_position(const Record *record, ShogiPosition *position) {
    memset(position, 0, sizeof(*position));
    memcpy(position->board, record->board, sizeof(position->board));
    memcpy(position->hand, record->hand, sizeof(position->hand));
    position->side = (ShogiColor)record->side;
    position->king_square[0] = position->king_square[1] = SHOGI_SQ_NONE;
    for (uint8_t square = 0; square < SHOGI_SQUARES; ++square) {
        uint8_t piece = position->board[square];
        if (piece != SHOGI_EMPTY && shogi_piece_type(piece) == SHOGI_KING)
            position->king_square[shogi_piece_color(piece)] = square;
    }
}

static size_t best_move(const ShogiNnueModel *model, ShogiPosition *position,
                        const ShogiMove *moves, size_t count) {
    size_t best = 0;
    int best_score = -2147483647;
    ShogiColor perspective = position->side;
    for (size_t index = 0; index < count; ++index) {
        ShogiUndo undo;
        if (!shogi_make_move_undo(position, moves[index], &undo)) continue;
        int score = shogi_nnue_evaluate_position(model, position, perspective);
        (void)shogi_unmake_move(position, &undo);
        if (score > best_score) {
            best_score = score;
            best = index;
        }
    }
    return best;
}

int main(int argc, char **argv) {
    if (argc != 4) {
        fprintf(stderr, "usage: %s baseline.nnue candidate.nnue data.ndf1\n", argv[0]);
        return 2;
    }
    ShogiNnueModel baseline, candidate;
    shogi_nnue_model_init(&baseline);
    shogi_nnue_model_init(&candidate);
    Record *records = NULL;
    uint32_t count = 0;
    if (!shogi_nnue_model_load(&baseline, argv[1]) ||
        !shogi_nnue_model_load(&candidate, argv[2]) ||
        read_data(argv[3], &records, &count) != 0 || count == 0) return 1;
    unsigned *errors = malloc((size_t)count * sizeof(*errors));
    if (errors == NULL) return 1;
    uint64_t error_sum = 0, positions_with_moves = 0, agreements = 0;
    shogi_init();
    for (uint32_t sample = 0; sample < count; ++sample) {
        ShogiPosition position;
        make_position(&records[sample], &position);
        int first = shogi_nnue_evaluate_position(&baseline, &position, position.side);
        int second = shogi_nnue_evaluate_position(&candidate, &position, position.side);
        unsigned error = (unsigned)(first > second ? first - second : second - first);
        errors[sample] = error;
        error_sum += error;
        ShogiMove moves[SHOGI_MAX_MOVES];
        size_t move_count = shogi_generate_legal_mut(&position, moves, SHOGI_MAX_MOVES);
        if (move_count != 0) {
            size_t first_best = best_move(&baseline, &position, moves, move_count);
            size_t second_best = best_move(&candidate, &position, moves, move_count);
            agreements += first_best == second_best;
            ++positions_with_moves;
        }
    }
    qsort(errors, count, sizeof(*errors), compare_unsigned);
    size_t p99_index = ((size_t)count * 99U + 99U) / 100U - 1U;
    double mae = (double)error_sum / count;
    double agreement = positions_with_moves == 0 ? 100.0 :
        (double)agreements * 100.0 / positions_with_moves;
    printf("positions=%u mae_cp=%.6f p99_cp=%u top_move_agreement=%.4f%% (%llu/%llu)\n",
           count, mae, errors[p99_index], agreement,
           (unsigned long long)agreements,
           (unsigned long long)positions_with_moves);
    int result = mae <= 1.0 && errors[p99_index] <= 4U && agreement >= 99.5 ? 0 : 1;
    free(errors);
    free(records);
    shogi_nnue_model_destroy(&candidate);
    shogi_nnue_model_destroy(&baseline);
    return result;
}
