#include "../src/nnue.h"

#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

typedef struct {
    uint8_t board[SHOGI_SQUARES]; uint8_t hand[14]; uint8_t padding;
    int16_t value; uint8_t side; uint8_t source;
} Record;

static int read_data(const char *path, Record **records, uint32_t *count) {
    FILE *file = fopen(path, "rb"); if (!file) return 1;
    char magic[4]; uint32_t header[3];
    int ok = fread(magic, 1, 4, file) == 4 && memcmp(magic, "NDF1", 4) == 0 &&
             fread(header, sizeof(*header), 3, file) == 3 && header[0] == 1 &&
             header[2] == sizeof(Record);
    Record *data = ok ? calloc(header[1], sizeof(*data)) : NULL;
    if (ok) ok = data != NULL && fread(data, sizeof(*data), header[1], file) == header[1];
    fclose(file); if (!ok) { free(data); return 1; }
    *records = data; *count = header[1]; return 0;
}

static void make_position(const Record *record, ShogiPosition *position) {
    memset(position, 0, sizeof(*position));
    memcpy(position->board, record->board, sizeof(position->board));
    memcpy(position->hand, record->hand, sizeof(position->hand));
    position->side = (ShogiColor)record->side;
    position->king_square[0] = position->king_square[1] = SHOGI_SQ_NONE;
    for (uint8_t square = 0; square < SHOGI_SQUARES; ++square)
        if (position->board[square] != SHOGI_EMPTY &&
            shogi_piece_type(position->board[square]) == SHOGI_KING)
            position->king_square[shogi_piece_color(position->board[square])] = square;
}

int main(int argc, char **argv) {
    if (argc != 3) { fprintf(stderr, "usage: %s model.nnue data.ndf1\n", argv[0]); return 2; }
    ShogiNnueModel model; shogi_nnue_model_init(&model);
    Record *records = NULL; uint32_t count = 0;
    if (!shogi_nnue_model_load(&model, argv[1]) || read_data(argv[2], &records, &count) != 0) return 1;
    shogi_init(); double squared = 0.0; int min_value = 1000000000, max_value = -1000000000;
    for (uint32_t index = 0; index < count; ++index) {
        ShogiPosition position; make_position(&records[index], &position);
        int value = shogi_nnue_evaluate_position(&model, &position, position.side);
        int error = value - records[index].value;
        squared += (double)error * error;
        if (value < min_value) min_value = value;
        if (value > max_value) max_value = value;
    }
    printf("samples=%u mse=%.3f value_min=%d value_max=%d\n", count,
           count == 0 ? 0.0 : squared / count, min_value, max_value);
    free(records); shogi_nnue_model_destroy(&model); return 0;
}
