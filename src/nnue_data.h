#ifndef TINYSHOGI_NNUE_DATA_H
#define TINYSHOGI_NNUE_DATA_H

#include "shogi.h"

#include <stdbool.h>
#include <stdint.h>
#include <stdio.h>
#include <string.h>

#define SHOGI_NDF_VERSION 1U
#define SHOGI_NDF_RECORD_SIZE 100U

typedef struct {
    uint8_t board[SHOGI_SQUARES];
    uint8_t hand[14];
    uint8_t padding;
    int16_t value;
    uint8_t side;
    uint8_t source;
} ShogiNdfRecord;

_Static_assert(sizeof(ShogiNdfRecord) == SHOGI_NDF_RECORD_SIZE,
               "NDF1 record layout changed");

static inline void shogi_ndf_record_from_position(ShogiNdfRecord *record,
                                                   const ShogiPosition *position,
                                                   int value, uint8_t source) {
    memcpy(record->board, position->board, sizeof(record->board));
    memcpy(record->hand, position->hand, sizeof(record->hand));
    record->padding = 0;
    record->value = (int16_t)value;
    record->side = (uint8_t)position->side;
    record->source = source;
}

static inline bool shogi_ndf_write_header(FILE *file, uint32_t count) {
    const char magic[4] = {'N', 'D', 'F', '1'};
    uint32_t header[3] = {SHOGI_NDF_VERSION, count, SHOGI_NDF_RECORD_SIZE};
    return file != NULL && fwrite(magic, 1, sizeof(magic), file) == sizeof(magic) &&
           fwrite(header, sizeof(*header), 3, file) == 3;
}

static inline bool shogi_ndf_read_header(FILE *file, uint32_t *count) {
    char magic[4];
    uint32_t header[3];
    if (file == NULL || count == NULL ||
        fread(magic, 1, sizeof(magic), file) != sizeof(magic) ||
        memcmp(magic, "NDF1", sizeof(magic)) != 0 ||
        fread(header, sizeof(*header), 3, file) != 3 ||
        header[0] != SHOGI_NDF_VERSION || header[2] != SHOGI_NDF_RECORD_SIZE)
        return false;
    *count = header[1];
    return true;
}

#endif
