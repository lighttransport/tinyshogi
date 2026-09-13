/* SPDX-License-Identifier: Apache-2.0 */
#include "dl_features.h"
#include <math.h>
#include <stdlib.h>
#include <string.h>
static const ShogiPieceType hands[7] = {SHOGI_PAWN, SHOGI_LANCE,  SHOGI_KNIGHT, SHOGI_SILVER,
                                        SHOGI_GOLD, SHOGI_BISHOP, SHOGI_ROOK};
static int canonical(const ShogiPosition *p, int sq) {
    return p->side == SHOGI_BLACK ? sq : 80 - sq;
}
int shogi_dl_action(const ShogiPosition *p, ShogiMove m) {
    if (!p || m.to >= 81 || m.promote > 1)
        return -1;
    int to = canonical(p, m.to);
    if (m.drop) {
        if (m.promote)
            return -1;
        for (int i = 0; i < 7; i++)
            if (m.drop == hands[i])
                return to * 139 + 132 + i;
        return -1;
    }
    if (m.from >= 81)
        return -1;
    int from = canonical(p, m.from), dx = to % 9 - from % 9, dy = to / 9 - from / 9, plane = -1;
    if (dy == -2 && (dx == -1 || dx == 1))
        plane = 128 + (dx == 1 ? 2 : 0) + m.promote;
    else {
        const int vx[8] = {0, 1, 1, 1, 0, -1, -1, -1}, vy[8] = {-1, -1, 0, 1, 1, 1, 0, -1};
        int dist = abs(dx) > abs(dy) ? abs(dx) : abs(dy);
        for (int d = 0; d < 8 && dist > 0 && dist <= 8; d++)
            if (dx == vx[d] * dist && dy == vy[d] * dist)
                plane = (d * 8 + dist - 1) * 2 + m.promote;
    }
    return plane < 0 ? -1 : from * 139 + plane;
}
void shogi_dl_encode(const ShogiPosition *p, float f[SHOGI_DL_FEATURES]) {
    memset(f, 0, SHOGI_DL_FEATURES * sizeof(float));
    for (int sq = 0; sq < 81; sq++) {
        uint8_t piece = p->board[sq];
        if (piece == SHOGI_EMPTY)
            continue;
        unsigned rel = shogi_piece_color(piece) == p->side ? 0 : 1,
                 type = shogi_piece_type(piece) - 1;
        f[canonical(p, sq) * 80 + rel * 14 + type] = 1;
        for (int dst = 0; dst < 81; dst++)
            if (shogi_piece_attacks_square(p, (uint8_t)sq, (uint8_t)dst))
                f[canonical(p, dst) * 80 + 28 + rel * 14 + type] = 1;
    }
    float scalar[22] = {0};
    const float maxima[7] = {18, 4, 4, 4, 4, 2, 2};
    for (unsigned rel = 0; rel < 2; rel++)
        for (unsigned h = 0; h < 7; h++)
            scalar[rel * 7 + h] = p->hand[(unsigned)p->side ^ rel][h] / maxima[h];
    scalar[14] = shogi_is_in_check(p, p->side);
    scalar[15] = shogi_is_in_check(p, (ShogiColor)(p->side ^ 1));
    unsigned previous = 0;
    size_t last = SIZE_MAX;
    for (size_t i = 0; i + 1 < p->history_length; i++)
        if (p->history[i] == p->hash) {
            previous++;
            last = i;
        }
    for (unsigned i = 0; i < 3; i++)
        scalar[16 + i] = previous > i;
    if (last != SIZE_MAX)
        for (unsigned rel = 0; rel < 2; rel++) {
            bool moved = false, all = true;
            for (size_t i = last + 1; i < p->history_length; i++)
                if (p->history_mover[i] == ((unsigned)p->side ^ rel)) {
                    moved = true;
                    if (!p->history_check[i])
                        all = false;
                }
            scalar[19 + rel] = moved && all;
        }
    scalar[21] = fminf((float)p->move_number / 512, 1);
    for (int sq = 0; sq < 81; sq++) {
        memcpy(f + sq * 80 + 56, scalar, sizeof(scalar));
        f[sq * 80 + 78] = (float)(sq % 9) / 4 - 1;
        f[sq * 80 + 79] = (float)(sq / 9) / 4 - 1;
    }
}
