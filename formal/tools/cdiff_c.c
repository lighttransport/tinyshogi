/* C side of tools/cdiff.py. One request per line: "<cmd> <hex payload>".
 *   S <sfen>          re-serialised SFEN, or REJECT
 *   L <sfen>          legal moves in USI, sorted, space separated
 *   M <sfen>|<usi>    SFEN after the move, or ILLEGAL
 *   P <sfen>|<depth>  perft count
 *   G <sfen>|<usi>*   play the space-separated moves, then
 *                     "<result> <sfen>" or "ILLEGAL <index>"
 * Hex payloads let any byte except NUL be tested. Output is flushed per
 * line so the driver can walk games interactively. */
/* Included (not linked) so the static rules functions can be called. */
#include "../../src/shogi.c"
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

static int hexval(int c) {
    if (c >= '0' && c <= '9') return c - '0';
    if (c >= 'a' && c <= 'f') return c - 'a' + 10;
    return -1;
}

/* Live state equal (see Shogi.C.activeState). */
static int same_active(const ShogiPosition *a, const ShogiPosition *b) {
    if (memcmp(a, b, offsetof(ShogiPosition, king_square) + 2) != 0 ||
        a->history_length != b->history_length) return 0;
    size_t n = a->history_length;
    return memcmp(a->history, b->history, n * sizeof(a->history[0])) == 0 &&
           memcmp(a->history_mover, b->history_mover, n) == 0 &&
           memcmp(a->history_check, b->history_check, n) == 0;
}

static int cmp_str(const void *a, const void *b) {
    return strcmp((const char *)a, (const char *)b);
}

static unsigned long long perft(const ShogiPosition *position, int depth) {
    if (depth == 0) return 1;
    ShogiMove moves[SHOGI_MAX_MOVES];
    size_t count = shogi_generate_legal(position, moves, SHOGI_MAX_MOVES);
    if (depth == 1) return count;
    unsigned long long total = 0;
    for (size_t i = 0; i < count; ++i) {
        static ShogiPosition stack[16];
        shogi_position_copy_active(&stack[depth], position);
        if (shogi_make_move(&stack[depth], moves[i])) total += perft(&stack[depth], depth - 1);
    }
    return total;
}

int main(void) {
    static char line[16384], text[8192], out[512];
    static char usi[SHOGI_MAX_MOVES][8];
    static ShogiPosition position;
    shogi_init();
    while (fgets(line, sizeof(line), stdin)) {
        size_t n = strcspn(line, "\n"), k = 0;
        char cmd = line[0];
        for (size_t i = 2; i + 1 < n && k + 1 < sizeof(text); i += 2)
            text[k++] = (char)(hexval(line[i]) * 16 + hexval(line[i + 1]));
        text[k] = '\0';
        char *arg = NULL;
        if (cmd != 'S') {
            arg = strrchr(text, '|');
            if (arg) *arg++ = '\0';
        }
        if (!shogi_position_from_sfen(&position, text)) {
            printf("REJECT\n");
        } else if (cmd == 'S') {
            if (shogi_position_to_sfen(&position, out, sizeof(out))) printf("%s\n", out);
            else printf("REJECT\n");
        } else if (cmd == 'L') {
            ShogiMove moves[SHOGI_MAX_MOVES];
            size_t count = shogi_generate_legal(&position, moves, SHOGI_MAX_MOVES);
            for (size_t i = 0; i < count; ++i) shogi_move_to_usi(moves[i], usi[i], sizeof(usi[i]));
            qsort(usi, count, sizeof(usi[0]), cmp_str);
            for (size_t i = 0; i < count; ++i) printf(i ? " %s" : "%s", usi[i]);
            printf("\n");
        } else if (cmd == 'M' && arg) {
            if (shogi_parse_and_make_move(&position, arg) &&
                shogi_position_to_sfen(&position, out, sizeof(out))) printf("%s\n", out);
            else printf("ILLEGAL\n");
        } else if (cmd == 'G' && arg) {
            static const char *names[] = {"ONGOING", "BLACK", "WHITE", "DRAW"};
            int index = 0, ok = 1;
            for (char *tok = strtok(arg, " "); tok; tok = strtok(NULL, " "), ++index) {
                if (!shogi_parse_and_make_move(&position, tok)) { ok = 0; break; }
            }
            if (!ok) printf("ILLEGAL %d\n", index);
            else if (shogi_position_to_sfen(&position, out, sizeof(out)))
                printf("%s %s\n", names[shogi_game_result(&position)], out);
            else printf("REJECT\n");
        } else if (cmd == 'A' || cmd == 'a') {
            for (int c = 0; c < 2; ++c)
                for (int t = 0; t < SHOGI_SQUARES; ++t)
                    putchar(square_attacked(&position, (uint8_t)t, (ShogiColor)c) ? '1' : '0');
            printf("\n");
        } else if (cmd == 'X' || cmd == 'x') {
            for (int f = 0; f < SHOGI_SQUARES; ++f)
                for (int t = 0; t < SHOGI_SQUARES; ++t)
                    putchar(shogi_piece_attacks_square(&position, (uint8_t)f, (uint8_t)t) ? '1' : '0');
            printf("\n");
        } else if (cmd == 'H' && arg) {
            if (shogi_parse_and_make_move(&position, arg) &&
                shogi_position_to_sfen(&position, out, sizeof(out)))
                printf("%s %llu\n", out, (unsigned long long)position.hash);
            else printf("ILLEGAL\n");
        } else if ((cmd == 'U' || cmd == 'V') && arg) {
            ShogiMove legal[SHOGI_MAX_MOVES], req;
            static ShogiPosition before;
            size_t count = shogi_generate_legal(&position, legal, SHOGI_MAX_MOVES), i;
            int found = 0;
            if (shogi_parse_usi_move(arg, &req))
                for (i = 0; i < count; ++i)
                    if (same_move(req, legal[i])) { req = legal[i]; found = 1; break; }
            if (!found) { printf("ILLEGAL\n"); fflush(stdout); continue; }
            ShogiUndo undo;
            before = position;
            int ok = cmd == 'V' ? shogi_make_move_undo_fast(&position, req, &undo)
                                : shogi_make_move_undo(&position, req, &undo);
            ok = ok && shogi_unmake_move(&position, &undo);
            printf(ok ? (same_active(&before, &position) ? "RESTORED\n" : "CHANGED\n") : "FAILED\n");
        } else if (cmd == 'P' && arg) {
            printf("%llu\n", perft(&position, atoi(arg)));
        } else {
            printf("BADCMD\n");
        }
        fflush(stdout);
    }
    return 0;
}
