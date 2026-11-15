/* C side of tools/cdiff.py: one SFEN per line on stdin (hex-encoded, so any
 * byte except NUL can be tested); prints the re-serialised SFEN or REJECT. */
#include "../../src/shogi.h"
#include <stdio.h>
#include <string.h>

static int hexval(int c) {
    if (c >= '0' && c <= '9') return c - '0';
    if (c >= 'a' && c <= 'f') return c - 'a' + 10;
    return -1;
}

int main(void) {
    static char line[8192], text[4096], out[512];
    shogi_init();
    while (fgets(line, sizeof(line), stdin)) {
        size_t n = strcspn(line, "\n"), k = 0;
        for (size_t i = 0; i + 1 < n && k + 1 < sizeof(text); i += 2)
            text[k++] = (char)(hexval(line[i]) * 16 + hexval(line[i + 1]));
        text[k] = '\0';
        ShogiPosition position;
        if (shogi_position_from_sfen(&position, text) &&
            shogi_position_to_sfen(&position, out, sizeof(out)))
            printf("%s\n", out);
        else
            printf("REJECT\n");
    }
    return 0;
}
