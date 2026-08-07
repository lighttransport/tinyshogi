#include "../src/brute.h"

#include <stdio.h>
#include <stdlib.h>
#include <string.h>

int main(void) {
    char line[1024];
    shogi_init();
    while (fgets(line, sizeof(line), stdin) != NULL) {
        char *tab = strchr(line, '\t');
        if (tab == NULL) { puts("error"); fflush(stdout); continue; }
        *tab++ = '\0';
        unsigned depth = (unsigned)strtoul(tab, NULL, 10);
        ShogiPosition position;
        if (!shogi_position_from_sfen(&position, line)) { puts("error"); fflush(stdout); continue; }
        ShogiBruteResult result = shogi_brute_search(&position, depth, 0);
        char move[16] = "resign";
        if (result.has_move) (void)shogi_move_to_usi(result.move, move, sizeof(move));
        printf("%s %d %llu\n", move, result.score_cp, (unsigned long long)result.nodes);
        fflush(stdout);
    }
    return 0;
}
