#include <stdbool.h>
#include <stdio.h>
#include <string.h>

#define BOARD_SIZE 5

typedef struct {
    char squares[BOARD_SIZE][BOARD_SIZE];
} Position;

static void position_reset(Position *position) {
    static const char start[BOARD_SIZE][BOARD_SIZE + 1] = {
        "kgsbr",
        ".p...",
        ".....",
        "...P.",
        "RBSGK"
    };

    for (int row = 0; row < BOARD_SIZE; ++row) {
        for (int col = 0; col < BOARD_SIZE; ++col) {
            position->squares[row][col] = start[row][col];
        }
    }
}

static void print_board(const Position *position) {
    for (int row = 0; row < BOARD_SIZE; ++row) {
        for (int col = 0; col < BOARD_SIZE; ++col) {
            putchar(position->squares[row][col]);
            if (col + 1 < BOARD_SIZE) {
                putchar(' ');
            }
        }
        putchar('\n');
    }
}

static bool find_bestmove(const Position *position, char out_move[6]) {
    for (int row = 0; row < BOARD_SIZE; ++row) {
        for (int col = 0; col < BOARD_SIZE; ++col) {
            if (position->squares[row][col] == 'P') {
                int to_row = row - 1;
                if (to_row >= 0 && position->squares[to_row][col] == '.') {
                    int from_file = BOARD_SIZE - col;
                    int to_file = BOARD_SIZE - col;
                    char from_rank = (char)('a' + row);
                    char to_rank = (char)('a' + to_row);

                    snprintf(out_move, 6, "%d%c%d%c", from_file, from_rank, to_file, to_rank);
                    return true;
                }
            }
        }
    }

    return false;
}

static int run_selftest(void) {
    Position position;
    char bestmove[6] = {0};

    position_reset(&position);
    if (!find_bestmove(&position, bestmove)) {
        fputs("selftest failed: no move found\n", stderr);
        return 1;
    }

    if (strcmp(bestmove, "2d2c") != 0) {
        fprintf(stderr, "selftest failed: expected 2d2c, got %s\n", bestmove);
        return 1;
    }

    return 0;
}

int main(int argc, char **argv) {
    Position position;
    char line[128];

    if (argc > 1 && strcmp(argv[1], "--selftest") == 0) {
        return run_selftest();
    }

    position_reset(&position);

    while (fgets(line, sizeof(line), stdin) != NULL) {
        if (strncmp(line, "usi", 3) == 0) {
            puts("id name tinyshogi-c11");
            puts("id author tinyshogi");
            puts("usiok");
        } else if (strncmp(line, "isready", 7) == 0) {
            puts("readyok");
        } else if (strncmp(line, "position startpos", 17) == 0) {
            position_reset(&position);
        } else if (strncmp(line, "go", 2) == 0) {
            char bestmove[6] = {0};
            if (find_bestmove(&position, bestmove)) {
                printf("bestmove %s\n", bestmove);
            } else {
                puts("bestmove resign");
            }
        } else if (strncmp(line, "d", 1) == 0) {
            print_board(&position);
        } else if (strncmp(line, "quit", 4) == 0) {
            break;
        }

        fflush(stdout);
    }

    return 0;
}
