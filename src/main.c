#define _POSIX_C_SOURCE 200809L

#include "search.h"
#include "shogi.h"

#include <errno.h>
#include <poll.h>
#include <stdbool.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/types.h>
#include <time.h>
#include <unistd.h>

typedef struct {
    ShogiPosition position;
    SearchOptions options;
    SearchJob *job;
    uint64_t last_info_ns;
    bool quit;
} Application;

static uint64_t monotonic_ns_main(void) {
    struct timespec time;
    clock_gettime(CLOCK_MONOTONIC, &time);
    return (uint64_t)time.tv_sec * UINT64_C(1000000000) + (uint64_t)time.tv_nsec;
}

static unsigned detected_threads(void) {
    long count = sysconf(_SC_NPROCESSORS_ONLN);
    if (count < 1) count = 1;
    if (count > 8) count = 8;
    return (unsigned)count;
}

static void print_bestmove(const SearchResult *result) {
    if (result->declaration_win) {
        puts("bestmove win");
    } else if (result->resign || !result->has_move) {
        puts("bestmove resign");
    } else {
        char text[16];
        if (shogi_move_to_usi(result->move, text, sizeof(text))) printf("bestmove %s\n", text);
        else puts("bestmove resign");
    }
    fflush(stdout);
}

static void print_search_info(const Application *application) {
    SearchProgress progress;
    if (application->job == NULL || !search_get_progress(application->job, &progress)) return;
    SearchLine lines[SEARCH_MAX_MULTIPV];
    size_t line_count = search_get_root_lines(application->job, lines, application->options.multi_pv);
    if (line_count == 0) {
        printf("info nodes %llu nps %llu time %llu multipv 1 score cp %d",
               (unsigned long long)progress.nodes,
               (unsigned long long)progress.nps,
               (unsigned long long)progress.time_ms,
               progress.score_cp);
        if (progress.has_move) {
            char move[16];
            if (shogi_move_to_usi(progress.move, move, sizeof(move))) printf(" pv %s", move);
        }
        putchar('\n');
        fflush(stdout);
        return;
    }
    for (size_t index = 0; index < line_count; ++index) {
        int score = lines[index].score_cp;
        printf("info nodes %llu nps %llu time %llu multipv %zu score cp %d",
               (unsigned long long)progress.nodes,
               (unsigned long long)progress.nps,
               (unsigned long long)progress.time_ms,
               index + 1,
               score);
        fputs(" pv", stdout);
        size_t pv_length = lines[index].pv_length;
        if (pv_length == 0) pv_length = 1;
        for (size_t pv_index = 0; pv_index < pv_length; ++pv_index) {
            ShogiMove move_value = pv_length == lines[index].pv_length ?
                lines[index].pv[pv_index] : lines[index].move;
            char move[16];
            if (shogi_move_to_usi(move_value, move, sizeof(move))) printf(" %s", move);
        }
        putchar('\n');
    }
    fflush(stdout);
}

static void finish_job(Application *application, bool emit_bestmove) {
    if (application->job == NULL) return;
    if (!search_is_done(application->job)) search_request_stop(application->job);
    SearchResult result;
    search_join(application->job, &result);
    if (emit_bestmove) print_bestmove(&result);
    search_destroy(application->job);
    application->job = NULL;
}

static bool parse_unsigned(const char *text, uint64_t *value) {
    if (text == NULL || *text == '\0' || text[0] == '-') return false;
    char *end = NULL;
    errno = 0;
    unsigned long long parsed = strtoull(text, &end, 10);
    if (errno != 0 || *end != '\0') return false;
    *value = (uint64_t)parsed;
    return true;
}

static bool parse_int(const char *text, int *value) {
    uint64_t parsed;
    if (!parse_unsigned(text, &parsed) || parsed > (uint64_t)INT32_MAX) return false;
    *value = (int)parsed;
    return true;
}

static size_t tokenize(char *line, char **tokens, size_t capacity) {
    size_t count = 0;
    char *save = NULL;
    char *token = strtok_r(line, " \t\r\n", &save);
    while (token != NULL && count < capacity) {
        tokens[count++] = token;
        token = strtok_r(NULL, " \t\r\n", &save);
    }
    return count;
}

static bool set_position_command(Application *application, char *line) {
    char *tokens[1024];
    size_t count = tokenize(line, tokens, sizeof(tokens) / sizeof(tokens[0]));
    if (count < 2 || strcmp(tokens[0], "position") != 0) return false;
    ShogiPosition next;
    size_t move_start = 0;
    if (strcmp(tokens[1], "startpos") == 0) {
        shogi_position_start(&next);
        move_start = 2;
    } else if (strcmp(tokens[1], "sfen") == 0 && count >= 6) {
        char sfen[512];
        int written = snprintf(sfen, sizeof(sfen), "%s %s %s %s", tokens[2], tokens[3], tokens[4], tokens[5]);
        if (written < 0 || (size_t)written >= sizeof(sfen) || !shogi_position_from_sfen(&next, sfen)) return false;
        move_start = 6;
    } else {
        return false;
    }
    if (move_start < count && strcmp(tokens[move_start], "moves") != 0) return false;
    if (move_start < count) ++move_start;
    for (size_t index = move_start; index < count; ++index) {
        if (!shogi_parse_and_make_move(&next, tokens[index])) return false;
    }
    application->position = next;
    return true;
}

static bool is_go_keyword(const char *token) {
    static const char *const keywords[] = {
        "searchmoves", "nodes", "depth", "movetime", "btime", "wtime",
        "byoyomi", "binc", "winc", "infinite", "ponder"
    };
    for (size_t index = 0; index < sizeof(keywords) / sizeof(keywords[0]); ++index) {
        if (strcmp(token, keywords[index]) == 0) return true;
    }
    return false;
}

static bool parse_go(char *line, SearchLimits *limits) {
    char *tokens[128];
    size_t count = tokenize(line, tokens, sizeof(tokens) / sizeof(tokens[0]));
    if (count < 1 || strcmp(tokens[0], "go") != 0) return false;
    memset(limits, 0, sizeof(*limits));
    for (size_t index = 1; index < count; ++index) {
        if (strcmp(tokens[index], "infinite") == 0) {
            limits->infinite = true;
            continue;
        }
        if (strcmp(tokens[index], "ponder") == 0) {
            limits->ponder = true;
            continue;
        }
        if (strcmp(tokens[index], "searchmoves") == 0) {
            limits->has_searchmoves = true;
            ++index;
            while (index < count && !is_go_keyword(tokens[index])) {
                if (limits->searchmove_count >= SHOGI_MAX_MOVES ||
                    !shogi_parse_usi_move(tokens[index], &limits->searchmoves[limits->searchmove_count])) {
                    return false;
                }
                ++limits->searchmove_count;
                ++index;
            }
            --index;
            continue;
        }
        int value;
        uint64_t nodes;
        if (index + 1 >= count) return false;
        const char *key = tokens[index];
        const char *argument = tokens[++index];
        if (strcmp(key, "nodes") == 0) {
            if (!parse_unsigned(argument, &nodes)) return false;
            limits->nodes = nodes;
        } else if (strcmp(key, "depth") == 0) {
            if (!parse_int(argument, &value)) return false;
            limits->depth = value;
        } else if (strcmp(key, "movetime") == 0) {
            if (!parse_int(argument, &value)) return false;
            limits->movetime_ms = value;
        } else if (strcmp(key, "btime") == 0) {
            if (!parse_int(argument, &value)) return false;
            limits->btime_ms = value;
        } else if (strcmp(key, "wtime") == 0) {
            if (!parse_int(argument, &value)) return false;
            limits->wtime_ms = value;
        } else if (strcmp(key, "byoyomi") == 0) {
            if (!parse_int(argument, &value)) return false;
            limits->byoyomi_ms = value;
        } else if (strcmp(key, "binc") == 0) {
            if (!parse_int(argument, &value)) return false;
            limits->binc_ms = value;
        } else if (strcmp(key, "winc") == 0) {
            if (!parse_int(argument, &value)) return false;
            limits->winc_ms = value;
        }
    }
    return true;
}

static void print_usi(void) {
    printf("id name tinyshogi-c11-mcts\n");
    printf("id author tinyshogi\n");
    printf("option name Threads type spin default %u min 1 max 64\n", detected_threads());
    printf("option name Seed type spin default 0 min 0 max 2147483647\n");
    printf("option name MaxTreeNodes type spin default 1000000 min 1000 max 10000000\n");
    printf("option name RolloutDepth type spin default %u min 1 max 512\n", SEARCH_DEFAULT_ROLLOUT_DEPTH);
    printf("option name UCTExploration type spin default %u min 1 max 3000\n", SEARCH_DEFAULT_EXPLORATION_MILLI);
    printf("option name MultiPV type spin default %u min 1 max %u\n", SEARCH_DEFAULT_MULTIPV, SEARCH_MAX_MULTIPV);
    puts("usiok");
    fflush(stdout);
}

static void set_option(Application *application, char *line) {
    char *tokens[32];
    size_t count = tokenize(line, tokens, sizeof(tokens) / sizeof(tokens[0]));
    if (count < 4 || strcmp(tokens[0], "setoption") != 0 || strcmp(tokens[1], "name") != 0) return;
    size_t value_index = 0;
    for (size_t index = 2; index < count; ++index) {
        if (strcmp(tokens[index], "value") == 0) {
            value_index = index + 1;
            break;
        }
    }
    if (value_index >= count) return;
    uint64_t value;
    if (strcmp(tokens[2], "Threads") == 0 && parse_unsigned(tokens[value_index], &value)) {
        if (value >= 1 && value <= 64) application->options.threads = (unsigned)value;
    } else if (strcmp(tokens[2], "Seed") == 0 && parse_unsigned(tokens[value_index], &value)) {
        if (value <= UINT32_MAX) {
            application->options.seed = value;
            application->options.seed_auto = value == 0;
        }
    } else if (strcmp(tokens[2], "MaxTreeNodes") == 0 && parse_unsigned(tokens[value_index], &value)) {
        if (value >= 1000 && value <= 10000000) application->options.max_tree_nodes = (size_t)value;
    } else if (strcmp(tokens[2], "RolloutDepth") == 0 && parse_unsigned(tokens[value_index], &value)) {
        if (value >= 1 && value <= 512) application->options.rollout_depth = (unsigned)value;
    } else if (strcmp(tokens[2], "UCTExploration") == 0 && parse_unsigned(tokens[value_index], &value)) {
        if (value >= 1 && value <= 3000) application->options.exploration_milli = (unsigned)value;
    } else if (strcmp(tokens[2], "MultiPV") == 0 && parse_unsigned(tokens[value_index], &value)) {
        if (value >= 1 && value <= SEARCH_MAX_MULTIPV) application->options.multi_pv = (unsigned)value;
    }
}

static bool selftest(void) {
    ShogiPosition position;
    shogi_position_start(&position);
    ShogiMove moves[SHOGI_MAX_MOVES];
    size_t count = shogi_generate_legal(&position, moves, SHOGI_MAX_MOVES);
    if (count == 30) {
        if (!shogi_parse_and_make_move(&position, "7g7f")) return false;
        char sfen[512];
        if (!shogi_position_to_sfen(&position, sfen, sizeof(sfen))) return false;
        return strcmp(sfen, "lnsgkgsnl/1r5b1/ppppppppp/9/9/2P6/PP1PPPPPP/1B5R1/LNSGKGSNL w - 2") == 0;
    }
    return false;
}

static void process_line(Application *application, char *line) {
    char command[32] = {0};
    if (sscanf(line, "%31s", command) != 1) return;
    if (strcmp(command, "quit") == 0) {
        finish_job(application, false);
        application->quit = true;
    } else if (strcmp(command, "stop") == 0) {
        finish_job(application, true);
    } else if (strcmp(command, "ponderhit") == 0) {
        (void)search_ponderhit(application->job);
    } else if (strcmp(command, "go") == 0) {
        finish_job(application, false);
        SearchLimits limits;
        if (!parse_go(line, &limits)) {
            puts("bestmove resign");
            fflush(stdout);
            return;
        }
        application->job = search_start(&application->position, &limits, &application->options);
        application->last_info_ns = monotonic_ns_main();
        if (application->job == NULL) {
            puts("bestmove resign");
            fflush(stdout);
        }
    } else if (strcmp(command, "usi") == 0) {
        finish_job(application, false);
        print_usi();
    } else if (strcmp(command, "isready") == 0) {
        finish_job(application, false);
        puts("readyok");
        fflush(stdout);
    } else if (strcmp(command, "setoption") == 0) {
        finish_job(application, false);
        set_option(application, line);
    } else if (strcmp(command, "usinewgame") == 0) {
        finish_job(application, false);
        shogi_position_start(&application->position);
    } else if (strcmp(command, "position") == 0) {
        finish_job(application, false);
        (void)set_position_command(application, line);
    } else if (strcmp(command, "d") == 0) {
        finish_job(application, false);
        shogi_print_position(&application->position);
        fflush(stdout);
    }
}

int main(int argc, char **argv) {
    shogi_init();
    if (argc > 1 && strcmp(argv[1], "--selftest") == 0) return selftest() ? 0 : 1;

    Application application;
    memset(&application, 0, sizeof(application));
    shogi_position_start(&application.position);
    application.options.threads = detected_threads();
    application.options.seed_auto = true;
    application.options.max_tree_nodes = 1000000;
    application.options.rollout_depth = SEARCH_DEFAULT_ROLLOUT_DEPTH;
    application.options.exploration_milli = SEARCH_DEFAULT_EXPLORATION_MILLI;
    application.options.multi_pv = SEARCH_DEFAULT_MULTIPV;

    char line[4096];
    bool input_eof = false;
    while (!application.quit) {
        if (application.job == NULL) {
            if (input_eof || fgets(line, sizeof(line), stdin) == NULL) break;
            process_line(&application, line);
            continue;
        }

        if (search_is_done(application.job)) {
            finish_job(&application, true);
            continue;
        }
        struct pollfd descriptor = {STDIN_FILENO, POLLIN | POLLHUP, 0};
        int status = input_eof ? poll(NULL, 0, 20) : poll(&descriptor, 1, 20);
        if (status < 0 && errno == EINTR) continue;
        if (status < 0) {
            finish_job(&application, true);
            break;
        }
        if (status > 0 && (descriptor.revents & (POLLIN | POLLHUP)) != 0) {
            if (fgets(line, sizeof(line), stdin) != NULL) {
                process_line(&application, line);
            } else {
                input_eof = true;
                if (search_waits_for_stop(application.job)) finish_job(&application, true);
            }
        }
        if (application.job != NULL) {
            uint64_t now = monotonic_ns_main();
            if (now - application.last_info_ns >= UINT64_C(250000000)) {
                print_search_info(&application);
                application.last_info_ns = now;
            }
        }
    }
    finish_job(&application, false);
    return 0;
}
