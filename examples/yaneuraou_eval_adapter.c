#define _POSIX_C_SOURCE 200809L

/*
 * TinyShogi evaluator plugin for a YaneuraOu NNUE process.
 *
 * This is deliberately a compatibility adapter, not an implementation of
 * YaneuraOu's private nn.bin format.  It keeps one YaneuraOu process alive,
 * sends it a position, and converts its USI score into TinyShogi's evaluator
 * ABI.  Set YANEURAOU_EVAL_ENGINE and YANEURAOU_EVAL_DIR before loading the
 * plugin; defaults are build/yaneuraou/YaneuraOu and its sibling eval dir.
 */

#include "eval.h"

#include <errno.h>
#include <fcntl.h>
#include <limits.h>
#include <pthread.h>
#include <signal.h>
#include <stdbool.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <poll.h>
#include <sys/types.h>
#include <sys/wait.h>
#include <unistd.h>

typedef struct {
    pid_t pid;
    int input;
    int output;
    pthread_mutex_t mutex;
    char engine[PATH_MAX];
    char eval_dir[PATH_MAX];
} YaneuraouAdapter;

static bool write_all(int fd, const char *text) {
    size_t left = strlen(text);
    while (left != 0) {
        ssize_t written = write(fd, text, left);
        if (written < 0 && errno == EINTR) continue;
        if (written <= 0) return false;
        text += written;
        left -= (size_t)written;
    }
    return true;
}

static bool read_line_timeout(int fd, char *line, size_t capacity) {
    size_t used = 0;
    while (used + 1 < capacity) {
        struct pollfd pollfd = {fd, POLLIN, 0};
        int ready;
        do {
            ready = poll(&pollfd, 1, 10000);
        } while (ready < 0 && errno == EINTR);
        if (ready <= 0) return false;
        char c;
        ssize_t count = read(fd, &c, 1);
        if (count == 0) return false;
        if (count < 0 && errno == EINTR) continue;
        if (count < 0) return false;
        if (c == '\n') {
            line[used] = '\0';
            return true;
        }
        if (c != '\r') line[used++] = c;
    }
    line[0] = '\0';
    return false;
}

static bool wait_for(YaneuraouAdapter *adapter, const char *needle) {
    char line[4096];
    while (read_line_timeout(adapter->output, line, sizeof(line))) {
        if (strcmp(line, needle) == 0) return true;
    }
    return false;
}

static bool start_engine(YaneuraouAdapter *adapter) {
    int to_child[2], from_child[2];
    if (pipe(to_child) != 0 || pipe(from_child) != 0) return false;
    pid_t pid = fork();
    if (pid < 0) return false;
    if (pid == 0) {
        dup2(to_child[0], STDIN_FILENO);
        dup2(from_child[1], STDOUT_FILENO);
        int nullfd = open("/dev/null", O_WRONLY);
        if (nullfd >= 0) dup2(nullfd, STDERR_FILENO);
        close(to_child[0]); close(to_child[1]);
        close(from_child[0]); close(from_child[1]);
        execl(adapter->engine, adapter->engine, (char *)NULL);
        _exit(127);
    }
    close(to_child[0]);
    close(from_child[1]);
    adapter->pid = pid;
    adapter->input = to_child[1];
    adapter->output = from_child[0];

    if (!write_all(adapter->input, "usi\n") || !wait_for(adapter, "usiok"))
        return false;
    if (adapter->eval_dir[0] != '\0') {
        char option[PATH_MAX + 64];
        snprintf(option, sizeof(option), "setoption name EvalDir value %s\n",
                 adapter->eval_dir);
        if (!write_all(adapter->input, option)) return false;
    }
    return write_all(adapter->input, "setoption name USI_Ponder value false\n") &&
           write_all(adapter->input, "isready\n") && wait_for(adapter, "readyok");
}

static void stop_engine(YaneuraouAdapter *adapter) {
    if (adapter->input >= 0) write_all(adapter->input, "quit\n");
    if (adapter->input >= 0) close(adapter->input);
    if (adapter->output >= 0) close(adapter->output);
    if (adapter->pid > 0) {
        int status;
        if (waitpid(adapter->pid, &status, 0) < 0 && errno == EINTR)
            (void)waitpid(adapter->pid, &status, 0);
    }
    adapter->pid = -1;
    adapter->input = -1;
    adapter->output = -1;
}

static void *create_adapter(const char *config) {
    (void)config;
    YaneuraouAdapter *adapter = calloc(1, sizeof(*adapter));
    if (adapter == NULL) return NULL;
    adapter->pid = -1; adapter->input = -1; adapter->output = -1;
    const char *engine = getenv("YANEURAOU_EVAL_ENGINE");
    const char *eval_dir = getenv("YANEURAOU_EVAL_DIR");
    snprintf(adapter->engine, sizeof(adapter->engine), "%s",
             engine == NULL ? "build/yaneuraou/YaneuraOu" : engine);
    snprintf(adapter->eval_dir, sizeof(adapter->eval_dir), "%s",
             eval_dir == NULL ? "build/yaneuraou/eval" : eval_dir);
    char nn_path[PATH_MAX];
    int nn_length = snprintf(nn_path, sizeof(nn_path), "%s/nn.bin", adapter->eval_dir);
    if (nn_length < 0 || (size_t)nn_length >= sizeof(nn_path) || access(nn_path, R_OK) != 0) {
        free(adapter);
        return NULL;
    }
    if (pthread_mutex_init(&adapter->mutex, NULL) != 0 || !start_engine(adapter)) {
        stop_engine(adapter);
        pthread_mutex_destroy(&adapter->mutex);
        free(adapter);
        return NULL;
    }
    return adapter;
}

static int evaluate(void *userdata, const ShogiPosition *position,
                    ShogiColor perspective) {
    YaneuraouAdapter *adapter = userdata;
    if (adapter == NULL || position == NULL) return 0;
    pthread_mutex_lock(&adapter->mutex);
    char sfen[512], command[600], line[4096];
    int score = 0;
    bool have_score = false;
    if (shogi_position_to_sfen(position, sfen, sizeof(sfen))) {
        snprintf(command, sizeof(command), "position sfen %s\ngo nodes 1\n", sfen);
        if (write_all(adapter->input, command)) {
            while (read_line_timeout(adapter->output, line, sizeof(line))) {
                char *marker = strstr(line, " score cp ");
                if (marker != NULL) { score = atoi(marker + 10); have_score = true; }
                if (strstr(line, " score mate ") != NULL) {
                    char *mate = strstr(line, " score mate ") + 12;
                    score = atoi(mate) >= 0 ? 1500 : -1500;
                    have_score = true;
                }
                if (strncmp(line, "bestmove ", 9) == 0) break;
            }
        }
    }
    pthread_mutex_unlock(&adapter->mutex);
    if (!have_score) return 0;
    return position->side == perspective ? score : -score;
}

static void destroy_adapter(void *userdata) {
    YaneuraouAdapter *adapter = userdata;
    if (adapter == NULL) return;
    pthread_mutex_lock(&adapter->mutex);
    stop_engine(adapter);
    pthread_mutex_unlock(&adapter->mutex);
    pthread_mutex_destroy(&adapter->mutex);
    free(adapter);
}

static const TinyShogiEvalPlugin plugin = {
    .abi_version = TINYSHOGI_EVAL_ABI_VERSION,
    .struct_size = sizeof(TinyShogiEvalPlugin),
    .name = "yaneuraou-nnue-usi-adapter",
    .create = create_adapter,
    .destroy = destroy_adapter,
    .evaluate = evaluate
};

const TinyShogiEvalPlugin *tinyshogi_eval_plugin(void) { return &plugin; }
