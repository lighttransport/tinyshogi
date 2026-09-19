#include "../src/shogi.h"
#include "../src/search.h"
#include "../src/nnue.h"

#include <emscripten/heap.h>
#include <stddef.h>

/* A deliberately small, single-position API for the browser demo. */
static ShogiPosition position;
#define WEB_MAX_UNDO 512
static ShogiUndo undo_stack[WEB_MAX_UNDO];
static size_t undo_count;
static ShogiMove redo_stack[WEB_MAX_UNDO];
static size_t redo_count;
static uint64_t engine_last_nodes;
static int engine_last_score;
static unsigned engine_last_depth;
static uint64_t engine_last_time_ms;
static uint64_t engine_last_nps;
static char root_sfen[512];
static ShogiMove cached_legal_moves[SHOGI_MAX_MOVES];
static size_t cached_legal_move_count;
static bool cached_legal_moves_valid;
#ifndef TINYSHOGI_WEB_HASH_BYTES
#define TINYSHOGI_WEB_HASH_BYTES (64U * 1024U)
#endif
/* Keep the alpha-beta transposition table alive across moves.  Emscripten's
 * growing heap does not return a freed 64 MiB table to the browser, so
 * allocating the native default for every engine move eventually exhausts
 * the worker's WASM memory. */
static SearchContext *web_search_context;

static void web_invalidate_legal_moves(void) {
    cached_legal_moves_valid = false;
    cached_legal_move_count = 0;
}

static size_t web_prepare_legal_moves(void) {
    if (!cached_legal_moves_valid) {
        cached_legal_move_count = shogi_generate_legal(
            &position, cached_legal_moves, SHOGI_MAX_MOVES);
        cached_legal_moves_valid = true;
    }
    return cached_legal_move_count;
}

static void web_clear_history(void) {
    undo_count = 0;
    redo_count = 0;
}

static void web_capture_root_sfen(void) {
    if (!shogi_position_to_sfen(&position, root_sfen, sizeof(root_sfen))) root_sfen[0] = '\0';
}

void web_reset(void) {
    shogi_position_start(&position);
    web_invalidate_legal_moves();
    web_clear_history();
    web_capture_root_sfen();
    if (web_search_context != NULL) search_context_clear(web_search_context);
    engine_last_nodes = 0;
    engine_last_score = 0;
    engine_last_depth = 0;
    engine_last_time_ms = 0;
    engine_last_nps = 0;
}

/* Black pieces are positive, white pieces are negative, and empty is zero. */
int web_piece_at(int square) {
    if (square < 0 || square >= SHOGI_SQUARES) return 0;
    uint8_t piece = position.board[square];
    if (piece == SHOGI_EMPTY) return 0;
    int type = (int)shogi_piece_type(piece);
    return shogi_piece_color(piece) == SHOGI_BLACK ? type : -type;
}

int web_side_to_move(void) {
    return (int)position.side;
}

int web_hand_count(int color, int hand_index) {
    if (color < 0 || color > 1 || hand_index < 0 || hand_index >= 7) return 0;
    return (int)position.hand[color][hand_index];
}

int web_legal_move_count(void) {
    return (int)web_prepare_legal_moves();
}

static bool web_get_move(int index, ShogiMove *move) {
    if (move == NULL || index < 0 || index >= SHOGI_MAX_MOVES) return false;
    size_t count = web_prepare_legal_moves();
    if ((size_t)index >= count) return false;
    *move = cached_legal_moves[index];
    return true;
}

int web_move_from(int index) {
    ShogiMove move;
    return web_get_move(index, &move) ? (int)move.from : SHOGI_SQ_NONE;
}

int web_move_to(int index) {
    ShogiMove move;
    return web_get_move(index, &move) ? (int)move.to : SHOGI_SQ_NONE;
}

int web_move_promotes(int index) {
    ShogiMove move;
    return web_get_move(index, &move) ? (int)move.promote : 0;
}

int web_move_drop(int index) {
    ShogiMove move;
    return web_get_move(index, &move) ? (int)move.drop : 0;
}

int web_play_move(int index) {
    ShogiMove move;
    if (!web_get_move(index, &move) || undo_count >= WEB_MAX_UNDO ||
        !shogi_make_move_undo(&position, move, &undo_stack[undo_count])) return 0;
    ++undo_count;
    redo_count = 0;
    web_invalidate_legal_moves();
    return 1;
}

int web_play_usi(const char *text) {
    ShogiMove wanted;
    if (text == NULL || !shogi_parse_usi_move(text, &wanted)) return 0;
    ShogiMove move;
    for (int index = 0; index < SHOGI_MAX_MOVES; ++index) {
        if (!web_get_move(index, &move)) break;
        if (move.from == wanted.from && move.to == wanted.to &&
            move.promote == wanted.promote && move.drop == wanted.drop) {
            return web_play_move(index);
        }
    }
    return 0;
}

int web_can_undo(void) { return undo_count != 0; }
int web_can_redo(void) { return redo_count != 0; }

int web_history_count(void) { return (int)undo_count; }

const char *web_history_move(int index) {
    static char move_text[16];
    if (index < 0 || (size_t)index >= undo_count ||
        !shogi_move_to_usi(undo_stack[index].move, move_text, sizeof(move_text))) return "";
    return move_text;
}

/* The timeline includes the current line and moves available through redo.
 * redo_stack is a LIFO stack, so its next move is at redo_count - 1. */
int web_timeline_count(void) { return (int)(undo_count + redo_count); }

const char *web_timeline_move(int index) {
    static char move_text[16];
    ShogiMove move;
    if (index < 0 || (size_t)index >= undo_count + redo_count) return "";
    if ((size_t)index < undo_count) move = undo_stack[index].move;
    else move = redo_stack[redo_count - 1U - ((size_t)index - undo_count)];
    return shogi_move_to_usi(move, move_text, sizeof(move_text)) ? move_text : "";
}

int web_undo(void) {
    if (undo_count == 0) return 0;
    ShogiUndo *undo = &undo_stack[undo_count - 1];
    if (!shogi_unmake_move(&position, undo)) return 0;
    if (redo_count < WEB_MAX_UNDO) redo_stack[redo_count++] = undo->move;
    --undo_count;
    web_invalidate_legal_moves();
    return 1;
}

int web_redo(void) {
    if (redo_count == 0 || undo_count >= WEB_MAX_UNDO) return 0;
    ShogiMove move = redo_stack[--redo_count];
    if (!shogi_make_move_undo(&position, move, &undo_stack[undo_count])) {
        ++redo_count;
        return 0;
    }
    ++undo_count;
    web_invalidate_legal_moves();
    return 1;
}

const char *web_get_sfen(void) {
    static char sfen[512];
    return shogi_position_to_sfen(&position, sfen, sizeof(sfen)) ? sfen : "";
}

const char *web_get_root_sfen(void) { return root_sfen; }

int web_set_sfen(const char *sfen) {
    ShogiPosition next;
    if (sfen == NULL || !shogi_position_from_sfen(&next, sfen)) return 0;
    position = next;
    web_invalidate_legal_moves();
    web_clear_history();
    web_capture_root_sfen();
    if (web_search_context != NULL) search_context_clear(web_search_context);
    return 1;
}

const char *web_engine_move(unsigned nodes) {
    static char move_text[16];
    if (web_search_context == NULL) {
        web_search_context = search_context_create();
        if (web_search_context == NULL) return "";
    }
    SearchLimits limits = {0};
    SearchOptions options = {
        .mode = SEARCH_MODE_ALPHABETA,
        .threads = 1,
        .seed = 1,
        .max_tree_nodes = 50000,
        .rollout_depth = 64,
        .quiescence_depth = SEARCH_DEFAULT_QUIESCENCE_DEPTH,
        .exploration_milli = SEARCH_DEFAULT_EXPLORATION_MILLI,
        .multi_pv = 1,
        /* The browser's bounded searches do not need the native 64 MiB table.
         * Prefer a lower linear-memory high-water mark over cache hits, and
         * reuse the allocation through web_search_context. */
        .hash_bytes = TINYSHOGI_WEB_HASH_BYTES,
        .context = web_search_context
    };
    limits.nodes = nodes == 0 ? 64 : nodes > 2000000U ? 2000000U : nodes;
    SearchJob *job = search_start(&position, &limits, &options);
    if (job == NULL) return "";
    SearchResult result;
    search_join(job, &result);
    SearchProgress progress = {0};
    (void)search_get_progress(job, &progress);
    engine_last_nodes = progress.nodes;
    engine_last_score = progress.score_cp;
    engine_last_depth = (unsigned)progress.depth;
    engine_last_time_ms = progress.time_ms;
    engine_last_nps = progress.nps;
    bool ok = result.has_move && shogi_move_to_usi(result.move, move_text, sizeof(move_text));
    if (ok) ok = web_play_usi(move_text);
    search_destroy(job);
    return ok ? move_text : "";
}

unsigned web_engine_last_nodes(void) { return (unsigned)engine_last_nodes; }
int web_engine_last_score(void) { return engine_last_score; }
unsigned web_engine_last_depth(void) { return engine_last_depth; }
unsigned web_engine_last_time_ms(void) { return (unsigned)engine_last_time_ms; }
unsigned web_engine_last_nps(void) { return (unsigned)engine_last_nps; }

int web_game_result(void) {
    return (int)shogi_game_result(&position);
}

/* Keep the model in JavaScript, where it can be uploaded to WebGPU.  These
 * small accessors expose the engine's canonical sparse feature encoding, so
 * the browser evaluator and native NNUE always agree about a position. */
int web_nnue_feature_count(int perspective) {
    uint32_t features[SHOGI_SQUARES + 14];
    if (perspective < SHOGI_BLACK || perspective > SHOGI_WHITE) return 0;
    return (int)shogi_nnue_feature_ids(&position, (ShogiColor)perspective,
                                       features, sizeof(features) / sizeof(features[0]));
}

unsigned web_nnue_feature_id(int perspective, int index) {
    uint32_t features[SHOGI_SQUARES + 14];
    if (perspective < SHOGI_BLACK || perspective > SHOGI_WHITE || index < 0)
        return 0;
    size_t count = shogi_nnue_feature_ids(&position, (ShogiColor)perspective,
                                          features, sizeof(features) / sizeof(features[0]));
    return (size_t)index < count ? features[index] : 0;
}

static size_t web_nnue_move_features(int move_index, int perspective,
                                     uint32_t *features, size_t capacity) {
    ShogiMove move;
    ShogiPosition next;
    if (perspective < SHOGI_BLACK || perspective > SHOGI_WHITE ||
        !web_get_move(move_index, &move)) return 0;
    next = position;
    if (!shogi_make_move(&next, move)) return 0;
    return shogi_nnue_feature_ids(&next, (ShogiColor)perspective, features, capacity);
}

int web_nnue_move_feature_count(int move_index, int perspective) {
    uint32_t features[SHOGI_SQUARES + 14];
    return (int)web_nnue_move_features(move_index, perspective, features,
                                       sizeof(features) / sizeof(features[0]));
}

unsigned web_nnue_move_feature_id(int move_index, int perspective, int feature_index) {
    uint32_t features[SHOGI_SQUARES + 14];
    size_t count;
    if (feature_index < 0) return 0;
    count = web_nnue_move_features(move_index, perspective, features,
                                   sizeof(features) / sizeof(features[0]));
    return (size_t)feature_index < count ? features[feature_index] : 0;
}

void web_init(void) {
    shogi_init();
    web_reset();
}

unsigned web_memory_bytes(void) {
    return (unsigned)emscripten_get_heap_size();
}
