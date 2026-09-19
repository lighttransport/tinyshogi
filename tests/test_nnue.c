#include "../src/nnue.h"

#include <math.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

static int fail(const char *message) {
    fprintf(stderr, "nnue test failure: %s\n", message);
    return 1;
}

static int check_state_move(const ShogiNnueModel *model, const char *sfen,
                            const char *move_text, ShogiColor perspective) {
    ShogiPosition position;
    ShogiMove move;
    if (!shogi_position_from_sfen(&position, sfen) ||
        !shogi_parse_usi_move(move_text, &move)) return fail("state case parse");
    ShogiNnueState state;
    ShogiNnueDelta delta;
    ShogiNnueAccumulator rebuilt;
    if (!shogi_nnue_state_init(&state, model, perspective) ||
        !shogi_nnue_state_reset(&state, &position) ||
        !shogi_nnue_accumulator_init(&rebuilt, model->hidden_dim))
        return fail("state case init");
    int32_t *before = malloc(model->hidden_dim * sizeof(*before));
    if (before == NULL) return fail("state case allocation");
    memcpy(before, state.sum, model->hidden_dim * sizeof(*before));
    ShogiUndo undo;
    if (!shogi_make_move_undo(&position, move, &undo) ||
        !shogi_nnue_state_apply_move(&state, &position, &undo, &delta) ||
        !shogi_nnue_accumulator_build(model, &position, &rebuilt) ||
        memcmp(state.sum, rebuilt.sum[perspective],
               model->hidden_dim * sizeof(*state.sum)) != 0)
        return fail("state case forward mismatch");
    if (!shogi_unmake_move(&position, &undo) ||
        !shogi_nnue_state_unapply_move(&state, &position, &delta) ||
        memcmp(state.sum, before, model->hidden_dim * sizeof(*state.sum)) != 0)
        return fail("state case reverse mismatch");
    free(before);
    shogi_nnue_accumulator_destroy(&rebuilt);
    shogi_nnue_state_destroy(&state);
    return 0;
}

int main(void) {
    shogi_init();
    ShogiNnueModel model;
    shogi_nnue_model_init(&model);
    if (!shogi_nnue_model_init_default(&model, 64)) return fail("model init");
    for (size_t index = 0; index < (size_t)model.feature_count * model.hidden_dim; ++index)
        model.feature_weights[index] = (int16_t)((index % 7) - 3);
    for (size_t index = 0; index < (size_t)model.hidden_dim * 2U; ++index)
        model.output_weights[index] = (int16_t)((index % 5) - 2);
    if (check_state_move(&model,
            "4k4/9/4P4/9/9/9/9/9/4K4 b - 1", "5c5b+", SHOGI_BLACK) ||
        check_state_move(&model,
            "4k4/9/4p4/4P4/9/9/9/9/4K4 b - 1", "5d5c", SHOGI_BLACK) ||
        check_state_move(&model,
            "4k4/9/9/9/9/9/9/9/4K4 b P 1", "P*5e", SHOGI_BLACK) ||
        check_state_move(&model,
            "4k4/9/9/9/9/9/9/9/4K4 b - 1", "5i5h", SHOGI_BLACK) ||
        check_state_move(&model,
            "4k4/9/9/9/9/9/9/9/4K4 b - 1", "5i5h", SHOGI_WHITE))
        return 1;

    ShogiPosition start;
    shogi_position_start(&start);
    uint32_t ids[128];
    if (shogi_nnue_feature_ids(&start, SHOGI_BLACK, ids, 128) == 0)
        return fail("feature extraction");
    if (shogi_nnue_feature_ids(&start, (ShogiColor)-1, ids, 128) != 0 ||
        shogi_nnue_state_init(&(ShogiNnueState){0}, &model, (ShogiColor)-1) ||
        shogi_nnue_evaluate_position(&model, &start, (ShogiColor)-1) != 0)
        return fail("invalid perspective rejection");
    ShogiPosition malformed = start;
    malformed.board[0] = 0xffU;
    if (shogi_nnue_feature_ids(&malformed, SHOGI_BLACK, ids, 128) != 0)
        return fail("malformed feature rejection");
    ShogiNnueAccumulator first, rebuilt;
    if (!shogi_nnue_accumulator_init(&first, model.hidden_dim) ||
        !shogi_nnue_accumulator_init(&rebuilt, model.hidden_dim) ||
        !shogi_nnue_accumulator_build(&model, &start, &first)) return fail("accumulator build");

    ShogiMove moves[SHOGI_MAX_MOVES];
    size_t count = shogi_generate_legal(&start, moves, SHOGI_MAX_MOVES);
    if (count == 0) return fail("legal moves");
    ShogiPosition next = start;
    if (!shogi_make_move(&next, moves[0]) ||
        !shogi_nnue_accumulator_update(&model, &start, &next, &first) ||
        !shogi_nnue_accumulator_build(&model, &next, &rebuilt)) return fail("accumulator update");
    if (memcmp(first.sum[0], rebuilt.sum[0], model.hidden_dim * sizeof(int32_t)) != 0 ||
        memcmp(first.sum[1], rebuilt.sum[1], model.hidden_dim * sizeof(int32_t)) != 0)
        return fail("incremental accumulator mismatch");
    ShogiNnueState state;
    ShogiNnueDelta delta;
    if (!shogi_nnue_state_init(&state, &model, SHOGI_BLACK) ||
        !shogi_nnue_state_reset(&state, &start)) return fail("state init");
    ShogiPosition state_position = start;
    ShogiUndo state_undo;
    if (!shogi_make_move_undo(&state_position, moves[0], &state_undo) ||
        !shogi_nnue_state_apply_move(&state, &state_position, &state_undo, &delta) ||
        memcmp(state.sum, rebuilt.sum[SHOGI_BLACK], model.hidden_dim * sizeof(int32_t)) != 0)
        return fail("move-synchronous state mismatch");
    if (!shogi_unmake_move(&state_position, &state_undo) ||
        !shogi_nnue_state_unapply_move(&state, &state_position, &delta))
        return fail("state undo operation");
    ShogiNnueAccumulator start_rebuilt;
    if (!shogi_nnue_accumulator_init(&start_rebuilt, model.hidden_dim) ||
        !shogi_nnue_accumulator_build(&model, &start, &start_rebuilt) ||
        memcmp(state.sum, start_rebuilt.sum[SHOGI_BLACK], model.hidden_dim * sizeof(int32_t)) != 0)
        return fail("state undo mismatch");
    int expected_black = shogi_nnue_evaluate(&model, &rebuilt, SHOGI_BLACK);
    int expected_white = shogi_nnue_evaluate(&model, &rebuilt, SHOGI_WHITE);
    /* Prime the thread-local cache with the parent, then exercise the
     * move-local feature-row update on the child. */
    (void)shogi_nnue_evaluate_position(&model, &start, SHOGI_BLACK);
    if (shogi_nnue_evaluate_position(&model, &next, SHOGI_BLACK) != expected_black ||
        shogi_nnue_evaluate_position(&model, &next, SHOGI_WHITE) != expected_white ||
        shogi_nnue_evaluate_position(&model, &next, SHOGI_BLACK) != expected_black)
        return fail("position evaluation cache mismatch");

    const char *path = "/tmp/tinyshogi-nnue-test.nnue";
    if (!shogi_nnue_model_save(&model, path)) return fail("model save");
    ShogiNnueModel loaded;
    shogi_nnue_model_init(&loaded);
    if (!shogi_nnue_model_load(&loaded, path)) return fail("model load");
    if (loaded.feature_count != model.feature_count || loaded.hidden_dim != model.hidden_dim)
        return fail("model metadata");
    shogi_nnue_model_destroy(&loaded);

    model.format_version = SHOGI_NNUE2_FORMAT_VERSION;
    model.activation_clip = 7;
    if (!shogi_nnue_model_save(&model, path)) return fail("NNUE2 model save");
    shogi_nnue_model_init(&loaded);
    if (!shogi_nnue_model_load(&loaded, path)) return fail("NNUE2 model load");
    if (loaded.format_version != SHOGI_NNUE2_FORMAT_VERSION ||
        loaded.activation_clip != model.activation_clip)
        return fail("NNUE2 metadata");
    if (!shogi_nnue_accumulator_build(&loaded, &next, &rebuilt))
        return fail("NNUE2 accumulator build");
    int64_t raw = (int64_t)loaded.output_bias * loaded.feature_scale;
    const int16_t *black_weights = loaded.output_weights;
    for (size_t i = 0; i < loaded.hidden_dim; ++i) {
        int32_t activation = rebuilt.sum[SHOGI_BLACK][i];
        if (activation < 0) activation = 0;
        if (activation > loaded.activation_clip) activation = loaded.activation_clip;
        raw += (int64_t)activation * black_weights[i];
    }
    double normalized = (double)raw /
        ((double)loaded.feature_scale * loaded.output_scale);
    if (shogi_nnue_evaluate(&loaded, &rebuilt, SHOGI_BLACK) !=
        (int)(tanh(normalized) * 1000.0))
        return fail("NNUE2 clipped evaluation");
    remove(path);
    shogi_nnue_model_destroy(&loaded);

    model.format_version = SHOGI_NNUE3_FORMAT_VERSION;
    model.head_dim = 4;
    model.head_clip = 31;
    model.head_shift = 8;
    model.head_weights = calloc((size_t)2U * model.head_dim * model.hidden_dim,
                                sizeof(*model.head_weights));
    model.head_bias = calloc((size_t)2U * model.head_dim, sizeof(*model.head_bias));
    model.final_weights = calloc((size_t)2U * model.head_dim,
                                 sizeof(*model.final_weights));
    model.final_bias = calloc(2U, sizeof(*model.final_bias));
    if (model.head_weights == NULL || model.head_bias == NULL ||
        model.final_weights == NULL || model.final_bias == NULL)
        return fail("NNUE3 allocation");
    for (size_t i = 0; i < (size_t)2U * model.head_dim * model.hidden_dim; ++i)
        model.head_weights[i] = (int16_t)((int)(i % 5U) - 2);
    for (size_t i = 0; i < (size_t)2U * model.head_dim; ++i)
        model.final_weights[i] = (int16_t)((int)(i % 7U) - 3);
    model.final_bias[0] = 11;
    model.final_bias[1] = -7;
    if (!shogi_nnue_model_save(&model, path)) return fail("NNUE3 model save");
    shogi_nnue_model_init(&loaded);
    if (!shogi_nnue_model_load(&loaded, path) ||
        loaded.format_version != SHOGI_NNUE3_FORMAT_VERSION ||
        loaded.head_dim != model.head_dim || loaded.head_clip != model.head_clip)
        return fail("NNUE3 model load");
    if (!shogi_nnue_accumulator_build(&loaded, &next, &rebuilt))
        return fail("NNUE3 accumulator build");
    ShogiNnueState v3_state;
    if (!shogi_nnue_state_init(&v3_state, &loaded, SHOGI_BLACK) ||
        !shogi_nnue_state_reset(&v3_state, &next) ||
        shogi_nnue_state_evaluate(&v3_state) !=
        shogi_nnue_evaluate(&loaded, &rebuilt, SHOGI_BLACK))
        return fail("NNUE3 state evaluation");
    shogi_nnue_state_destroy(&v3_state);
    remove(path);
    shogi_nnue_model_destroy(&loaded);
    shogi_nnue_accumulator_destroy(&first);
    shogi_nnue_accumulator_destroy(&rebuilt);
    shogi_nnue_accumulator_destroy(&start_rebuilt);
    shogi_nnue_state_destroy(&state);
    shogi_nnue_model_destroy(&model);
    return 0;
}
