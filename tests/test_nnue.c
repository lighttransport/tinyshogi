#include "../src/nnue.h"

#include <stdio.h>
#include <string.h>

static int fail(const char *message) {
    fprintf(stderr, "nnue test failure: %s\n", message);
    return 1;
}

int main(void) {
    shogi_init();
    ShogiNnueModel model;
    shogi_nnue_model_init(&model);
    if (!shogi_nnue_model_init_default(&model, 8)) return fail("model init");
    for (size_t index = 0; index < (size_t)model.feature_count * model.hidden_dim; ++index)
        model.feature_weights[index] = (int16_t)((index % 7) - 3);
    for (size_t index = 0; index < (size_t)model.hidden_dim * 2U; ++index)
        model.output_weights[index] = (int16_t)((index % 5) - 2);

    ShogiPosition start;
    shogi_position_start(&start);
    uint32_t ids[128];
    if (shogi_nnue_feature_ids(&start, SHOGI_BLACK, ids, 128) == 0)
        return fail("feature extraction");
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
    (void)shogi_nnue_evaluate(&model, &first, SHOGI_BLACK);

    const char *path = "/tmp/tinyshogi-nnue-test.nnue";
    if (!shogi_nnue_model_save(&model, path)) return fail("model save");
    ShogiNnueModel loaded;
    shogi_nnue_model_init(&loaded);
    if (!shogi_nnue_model_load(&loaded, path)) return fail("model load");
    if (loaded.feature_count != model.feature_count || loaded.hidden_dim != model.hidden_dim)
        return fail("model metadata");
    remove(path);
    shogi_nnue_model_destroy(&loaded);
    shogi_nnue_accumulator_destroy(&first);
    shogi_nnue_accumulator_destroy(&rebuilt);
    shogi_nnue_model_destroy(&model);
    return 0;
}
