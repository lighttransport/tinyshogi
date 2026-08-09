#include "a64fx_uct.h"

#include <arm_sve.h>
#include <float.h>
#include <stdint.h>

size_t tinyshogi_a64fx_uct_argmax(const float *mean, const float *inv_sqrt,
                                  size_t count, float exploration_scale,
                                  bool maximizing) {
    if (mean == NULL || inv_sqrt == NULL || count == 0) return SIZE_MAX;
    const size_t lanes = svcntw();
    if (lanes > 16U) return SIZE_MAX;
    svfloat32_t one = svdup_n_f32(1.0f);
    svfloat32_t scale = svdup_n_f32(exploration_scale);
    float best_score = -FLT_MAX;
    size_t best_index = SIZE_MAX;
    for (size_t base = 0; base < count; base += lanes) {
        svbool_t active = svwhilelt_b32((uint64_t)base, (uint64_t)count);
        svfloat32_t value = svld1_f32(active, mean + base);
        if (!maximizing) value = svsub_f32_x(active, one, value);
        svfloat32_t inverse = svld1_f32(active, inv_sqrt + base);
        value = svmla_f32_x(active, value, inverse, scale);
        float block_best = svmaxv_f32(active, value);
        if (block_best <= best_score) continue;
        svbool_t equal = svcmpeq_n_f32(active, value, block_best);
        svbool_t before = svbrkb_z(active, equal);
        size_t lane = svcntp_b32(active, before);
        best_score = block_best;
        best_index = base + lane;
    }
    return best_index;
}
