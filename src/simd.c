#include "simd.h"

#include <string.h>

static int32_t dot_i8_scalar(const int8_t *left, const int8_t *right, size_t count) {
    int32_t result = 0;
    for (size_t i = 0; i < count; ++i) result += (int32_t)left[i] * right[i];
    return result;
}

static int32_t dot_i16_i8_scalar(const int16_t *left, const int8_t *right, size_t count) {
    int32_t result = 0;
    for (size_t i = 0; i < count; ++i) result += (int32_t)left[i] * right[i];
    return result;
}

static int64_t dot_relu_i32_i16_scalar(const int32_t *left, const int16_t *right, size_t count) {
    int64_t result = 0;
    for (size_t i = 0; i < count; ++i)
        if (left[i] > 0) result += (int64_t)left[i] * right[i];
    return result;
}

static void add_i16_i32_scalar(int32_t *accumulator, const int16_t *weights,
                               size_t count, int sign) {
    for (size_t i = 0; i < count; ++i) accumulator[i] += sign * (int32_t)weights[i];
}

static void add_i16_i32_rows_scalar(int32_t *accumulator,
                                    const int16_t *const *rows,
                                    size_t row_count, size_t count, int sign) {
    for (size_t row = 0; row < row_count; ++row)
        add_i16_i32_scalar(accumulator, rows[row], count, sign);
}

static void add_f32_scalar(float *accumulator, const float *values, size_t count) {
    for (size_t i = 0; i < count; ++i) accumulator[i] += values[i];
}

#if defined(__aarch64__) && defined(__ARM_NEON)
#include <arm_neon.h>

static int32_t dot_i8_neon(const int8_t *left, const int8_t *right, size_t count) {
    int32x4_t sum = vdupq_n_s32(0);
    size_t i = 0;
    for (; i + 16 <= count; i += 16) {
        int8x16_t a = vld1q_s8(left + i), b = vld1q_s8(right + i);
        sum = vaddq_s32(sum, vpaddlq_s16(vmull_s8(vget_low_s8(a), vget_low_s8(b))));
        sum = vaddq_s32(sum, vpaddlq_s16(vmull_s8(vget_high_s8(a), vget_high_s8(b))));
    }
    int32_t lanes[4]; vst1q_s32(lanes, sum);
    int32_t result = lanes[0] + lanes[1] + lanes[2] + lanes[3];
    return result + dot_i8_scalar(left + i, right + i, count - i);
}

static int32_t dot_i16_i8_neon(const int16_t *left, const int8_t *right, size_t count) {
    int32x4_t sum = vdupq_n_s32(0);
    size_t i = 0;
    for (; i + 8 <= count; i += 8) {
        int16x8_t a = vld1q_s16(left + i);
        int16x8_t b = vmovl_s8(vld1_s8(right + i));
        sum = vaddq_s32(sum, vpaddlq_s16(vmulq_s16(a, b)));
    }
    int32_t lanes[4]; vst1q_s32(lanes, sum);
    int32_t result = lanes[0] + lanes[1] + lanes[2] + lanes[3];
    return result + dot_i16_i8_scalar(left + i, right + i, count - i);
}

static void add_i16_i32_neon(int32_t *accumulator, const int16_t *weights,
                             size_t count, int sign) {
    int16x8_t direction = vdupq_n_s16((int16_t)sign);
    size_t i = 0;
    for (; i + 8 <= count; i += 8) {
        int16x8_t w = vmulq_s16(vld1q_s16(weights + i), direction);
        int32x4_t lo = vaddq_s32(vld1q_s32(accumulator + i), vmovl_s16(vget_low_s16(w)));
        int32x4_t hi = vaddq_s32(vld1q_s32(accumulator + i + 4), vmovl_s16(vget_high_s16(w)));
        vst1q_s32(accumulator + i, lo); vst1q_s32(accumulator + i + 4, hi);
    }
    add_i16_i32_scalar(accumulator + i, weights + i, count - i, sign);
}

static void add_f32_neon(float *accumulator, const float *values, size_t count) {
    size_t i = 0;
    for (; i + 4 <= count; i += 4)
        vst1q_f32(accumulator + i, vaddq_f32(vld1q_f32(accumulator + i), vld1q_f32(values + i)));
    add_f32_scalar(accumulator + i, values + i, count - i);
}
#endif

#if defined(__aarch64__) && defined(__ARM_FEATURE_SVE)
#include <arm_sve.h>
extern int64_t tinyshogi_nnue_dot_relu_i32_i16_sve_4way(const int32_t *,
                                                         const int16_t *, size_t);
extern void tinyshogi_nnue_add_i16_i32_rows_sve(int32_t *, const int16_t *const *,
                                                size_t, size_t, int);
extern void tinyshogi_nnue_add_i16_i32_rows_sve_2way(int32_t *, const int16_t *const *,
                                                      size_t, size_t, int);
extern void tinyshogi_nnue_add_i16_i32_rows_sve_4way(int32_t *, const int16_t *const *,
                                                      size_t, size_t, int);
extern void tinyshogi_nnue_add_i16_i32_rows_sve_4row(int32_t *, const int16_t *const *,
                                                      size_t, size_t, int);
extern void tinyshogi_nnue_add_i16_i32_rows_sve_4exact(int32_t *, const int16_t *const *,
                                                        size_t, size_t, int);
extern void tinyshogi_nnue_add_i16_i32_one_sve(int32_t *, const int16_t *, size_t, int);

static int32_t dot_i8_sve(const int8_t *left, const int8_t *right, size_t count) {
    svint32_t sum0 = svdup_s32(0), sum1 = svdup_s32(0);
    svint32_t sum2 = svdup_s32(0), sum3 = svdup_s32(0);
    svint32_t sum4 = svdup_s32(0), sum5 = svdup_s32(0);
    svint32_t sum6 = svdup_s32(0), sum7 = svdup_s32(0);
    size_t i = 0;
    const size_t lanes = svcntb();
    svbool_t full = svptrue_b8();
    for (; i + 8 * lanes <= count; i += 8 * lanes) {
#define DOT_I8_STEP(N) \
        do { \
            sum##N = svdot_s32(sum##N, svld1_s8(full, left + i + (N) * lanes), \
                               svld1_s8(full, right + i + (N) * lanes)); \
        } while (0)
        DOT_I8_STEP(0); DOT_I8_STEP(1); DOT_I8_STEP(2); DOT_I8_STEP(3);
        DOT_I8_STEP(4); DOT_I8_STEP(5); DOT_I8_STEP(6); DOT_I8_STEP(7);
#undef DOT_I8_STEP
    }
    for (; i + 4 * lanes <= count; i += 4 * lanes) {
        sum0 = svdot_s32(sum0, svld1_s8(full, left + i),
                         svld1_s8(full, right + i));
        sum1 = svdot_s32(sum1, svld1_s8(full, left + i + lanes),
                         svld1_s8(full, right + i + lanes));
        sum2 = svdot_s32(sum2, svld1_s8(full, left + i + 2 * lanes),
                         svld1_s8(full, right + i + 2 * lanes));
        sum3 = svdot_s32(sum3, svld1_s8(full, left + i + 3 * lanes),
                         svld1_s8(full, right + i + 3 * lanes));
    }
    if (i < count) {
        svbool_t pg = svwhilelt_b8(i, count);
        sum0 = svdot_s32(sum0, svld1_s8(pg, left + i),
                         svld1_s8(pg, right + i));
    }
    svint32_t total = svadd_s32_x(svptrue_b32(), sum0, sum1);
    total = svadd_s32_x(svptrue_b32(), total, sum2);
    total = svadd_s32_x(svptrue_b32(), total, sum3);
    total = svadd_s32_x(svptrue_b32(), total, sum4);
    total = svadd_s32_x(svptrue_b32(), total, sum5);
    total = svadd_s32_x(svptrue_b32(), total, sum6);
    total = svadd_s32_x(svptrue_b32(), total, sum7);
    return svaddv_s32(svptrue_b32(), total);
}

/* A64FX has SVE1, so use widening loads and 32-bit multiplies rather than
 * SVE2-only integer dot/widening multiply-long instructions. */
static int32_t dot_i16_i8_sve(const int16_t *left, const int8_t *right, size_t count) {
    svbool_t all32 = svptrue_b32();
    svbool_t all16 = svptrue_b16(), all8 = svptrue_b8();
    svint32_t sum_lo0 = svdup_s32(0), sum_hi0 = svdup_s32(0);
    svint32_t sum_lo1 = svdup_s32(0), sum_hi1 = svdup_s32(0);
    svint32_t sum_lo2 = svdup_s32(0), sum_hi2 = svdup_s32(0);
    svint32_t sum_lo3 = svdup_s32(0), sum_hi3 = svdup_s32(0);
    svint32_t sum_lo4 = svdup_s32(0), sum_hi4 = svdup_s32(0);
    svint32_t sum_lo5 = svdup_s32(0), sum_hi5 = svdup_s32(0);
    svint32_t sum_lo6 = svdup_s32(0), sum_hi6 = svdup_s32(0);
    svint32_t sum_lo7 = svdup_s32(0), sum_hi7 = svdup_s32(0);
    size_t i = 0;
    const size_t chunk = svcnth();
    for (; i + 8 * chunk <= count; i += 8 * chunk) {
#define DOT_I16_I8_STEP(N) \
        do { \
            svint16_t a##N = svld1_s16(all16, left + i + (N) * chunk); \
            svint16_t b##N = svunpklo_s16(svld1_s8(all8, right + i + (N) * chunk)); \
            sum_lo##N = svadd_s32_x(all32, sum_lo##N, \
                svmul_s32_x(all32, svunpklo_s32(a##N), svunpklo_s32(b##N))); \
            sum_hi##N = svadd_s32_x(all32, sum_hi##N, \
                svmul_s32_x(all32, svunpkhi_s32(a##N), svunpkhi_s32(b##N))); \
        } while (0)
        DOT_I16_I8_STEP(0); DOT_I16_I8_STEP(1);
        DOT_I16_I8_STEP(2); DOT_I16_I8_STEP(3);
        DOT_I16_I8_STEP(4); DOT_I16_I8_STEP(5);
        DOT_I16_I8_STEP(6); DOT_I16_I8_STEP(7);
#undef DOT_I16_I8_STEP
    }
    for (; i + 4 * chunk <= count; i += 4 * chunk) {
#define DOT_I16_I8_STEP(N) \
        do { \
            svint16_t a##N = svld1_s16(all16, left + i + (N) * chunk); \
            svint16_t b##N = svunpklo_s16(svld1_s8(all8, right + i + (N) * chunk)); \
            sum_lo##N = svadd_s32_x(all32, sum_lo##N, \
                svmul_s32_x(all32, svunpklo_s32(a##N), svunpklo_s32(b##N))); \
            sum_hi##N = svadd_s32_x(all32, sum_hi##N, \
                svmul_s32_x(all32, svunpkhi_s32(a##N), svunpkhi_s32(b##N))); \
        } while (0)
        DOT_I16_I8_STEP(0); DOT_I16_I8_STEP(1);
        DOT_I16_I8_STEP(2); DOT_I16_I8_STEP(3);
#undef DOT_I16_I8_STEP
    }
    svint32_t total_lo = svadd_s32_x(all32, sum_lo0, sum_lo1);
    total_lo = svadd_s32_x(all32, total_lo, sum_lo2);
    total_lo = svadd_s32_x(all32, total_lo, sum_lo3);
    total_lo = svadd_s32_x(all32, total_lo, sum_lo4);
    total_lo = svadd_s32_x(all32, total_lo, sum_lo5);
    total_lo = svadd_s32_x(all32, total_lo, sum_lo6);
    total_lo = svadd_s32_x(all32, total_lo, sum_lo7);
    svint32_t total_hi = svadd_s32_x(all32, sum_hi0, sum_hi1);
    total_hi = svadd_s32_x(all32, total_hi, sum_hi2);
    total_hi = svadd_s32_x(all32, total_hi, sum_hi3);
    total_hi = svadd_s32_x(all32, total_hi, sum_hi4);
    total_hi = svadd_s32_x(all32, total_hi, sum_hi5);
    total_hi = svadd_s32_x(all32, total_hi, sum_hi6);
    total_hi = svadd_s32_x(all32, total_hi, sum_hi7);
    return svaddv_s32(all32, total_lo) + svaddv_s32(all32, total_hi) +
           dot_i16_i8_scalar(left + i, right + i, count - i);
}

static int64_t dot_relu_i32_i16_sve(const int32_t *left, const int16_t *right, size_t count) {
    svbool_t all64 = svptrue_b64();
    svbool_t all32 = svptrue_b32(), all16 = svptrue_b16();
    svint64_t sum0 = svdup_s64(0), sum1 = svdup_s64(0);
    svint64_t sum2 = svdup_s64(0), sum3 = svdup_s64(0);
    size_t i = 0;
    const size_t chunk = svcntw();
    for (; i + 4 * chunk <= count; i += 4 * chunk) {
#define DOT_RELU_STEP(N) \
        do { \
            svint16_t b##N = svld1_s16(all16, right + i + (N) * chunk); \
            svint32_t a##N = svmax_s32_x(all32, \
                svld1_s32(all32, left + i + (N) * chunk), svdup_s32(0)); \
            svint32_t p##N = svmul_s32_x(all32, a##N, svunpklo_s32(b##N)); \
            sum##N = svadd_s64_x(all64, sum##N, svunpklo_s64(p##N)); \
            sum##N = svadd_s64_x(all64, sum##N, svunpkhi_s64(p##N)); \
        } while (0)
        DOT_RELU_STEP(0); DOT_RELU_STEP(1);
        DOT_RELU_STEP(2); DOT_RELU_STEP(3);
#undef DOT_RELU_STEP
    }
    return svaddv_s64(all64, sum0) + svaddv_s64(all64, sum1) +
           svaddv_s64(all64, sum2) + svaddv_s64(all64, sum3) +
           dot_relu_i32_i16_scalar(left + i, right + i, count - i);
}

static void add_i16_i32_sve(int32_t *accumulator, const int16_t *weights,
                            size_t count, int sign) {
    size_t i = 0;
    while (i < count) {
        /* svunpklo_s32 expands the lower half of the 16-bit vector to
         * svcntw() 32-bit lanes, so advance by the full word-lane count. */
        size_t lanes = svcntw();
        svbool_t pg16 = svwhilelt_b16(i, count);
        svbool_t pg32 = svwhilelt_b32(i, count);
        svint32_t a = svld1_s32(pg32, accumulator + i);
        svint32_t w = svunpklo_s32(svld1_s16(pg16, weights + i));
        a = sign > 0 ? svadd_s32_m(pg32, a, w) : svsub_s32_m(pg32, a, w);
        svst1_s32(pg32, accumulator + i, a);
        i += lanes;
    }
}

static void add_i16_i32_rows_sve(int32_t *accumulator,
                                 const int16_t *const *rows,
                                 size_t row_count, size_t count, int sign) {
    if (row_count == 0) return;
    svbool_t all32 = svptrue_b32();
    size_t i = 0;
    while (i < count) {
        svbool_t pg32 = svwhilelt_b32(i, count);
        svbool_t pg16 = svwhilelt_b16(i, count);
        svint32_t a = svld1_s32(pg32, accumulator + i);
        for (size_t row = 0; row < row_count; ++row) {
            svint32_t w = svunpklo_s32(svld1_s16(pg16, rows[row] + i));
            a = sign > 0 ? svadd_s32_m(pg32, a, w) : svsub_s32_m(pg32, a, w);
        }
        svst1_s32(pg32, accumulator + i, a);
        i += svcntw();
    }
}

static void add_f32_sve(float *accumulator, const float *values, size_t count) {
    size_t i = 0;
    while (i < count) {
        svbool_t pg = svwhilelt_b32(i, count);
        svst1_f32(pg, accumulator + i,
                  svadd_f32_m(pg, svld1_f32(pg, accumulator + i), svld1_f32(pg, values + i)));
        i += svcntw();
    }
}
#endif

const char *tinyshogi_simd_backend(void) {
#if defined(__aarch64__) && defined(__ARM_FEATURE_SVE)
    return "arm64-sve";
#elif defined(__aarch64__) && defined(__ARM_NEON)
    return "arm64-neon";
#elif defined(__x86_64__) || defined(__i386__)
    return "x86";
#else
    return "scalar";
#endif
}

int32_t tinyshogi_dot_i8_i8(const int8_t *left, const int8_t *right, size_t count) {
#if defined(__aarch64__) && defined(__ARM_FEATURE_SVE)
    return dot_i8_sve(left, right, count);
#elif defined(__aarch64__) && defined(__ARM_NEON)
    return dot_i8_neon(left, right, count);
#else
    return dot_i8_scalar(left, right, count);
#endif
}

int32_t tinyshogi_dot_i16_i8(const int16_t *left, const int8_t *right, size_t count) {
#if defined(__aarch64__) && defined(__ARM_FEATURE_SVE)
    return dot_i16_i8_sve(left, right, count);
#elif defined(__aarch64__) && defined(__ARM_NEON)
    return dot_i16_i8_neon(left, right, count);
#else
    return dot_i16_i8_scalar(left, right, count);
#endif
}

int64_t tinyshogi_dot_relu_i32_i16(const int32_t *left, const int16_t *right, size_t count) {
#if defined(__aarch64__) && defined(__ARM_FEATURE_SVE)
    if (svcntw() == 16 && (count & 63U) == 0U)
        return tinyshogi_nnue_dot_relu_i32_i16_sve_4way(left, right, count);
    return dot_relu_i32_i16_sve(left, right, count);
#else
    return dot_relu_i32_i16_scalar(left, right, count);
#endif
}

void tinyshogi_add_i16_i32(int32_t *accumulator, const int16_t *weights,
                           size_t count, int sign) {
#if defined(__aarch64__) && defined(__ARM_FEATURE_SVE)
    add_i16_i32_sve(accumulator, weights, count, sign);
#elif defined(__aarch64__) && defined(__ARM_NEON)
    add_i16_i32_neon(accumulator, weights, count, sign);
#else
    add_i16_i32_scalar(accumulator, weights, count, sign);
#endif
}

void tinyshogi_add_i16_i32_rows(int32_t *accumulator,
                                const int16_t *const *rows,
                                size_t row_count, size_t count, int sign) {
    if (accumulator == NULL || rows == NULL || row_count == 0 || count == 0) return;
#if defined(__aarch64__) && defined(__ARM_FEATURE_SVE)
    if (row_count == 1U) {
        if (svcntw() == 16U && (count & 63U) == 0U && count >= 64U) {
            tinyshogi_nnue_add_i16_i32_one_sve(accumulator, rows[0], count, sign);
            return;
        }
        tinyshogi_add_i16_i32(accumulator, rows[0], count, sign);
        return;
    }
    if (row_count == 2U && svcntw() == 16U && (count & 63U) == 0U && count >= 64U) {
        tinyshogi_nnue_add_i16_i32_rows_sve_2way(accumulator, rows, row_count, count, sign);
        return;
    }
    if (row_count == 4U && svcntw() == 16U && (count & 63U) == 0U && count >= 64U) {
        tinyshogi_nnue_add_i16_i32_rows_sve_4exact(accumulator, rows, row_count, count, sign);
        return;
    }
    if (row_count >= 4U && row_count <= 8U && svcntw() == 16U &&
        (count & 63U) == 0U && count >= 64U) {
        tinyshogi_nnue_add_i16_i32_rows_sve_4row(accumulator, rows, row_count, count, sign);
        return;
    }
    /* The four-bank schedule wins as soon as it has a second row to hide
     * behind the first accumulator update.  Keep the one-row case on the
     * lower-overhead single-bank SVE loop. */
    if (svcntw() == 16 && (count & 63U) == 0U && count >= 128U && row_count >= 4U) {
        tinyshogi_nnue_add_i16_i32_rows_sve_4way(accumulator, rows, row_count, count, sign);
        return;
    }
    if (svcntw() == 16 && (count & 63U) == 0U) {
        tinyshogi_nnue_add_i16_i32_rows_sve(accumulator, rows, row_count, count, sign);
        return;
    }
    add_i16_i32_rows_sve(accumulator, rows, row_count, count, sign);
#elif defined(__aarch64__) && defined(__ARM_NEON)
    for (size_t row = 0; row < row_count; ++row)
        add_i16_i32_neon(accumulator, rows[row], count, sign);
#else
    add_i16_i32_rows_scalar(accumulator, rows, row_count, count, sign);
#endif
}

void tinyshogi_add_f32(float *accumulator, const float *values, size_t count) {
#if defined(__aarch64__) && defined(__ARM_FEATURE_SVE)
    add_f32_sve(accumulator, values, count);
#elif defined(__aarch64__) && defined(__ARM_NEON)
    add_f32_neon(accumulator, values, count);
#else
    add_f32_scalar(accumulator, values, count);
#endif
}
