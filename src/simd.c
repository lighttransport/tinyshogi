#include "simd.h"

#include <string.h>

#if defined(__GNUC__) || defined(__FUJITSU)
#define TS_MAYBE_UNUSED __attribute__((unused))
#else
#define TS_MAYBE_UNUSED
#endif

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

static TS_MAYBE_UNUSED void add_i16_i32_rows_scalar(
    int32_t *accumulator, const int16_t *const *rows,
    size_t row_count, size_t count, int sign) {
    for (size_t row = 0; row < row_count; ++row)
        add_i16_i32_scalar(accumulator, rows[row], count, sign);
}

static TS_MAYBE_UNUSED void add_f32_scalar(float *accumulator,
                                           const float *values, size_t count) {
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
extern int64_t tinyshogi_nnue_dot_relu_i32_i16_sve_sdot(const int32_t *,
                                                         const int16_t *, size_t);
extern int64_t tinyshogi_nnue_dot_clip_i32_i16_sve_sdot(const int32_t *,
                                                         const int16_t *, size_t,
                                                         int32_t);
extern int64_t tinyshogi_dot_i16_i16_sve_sdot(const int16_t *, const int16_t *, size_t);
extern void tinyshogi_dot_i16_i16_4_sve_sdot(const int16_t *, const int16_t *,
                                             size_t, size_t, int64_t *);
extern void tinyshogi_dot_i16_i16_8_sve_sdot(const int16_t *, const int16_t *,
                                             size_t, size_t, int64_t *);
extern void tinyshogi_dot_i16_i16_batch8_sve_sdot(const int16_t *, size_t,
                                                  const int16_t *, size_t,
                                                  int64_t *);
extern void tinyshogi_dot_i8_i8_8_sve_sdot(const int8_t *, const int8_t *,
                                           size_t, size_t, int32_t *);
extern void tinyshogi_a64fx_sdot_gemm_6x4(size_t, const int8_t *, const int8_t *,
                                         int32_t *, size_t);
extern void tinyshogi_a64fx_sdot_gemm_64x6(size_t, const int8_t *, const int8_t *,
                                           int32_t *, size_t);
extern void tinyshogi_a64fx_sdot_gemm_4x5(size_t, const int8_t *, const int8_t *,
                                          int32_t *, size_t);
extern void tinyshogi_a64fx_sdot_gemm_6x4_i16(size_t, const int16_t *, const int16_t *,
                                             int64_t *, size_t);
extern void tinyshogi_a64fx_sdot_gemm_5x4_i16(size_t, const int16_t *, const int16_t *,
                                             int64_t *, size_t);
extern void tinyshogi_a64fx_sdot_gemm_4x5_i16(size_t, const int16_t *, const int16_t *,
                                             int64_t *, size_t);
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
#if defined(__FUJITSU)
    /* FCC 4.x exposes A64FX's SDOT instruction to assembly but its bundled
     * SVE ACLE does not declare svdot_s32.  The throughput-sensitive 8-output
     * and GEMM paths below already dispatch to hand-written SDOT kernels. */
    return dot_i8_scalar(left, right, count);
#else
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
#endif
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

void tinyshogi_dot_i8_i8_8(const int8_t *left, const int8_t *weights,
                           size_t stride, size_t count, int32_t out[8]) {
#if defined(__aarch64__) && defined(__ARM_FEATURE_SVE)
    if (svcntw() == 16 && count >= 256U && (count & 255U) == 0U) {
        tinyshogi_dot_i8_i8_8_sve_sdot(left, weights, stride, count, out);
        return;
    }
#endif
    for (unsigned lane = 0; lane < 8; ++lane)
        out[lane] = dot_i8_scalar(left, weights + (size_t)lane * stride, count);
}

void tinyshogi_gemm_i8_6x64(size_t count, const int8_t *a, const int8_t *b,
                            int32_t *c, size_t ldc) {
    if (a == NULL || b == NULL || c == NULL || count == 0 || (count & 3U) != 0 || ldc < 64) return;
#if defined(__aarch64__) && defined(__ARM_FEATURE_SVE)
    if (svcntw() == 16U) {
        tinyshogi_a64fx_sdot_gemm_6x4(count, a, b, c, ldc);
        return;
    }
#endif
    for (size_t row = 0; row < 6; ++row) {
        for (size_t col = 0; col < 64; ++col) {
            int32_t sum = 0;
            for (size_t k = 0; k < count; ++k) {
                size_t block = k >> 2, lane = k & 3U;
                sum += (int32_t)a[block * 24U + row * 4U + lane] *
                       (int32_t)b[block * 256U + col * 4U + lane];
            }
            c[row * ldc + col] = sum;
        }
    }
}

void tinyshogi_gemm_i8_64x6(size_t count, const int8_t *weights,
                            const int8_t *positions, int32_t *output,
                            size_t output_stride) {
    if (weights == NULL || positions == NULL || output == NULL || count == 0 ||
        (count & 3U) != 0U || output_stride < 64U) return;
#if defined(__aarch64__) && defined(__ARM_FEATURE_SVE)
    if (svcntw() == 16U) {
        tinyshogi_a64fx_sdot_gemm_64x6(count, weights, positions, output,
                                       output_stride);
        return;
    }
#endif
    for (size_t position = 0; position < 6U; ++position)
        for (size_t unit = 0; unit < 64U; ++unit) {
            int32_t sum = 0;
            for (size_t k = 0; k < count; ++k) {
                size_t block = k >> 2, lane = k & 3U;
                sum += (int32_t)weights[block * 256U + unit * 4U + lane] *
                       (int32_t)positions[block * 24U + position * 4U + lane];
            }
            output[position * output_stride + unit] = sum;
        }
}

void tinyshogi_gemm_i8_64x5(size_t count, const int8_t *weights,
                            const int8_t *positions, int32_t *output,
                            size_t output_stride) {
    if (weights == NULL || positions == NULL || output == NULL || count == 0 ||
        (count & 3U) != 0U || output_stride < 64U) return;
#if defined(__aarch64__) && defined(__ARM_FEATURE_SVE)
    if (svcntw() == 16U) {
        tinyshogi_a64fx_sdot_gemm_4x5(count, weights, positions, output,
                                      output_stride);
        return;
    }
#endif
    for (size_t position = 0; position < 5U; ++position)
        for (size_t unit = 0; unit < 64U; ++unit) {
            int32_t sum = 0;
            for (size_t k = 0; k < count; ++k) {
                size_t block = k >> 2, lane = k & 3U;
                sum += (int32_t)weights[block * 256U + unit * 4U + lane] *
                       (int32_t)positions[block * 20U + position * 4U + lane];
            }
            output[position * output_stride + unit] = sum;
        }
}

void tinyshogi_gemm_i16_6x32(size_t count, const int16_t *a, const int16_t *b,
                             int64_t *c, size_t ldc) {
    if (a == NULL || b == NULL || c == NULL || count == 0 || (count & 3U) != 0 || ldc < 32) return;
#if defined(__aarch64__) && defined(__ARM_FEATURE_SVE)
    if (svcntw() == 16U) {
        tinyshogi_a64fx_sdot_gemm_6x4_i16(count, a, b, c, ldc);
        return;
    }
#endif
    for (size_t row = 0; row < 6; ++row) {
        for (size_t col = 0; col < 32; ++col) {
            int64_t sum = 0;
            for (size_t k = 0; k < count; ++k) {
                size_t block = k >> 2, lane = k & 3U;
                sum += (int64_t)a[block * 24U + row * 4U + lane] *
                       (int64_t)b[block * 128U + col * 4U + lane];
            }
            c[row * ldc + col] = sum;
        }
    }
}

void tinyshogi_nnue_head_gemm_i16_32x5(size_t count, const int16_t *weights,
                                       const int16_t *positions, int64_t *output) {
    if (weights == NULL || positions == NULL || output == NULL || count != 256U) return;
#if defined(__aarch64__) && defined(__ARM_FEATURE_SVE)
#if defined(__FUJITSU)
    /* FCC's A64FX target is fixed at VL=512; avoid an ACLE VL query in the
     * hottest NNUE path (some FCC runtime environments report it late). */
    tinyshogi_a64fx_sdot_gemm_5x4_i16(count, positions, weights, output, 32U);
    return;
#else
    if (svcntw() == 16U) {
        tinyshogi_a64fx_sdot_gemm_5x4_i16(count, positions, weights, output, 32U);
        return;
    }
#endif
#endif
#if !defined(__aarch64__) || !defined(__ARM_FEATURE_SVE) || !defined(__FUJITSU)
    for (size_t position = 0; position < 5U; ++position)
        for (size_t head = 0; head < 32U; ++head) {
            int64_t sum = 0;
            for (size_t unit = 0; unit < count; ++unit) {
                size_t block = unit >> 2U, lane = unit & 3U;
                size_t vector = head >> 3U, vector_lane = head & 7U;
                sum += (int64_t)weights[block * 128U + vector * 32U + vector_lane * 4U + lane] *
                       positions[block * 20U + position * 4U + lane];
            }
            output[position * 32U + head] = sum;
        }
#endif
}

void tinyshogi_nnue_head_gemm_i16_6x32(size_t count, const int16_t *weights,
                                       const int16_t *positions, int64_t *output) {
    if (count != 256U || weights == NULL || positions == NULL || output == NULL)
        return;
    /* The NNUE3 packed weight layout is the 6x32 kernel's B layout; positions
     * are packed as six groups of four values for each K step. */
    tinyshogi_gemm_i16_6x32(count, positions, weights, output, 32U);
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

int64_t tinyshogi_dot_i16_i16(const int16_t *left, const int16_t *right, size_t count) {
#if defined(__aarch64__) && defined(__ARM_FEATURE_SVE)
    if (svcntw() == 16 && count >= 256U && (count & 255U) == 0U)
        return tinyshogi_dot_i16_i16_sve_sdot(left, right, count);
#endif
    int64_t result = 0;
    for (size_t i = 0; i < count; ++i)
        result += (int64_t)left[i] * (int64_t)right[i];
    return result;
}

void tinyshogi_dot_i16_i16_4(const int16_t *left, const int16_t *weights,
                             size_t stride, size_t count, int64_t out[4]) {
#if defined(__aarch64__) && defined(__ARM_FEATURE_SVE)
    if (svcntw() == 16 && count >= 256U && (count & 255U) == 0U) {
        tinyshogi_dot_i16_i16_4_sve_sdot(left, weights, stride, count, out);
        return;
    }
#endif
    for (unsigned action = 0; action < 4; ++action) {
        int64_t sum = 0;
        const int16_t *row = weights + action * stride;
        for (size_t i = 0; i < count; ++i) sum += (int64_t)left[i] * row[i];
        out[action] = sum;
    }
}

void tinyshogi_dot_i16_i16_8(const int16_t *left, const int16_t *weights,
                             size_t stride, size_t count, int64_t out[8]) {
#if defined(__aarch64__) && defined(__ARM_FEATURE_SVE)
    if (svcntw() == 16 && count >= 256U && (count & 255U) == 0U) {
        tinyshogi_dot_i16_i16_8_sve_sdot(left, weights, stride, count, out);
        return;
    }
#endif
    for (unsigned action = 0; action < 8; ++action) {
        int64_t sum = 0;
        const int16_t *row = weights + action * stride;
        for (size_t i = 0; i < count; ++i) sum += (int64_t)left[i] * row[i];
        out[action] = sum;
    }
}

void tinyshogi_dot_i16_i16_batch8(const int16_t *positions, size_t stride,
                                  const int16_t *weights, size_t count,
                                  int64_t out[8]) {
    if (positions == NULL || weights == NULL || out == NULL || stride < count ||
        count == 0) return;
#if defined(__aarch64__) && defined(__ARM_FEATURE_SVE)
    if (svcntw() == 16 && count >= 256U && (count & 31U) == 0U) {
        tinyshogi_dot_i16_i16_batch8_sve_sdot(positions, stride, weights, count, out);
        return;
    }
#endif
    for (unsigned position = 0; position < 8; ++position)
        out[position] = tinyshogi_dot_i16_i16(positions + (size_t)position * stride,
                                              weights, count);
}

int64_t tinyshogi_dot_relu_i32_i16(const int32_t *left, const int16_t *right, size_t count) {
#if defined(__aarch64__) && defined(__ARM_FEATURE_SVE)
    if (svcntw() == 16 && count >= 1024U && (count & 255U) == 0U) {
        int sdot_safe = 1;
        for (size_t i = 0; i < count; ++i)
            if (left[i] > INT16_MAX) { sdot_safe = 0; break; }
        if (sdot_safe)
            return tinyshogi_nnue_dot_relu_i32_i16_sve_sdot(left, right, count);
    }
    if (svcntw() == 16 && (count & 63U) == 0U)
        return tinyshogi_nnue_dot_relu_i32_i16_sve_4way(left, right, count);
    return dot_relu_i32_i16_sve(left, right, count);
#else
    return dot_relu_i32_i16_scalar(left, right, count);
#endif
}

int64_t tinyshogi_dot_clip_i32_i16(const int32_t *left, const int16_t *right,
                                   size_t count, int32_t clip) {
    if (left == NULL || right == NULL || clip <= 0) return 0;
#if defined(__aarch64__) && defined(__ARM_FEATURE_SVE)
    if (svcntw() == 16 && count >= 256U && (count & 255U) == 0U && clip <= INT16_MAX)
        return tinyshogi_nnue_dot_clip_i32_i16_sve_sdot(left, right, count, clip);
#endif
    int64_t result = 0;
    for (size_t i = 0; i < count; ++i) {
        int32_t activation = left[i];
        if (activation < 0) activation = 0;
        if (activation > clip) activation = clip;
        result += (int64_t)activation * right[i];
    }
    return result;
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
