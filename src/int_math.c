#include "int_math.h"

#include <limits.h>

#define INT_LN2_Q16 45426

static int32_t clamp_i32(int64_t value) {
    if (value > INT32_MAX) return INT32_MAX;
    if (value < 0) return 0;
    return (int32_t)value;
}

int32_t int_exp_q16(int32_t x) {
    if (x <= -16 * INT_LN2_Q16) return 0;
    if (x >= 15 * INT_LN2_Q16) return INT32_MAX;
    int32_t n = x / INT_LN2_Q16;
    int32_t remainder = x - n * INT_LN2_Q16;
    if (remainder < 0) { --n; remainder += INT_LN2_Q16; }
    int64_t r = remainder;
    int64_t r2 = (r * r) >> 16;
    int64_t r3 = (r2 * r) >> 16;
    int64_t r4 = (r3 * r) >> 16;
    int64_t series = INT_Q16_ONE + r + r2 / 2 + r3 / 6 + r4 / 24;
    if (n >= 0) {
        if (n > 14) return INT32_MAX;
        series <<= n;
    } else {
        series >>= -n;
    }
    return clamp_i32(series);
}

int32_t int_log_q16(int32_t x) {
    if (x <= 0) return INT32_MIN;
    int32_t value = x;
    int32_t exponent = 0;
    while (value >= 2 * INT_Q16_ONE) { value >>= 1; ++exponent; }
    while (value < INT_Q16_ONE) { value <<= 1; --exponent; }
    int64_t numerator = (int64_t)value - INT_Q16_ONE;
    int64_t denominator = (int64_t)value + INT_Q16_ONE;
    int64_t z = (numerator << 16) / denominator;
    int64_t z2 = (z * z) >> 16;
    int64_t term = z;
    int64_t series = term;
    term = (term * z2) >> 16; series += term / 3;
    term = (term * z2) >> 16; series += term / 5;
    term = (term * z2) >> 16; series += term / 7;
    term = (term * z2) >> 16; series += term / 9;
    int64_t result = 2 * series + (int64_t)exponent * INT_LN2_Q16;
    if (result > INT32_MAX) return INT32_MAX;
    if (result < INT32_MIN) return INT32_MIN;
    return (int32_t)result;
}

int32_t int_tanh_q16(int32_t x) {
    if (x >= 8 * INT_Q16_ONE) return INT_Q16_ONE;
    if (x <= -8 * INT_Q16_ONE) return -INT_Q16_ONE;
    int negative = x < 0;
    int64_t magnitude64 = negative ? -(int64_t)x : x;
    int32_t magnitude = (int32_t)magnitude64;
    int32_t e = int_exp_q16(-2 * magnitude);
    int64_t numerator = (int64_t)INT_Q16_ONE - e;
    int64_t denominator = (int64_t)INT_Q16_ONE + e;
    int32_t result = denominator == 0 ? INT_Q16_ONE : (int32_t)((numerator << 16) / denominator);
    return negative ? -result : result;
}

void int_softmax_q16(const int32_t *logits, int32_t *probabilities, size_t count) {
    if (logits == NULL || probabilities == NULL || count == 0) return;
    int32_t maximum = logits[0];
    for (size_t index = 1; index < count; ++index) if (logits[index] > maximum) maximum = logits[index];
    uint64_t total = 0;
    for (size_t index = 0; index < count; ++index) {
        int64_t difference = (int64_t)logits[index] - maximum;
        int32_t value = int_exp_q16(difference < INT32_MIN ? INT32_MIN :
                                    difference > INT32_MAX ? INT32_MAX : (int32_t)difference);
        probabilities[index] = value;
        total += (uint32_t)value;
    }
    if (total == 0) { for (size_t index = 0; index < count; ++index) probabilities[index] = 0; return; }
    for (size_t index = 0; index < count; ++index) {
        probabilities[index] = (int32_t)(((uint64_t)(uint32_t)probabilities[index] * INT_Q16_ONE) / total);
    }
}
