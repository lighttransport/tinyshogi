#ifndef TINYSHOGI_INT_MATH_H
#define TINYSHOGI_INT_MATH_H

#include <stddef.h>
#include <stdint.h>

#define INT_Q16_ONE 65536

int32_t int_exp_q16(int32_t x);
int32_t int_log_q16(int32_t x);
int32_t int_tanh_q16(int32_t x);
void int_softmax_q16(const int32_t *logits, int32_t *probabilities, size_t count);

#endif
