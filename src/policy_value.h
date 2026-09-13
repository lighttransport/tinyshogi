/* SPDX-License-Identifier: Apache-2.0 */
#ifndef TINYSHOGI_POLICY_VALUE_H
#define TINYSHOGI_POLICY_VALUE_H
#include "shogi.h"
/* Outputs raw logits in the supplied legal-move order, and W,D,L probabilities
 * from each position's player-to-move perspective. Thread-safe callback;
 * implementations may combine concurrent requests into a device batch. */
typedef struct {
    void *userdata;
    bool (*evaluate_batch)(void *, const ShogiPosition *const *, const ShogiMove *const *,
                           const size_t *, size_t, float *const *, float *);
} ShogiPolicyValueEvaluator;
#endif
