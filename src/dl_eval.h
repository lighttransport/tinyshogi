/* SPDX-License-Identifier: Apache-2.0 */
#ifndef TINYSHOGI_DL_EVAL_H
#define TINYSHOGI_DL_EVAL_H
#include "policy_value.h"
typedef struct ShogiDlModel ShogiDlModel;
ShogiDlModel *shogi_dl_open(const char *path, const char *backend, int device, unsigned batch);
void shogi_dl_close(ShogiDlModel *);
const ShogiPolicyValueEvaluator *shogi_dl_evaluator(ShogiDlModel *);
const char *shogi_dl_error(const ShogiDlModel *);
#endif
