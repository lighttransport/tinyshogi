/* SPDX-License-Identifier: Apache-2.0 */
#ifndef TINYSHOGI_DL_FEATURES_H
#define TINYSHOGI_DL_FEATURES_H
#include "shogi.h"
#define SHOGI_DL_CHANNELS 80U
#define SHOGI_DL_PLANES 139U
#define SHOGI_DL_ACTIONS (81U * SHOGI_DL_PLANES)
#define SHOGI_DL_FEATURES (81U * SHOGI_DL_CHANNELS)
/* NHWC, canonical player-to-move orientation. No external engine mappings. */
void shogi_dl_encode(const ShogiPosition *, float features[SHOGI_DL_FEATURES]);
/* -1 for an unrepresentable move. The caller establishes legality separately. */
int shogi_dl_action(const ShogiPosition *, ShogiMove);
#endif
