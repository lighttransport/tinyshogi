#ifndef TINYSHOGI_A64FX_UCT_H
#define TINYSHOGI_A64FX_UCT_H

#include <stdbool.h>
#include <stddef.h>

size_t tinyshogi_a64fx_uct_argmax(const float *mean, const float *inv_sqrt,
                                  size_t count, float exploration_scale,
                                  bool maximizing);

#endif
