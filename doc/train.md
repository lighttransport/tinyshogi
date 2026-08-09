# TinyShogi training report

This report records the reproducible A64FX distributed-training experiments
performed on 2026-08-10. It compares Momentum SGD, Nesterov SGD, and the
experimental Muon hybrid optimizer on real, non-duplicated self-play positions.

## Dataset

A 12-node A64FX allocation generated 96 distinct games. Each rank played eight
disjoint game IDs, covering IDs `100000` through `100095`.

```text
simulations/move       2000
maximum plies          128
self-play threads      48 per node
leaf batch             12
seed                   20260810
generated records      10904
duplicate records      911
unique records         9993
```

After removing repeated opening records, the unique corpus contained 9,993
records. A deterministic 80/20 split produced 7,994 training records across 12
rank-local NDF1 shards and 1,999 held-out records. Held-out records were never
supplied to the trainer.

```text
runs/real-12n.ZurMTJ/unique.ndf1
runs/real-12n.ZurMTJ/train/rank-{0..11}.ndf1
runs/real-12n.ZurMTJ/heldout.ndf1
```

## Distributed configuration

Each MPI rank read its own shard. The trainer used one rank and 48 OpenMP
workers per A64FX node.

```text
MPI ranks               12
OpenMP threads/rank     48
global batch            2304
momentum                0.9
auxiliary learning rate 0.001
seed                    20260810
epochs                  1000 unless stated otherwise
```

The model is value-only NNUE3 with a 256-unit hidden layer and two 32x256
hidden matrices. Board-feature rows are assigned by perspective-king bucket;
replicated hand and dense gradients are synchronized with MPI collectives.

## Optimizer comparison

All optimizers used identical initialization, seed, shards, global batch, and
1,000 epochs.

| Optimizer | Wall time | Final train MSE | Held-out MSE | Final throughput |
|---|---:|---:|---:|---:|
| Momentum SGD | 46.55 s | 0.00990645 | 9,905.355 | 98.7k samples/s |
| Nesterov SGD | 46.92 s | 0.00990646 | 9,905.355 | 187.2k samples/s |
| Muon hybrid, matrix LR 0.01 | 55.63 s | 0.00061604 | 10,935.603 | 159.4k samples/s |

Muon reduced training loss much faster but generalized worse. It should not be
selected by training MSE alone. `eval_nnue` reports fixed-point outputs against
NDF1 values, so the absolute held-out MSE scale is less important than the
matched comparison.

## Muon learning-rate and early-stopping sweep

The auxiliary learning rate remained `0.001`; only the hidden-matrix rate
changed.

| Matrix LR | Held-out MSE after 1,000 epochs |
|---:|---:|
| 0.0025 | 10,555.343 |
| 0.0050 | 9,962.271 |
| 0.0075 | 10,134.044 |
| 0.0100 | 10,935.603 |

At matrix LR `0.005`, early stopping produced:

| Epochs | Held-out MSE |
|---:|---:|
| 100 | 9,909.750 |
| 300 | 10,014.342 |
| 600 | 10,532.301 |
| 1,000 | 9,962.271 |

The best Muon point is close to, but still slightly worse than, Momentum SGD.
The non-monotonic curve makes checkpointed early stopping essential.

Additional stabilization tests were run on the same split. Disabling Muon's
Nesterov look-ahead at matrix LR `0.005` produced held-out MSE `10,351.391`,
worse than the default Nesterov form. Gradient-norm clipping at `0.1`, `0.25`,
and `0.5` produced `9,962.271` in each case, identical to unclipped Muon;
the gradients did not reach those clip thresholds. The recommended Muon
configuration therefore remains Nesterov enabled, matrix LR `0.005`, and
held-out checkpoint selection around the 100-epoch point.

Warmup and decoupled weight decay were also tested at matrix LR `0.005`:

| Warmup steps | Weight decay | Held-out MSE |
|---:|---:|---:|
| 500 | 0.00 | 10,496.771 |
| 500 | 0.01 | 10,666.096 |
| 500 | 0.10 | 10,275.670 |

All three were worse than the unclipped, no-warmup baseline (`9,962.271`).
These controls remain available for future datasets but are disabled by
default; the current stable Muon baseline is Nesterov enabled, no clipping,
no warmup, no weight decay, and early checkpoint selection.

## Muon implementation and performance

The optimized Muon implementation includes:

- five-step quintic Newton-Schulz orthogonalization;
- separate ownership of the two side-dependent hidden matrices by MPI ranks;
- OpenMP-parallel normalization and matrix products;
- contiguous row-major FMA traversal for the `B x X` update;
- persistent temporary workspace instead of per-step allocation.

The 12-node 1,000-epoch smoke test improved from the initial 49.4k samples/s
to 137.6k samples/s. It completed in 16.15 seconds with final training MSE
`0.05914961` on the small fixture. This is an optimizer throughput
improvement, not a strength improvement.

## Checkpoint and resume

The trainer supports rank-local, atomic optimizer checkpoints:

```sh
build/train_nnue_mpi --data train.ndf1 --output candidate.nnue \
  --epochs 100 --checkpoint runs/state --checkpoint-epochs 10
```

Resume with the same rank count and model geometry:

```sh
build/train_nnue_mpi --data train.ndf1 --output candidate-resumed.nnue \
  --epochs 100 --resume runs/state
```

Each rank stores weights, optimizer velocities, lazy-momentum timestamps, Muon
state, epoch, and global step. Files are written as `.partial`, flushed and
fsynced, then atomically renamed. Six uninterrupted epochs were compared with
four epochs plus checkpoint/resume to epoch six; final NNUE3 files were
byte-identical across all 12 ranks: `PASS`.

## Reproduction

Build the native engine and trainer:

```sh
OUT_DIR=build-fcc-a64fx ./scripts/build_fcc_a64fx.sh
```

Deduplicate and split a merged corpus:

```sh
tools/dedupe_ndf.py --output unique.ndf1 data/rank-*.ndf1
tools/split_ndf.py unique.ndf1 --train-dir train \
  --heldout heldout.ndf1 --ranks 12
```

Run Muon with checkpointing:

```sh
mpiexec -n 12 build/train_nnue_mpi \
  --data train/rank-$PMIX_RANK.ndf1 --output muon.nnue \
  --epochs 1000 --global-batch 2304 --optimizer muon \
  --learning-rate 0.001 --muon-learning-rate 0.005 \
  --momentum 0.9 --checkpoint state --checkpoint-epochs 100
```

The stabilizer controls are also available for experiments:

```sh
--muon-nesterov 0|1 --muon-gradient-clip N
```

## Decision

Momentum SGD remains the current quality baseline. Nesterov has comparable
held-out quality. Muon is retained as an experimental option because it fits
training data rapidly and its A64FX implementation is substantially faster,
but it requires held-out checkpoint selection and further regularization before
it should replace Momentum SGD for production playing models.
