# TinyShogi technical overview

This document describes TinyShogi's engine architecture, neural evaluation,
A64FX optimizations, measured performance, and training workflow. Measurements
are snapshots from the native A64FX work described in the repository; they are
performance results, not claims about playing strength.

## 1. Project overview

TinyShogi is a clean-room C11 engine for standard 9x9 shogi. It provides:

- complete legal move generation, make/unmake, checks, mate, promotion, drops,
  nifu, dead-rank restrictions, and uchifuzume;
- fourfold repetition and the configured 27-point entering-king declaration;
- USI operation, deterministic fixed-node searches, self-play, and match tools;
- Monte Carlo Tree Search (MCTS) and alpha-beta/PVS search modes;
- scalar, AVX2, Arm NEON, and A64FX SVE evaluation backends;
- integer TSM3 and HalfKP-style NNUE evaluators;
- direct NDF1 training-data output and CPU, GPU, and distributed CPU trainers.

The normal engine has no mandatory third-party runtime dependency. The A64FX
MPI trainer additionally requires MPI and OpenMP.

## 2. Engine structure

The main components are:

| Area | Main files | Responsibility |
|---|---|---|
| Rules and position | `src/shogi.c`, `src/shogi.h` | Board representation, legal moves, attacks, make/unmake, SFEN |
| Search | `src/search.c`, `src/search.h` | MCTS, neural leaf batching, rollout search, alpha-beta/PVS |
| Evaluation API | `src/eval.c`, `src/eval.h` | Built-in and plugin evaluator abstraction |
| NNUE | `src/nnue.c`, `src/nnue.h` | Model I/O, features, accumulators, incremental updates, batched heads |
| SIMD dispatch | `src/simd.c`, `src/simd.h` | Portable and architecture-specific kernels |
| A64FX assembly | `src/a64fx_*.S` | SVE SDOT/GEMM and accumulator kernels |
| USI/self-play | `src/main.c` | Protocol frontend and JSONL/NDF1 generation |
| Distributed training | `cpu/train_nnue_mpi.c` | Exact synchronous MPI/OpenMP NNUE3 training |

### Position and rules hot path

Search uses mutable make/unmake instead of copying a complete position for
every generated child. Target-centered attack detection reduces unnecessary
board scans. The measured rules benchmark fell from 540.0 million cycles and
393.7 million instructions to 420.8 million cycles and 286.6 million
instructions after these changes.

Rule correctness must remain the first optimization gate. A faster generator
that mishandles drops, checks, repetition, or entering-king declaration is not
a valid engine optimization.

## 3. Search design

MCTS is the default search. Alpha-beta/PVS can be selected through USI with:

```text
setoption name SearchMode value alphabeta
```

### Worker-local MCTS

The optimized neural path gives each worker its own tree, NNUE accumulator,
evaluation cache, and scratch state. Workers publish root visit/value totals,
but avoid locks on interior tree operations. This removes shared-tree and
shared-evaluator-cache contention at 48 cores.

Workers are pinned across the four A64FX core-memory groups (CMGs). On a normal
48-core allocation, the first workers are distributed over CMGs instead of
filling one CMG before moving to the next. This improves aggregate HBM and
cache behavior while preserving ordinary ordinal pinning on smaller systems.

### Neural leaf batching

One worker claims several simulations, descends several independent lanes,
then evaluates the leaves as a small matrix tile. The relevant operating points
are:

- `LeafBatch 5`: play-throughput default; maps to the 5-position x 32-head tile;
- `LeafBatch 6`: one complete 6-position x 32-head tile;
- `LeafBatch 12`: two 6-position tiles for throughput-oriented self-play.

Batch 12 amortizes lane setup, root restoration, and weight traffic, but it can
reduce search diversity and increase decision latency. It is therefore a data
generation setting, not automatically the strongest playing setting.

After each simulation, a neural lane restores its root accumulator with one
1 KiB copy instead of replaying every sparse delta in reverse. Worker-local
trees persist between searches, and only the active repetition-history prefix
is cloned.

## 4. NNUE3 evaluation

The current native value model is a HalfKP-style NNUE with:

- perspective-king feature buckets;
- a 256-element accumulator/hidden layer;
- clipped activation;
- two side-dependent 32-unit hidden heads;
- a side-dependent scalar value output;
- fixed-point inference in the engine.

Normal moves update sparse feature rows incrementally. Captures, promotions,
hand changes, and drops update both board and hand features. A king move changes
the perspective bucket and requires rebuilding that perspective accumulator;
the batched search has a small worker-local cache for repeated rebuilds.

NNUE3 stores packed head weights for the A64FX batched kernels. Inference uses
INT16 dot products with INT64 accumulators to avoid overflow and preserve exact
integer behavior.

## 5. Why batching is essential on A64FX

A single 256-element NNUE output dot has too little independent work. It issues
only a handful of SDOT operations and also pays clipping, packing, loading, and
horizontal-reduction costs. Consequently, its efficiency cannot approach the
dense arithmetic peak.

Batching positions converts the head into a small GEMM-like operation:

```text
             K = 256 hidden activations
          +--------------------------------+
positions | activation rows                |
          +--------------------------------+
                         x
          +--------------------------------+
heads     | packed 32 x 256 head weights   |
          +--------------------------------+
                         =
          +--------------------------------+
          | position x 32 head outputs     |
          +--------------------------------+
```

The 5x32 and 6x32 kernels keep many independent accumulators live. This hides
SDOT latency, reuses weights across positions, and remains inside A64FX's useful
short-loop/decode window.

## 6. A64FX-specific optimization

### Architecture assumptions

The native configuration assumes:

- 48 compute cores divided into four 12-core CMGs;
- 512-bit SVE vectors;
- high-bandwidth memory local to the CMGs;
- two relevant SDOT forms in this work: INT8 accumulation and an INT16-input,
  INT64-accumulation formulation;
- a nominal 2.0 GHz benchmark frequency unless stated otherwise.

At 2.0 GHz, counting multiply and add as two operations:

- INT8 SDOT peak: 512 GOPS/core;
- INT16 SDOT to INT64 peak: 256 GOPS/core.

At 2.2 GHz these become 563.2 and 281.6 GOPS/core respectively.

### Kernel techniques

The hand-written SVE kernels use:

- packed K-major weight layouts;
- 20 or 24 independent accumulators for latency hiding;
- explicit register-renaming schedules derived with the Clair A64FX model;
- multi-step software pipelines for the FLA/FLB execution resources;
- delayed horizontal reduction because 512-bit `UADDV` is expensive;
- loop bodies sized for the A64FX short-loop/decode behavior;
- exact scalar/SIMD cross-checks before performance measurements.

FCC's Clang frontend builds C11-atomic search code, while the classic frontend
with `-KSVE` builds SVE code. The resulting objects are ABI-compatible and are
linked with the assembly kernels by `scripts/build_fcc_a64fx.sh`.

## 7. Measured A64FX performance

### Arithmetic kernels

These are single-core, steady-state measurements at 2.0 GHz:

| Kernel | Measured | Peak | Efficiency |
|---|---:|---:|---:|
| INT8 SDOT, 64 outputs x 5 positions, K=256 | 472.8 GOPS | 512 GOPS | 92.4% |
| INT16 SDOT to INT64, 32 outputs x 5 positions | 237.4 GOPS | 256 GOPS | 92.8% |
| NNUE3 row-major, 5 positions x 32 heads | 230.4 GOPS | 256 GOPS | 90.0% |
| NNUE3 row-major, 6 positions x 32 heads | 238.0 GOPS | 256 GOPS | 93.0% |
| NNUE2 single output dot | 9.66 GOPS | 256 GOPS | 3.77% |
| NNUE2 8-position output tile | 33.38 GOPS | 256 GOPS | 13.04% |

The approximately 90% result applies to the packed matrix microkernel. It does
not describe an entire NNUE evaluation or MCTS node, which also includes sparse
updates, clipping, reductions, tree traversal, rules, cache misses, and control
flow.

Additional evaluator results:

- 53.0 ns for one NNUE2 clipped output dot;
- 15.3 ns/position for the 8-position output tile;
- 65.2 million output positions/s for the weight-reusing 8-position tile;
- 1.236 million complete make/update/evaluate/unmake/evaluate round trips/s,
  equivalent to 2.472 million evaluations/s;
- 277,237 positions/s for the batched TSM3 path at batch 48.

### End-to-end neural MCTS

The play benchmark uses one persistent USI process, 48 pinned workers,
one-second searches, exact rules, and 96 positions split equally among opening,
middlegame, and late-game phases.

| Configuration | Median nodes/s | Opening | Middlegame | Late game |
|---|---:|---:|---:|---:|
| Pre-optimization | 2.583M | - | - | - |
| Earlier candidate | 4.454M | - | - | - |
| `LeafBatch 5`, play default | 4.782M | 5.345M | 5.112M | 4.142M |
| `LeafBatch 12`, throughput | 5.261M | 6.093M | 5.317M | 3.652M |

Batch 12 is 10.0% faster overall than batch 5 on this corpus, but its late-game
rate is lower. This is a useful example of why one aggregate throughput number
does not determine playing configuration.

The model used by this benchmark is a native NNUE3 performance fixture trained
from a small checked-in match corpus. It is not a production strength model.
Playing changes require match and SPRT validation.

## 8. Build and benchmark

Native FCC build:

```sh
OUT_DIR=build-fcc-a64fx ./scripts/build_fcc_a64fx.sh
```

The build script runs rule, search, SIMD, NNUE, integer-batch, UCT, and SDOT
correctness tests as well as native microbenchmarks.

Representative pinned kernel tests:

```sh
taskset -c 12 build-fcc-a64fx/sdot-i8-gemm-bench 256 100000
taskset -c 12 build-fcc-a64fx/sdot-i16-gemm-bench 256 100000
taskset -c 12 build-fcc-a64fx/nnue-batch-bench 256 1000000
```

Reproduce the real-play benchmark:

```sh
python3 tools/prepare_nnue.py selfplay-tiny-aobannue.jsonl \
  selfplay-tiny-yaneuraou.jsonl -o build/perf/play.ndf1 --shuffle --seed 7
cpu/train_nnue build/perf/play.ndf1 build/perf/play-v3.nnue 5 0.01 32767 32
python3 scripts/bench_a64fx_play.py \
  --engine build-fcc-a64fx/tinyshogi \
  --model build/perf/play-v3.nnue \
  --positions-per-phase 32 --movetime-ms 1000 \
  --threads 48 --a64fx-mode auto --leaf-batch 5
```

## 9. Self-play and training

### Direct NDF1 generation

For large runs, self-play writes fixed-size 100-byte NDF1 records directly.
The engine first writes a `.partial` file, updates and flushes the header, calls
`fsync`, and atomically renames the completed shard. `--game-offset` makes game
IDs and seeds deterministic across rank-count partitions.

```sh
build-fcc-a64fx/tinyshogi --selfplay \
  --eval-model current.nnue --games 100 --game-offset 0 \
  --simulations 100000 --threads 48 --leaf-batch 12 \
  --output-format ndf1 --output train.ndf1
```

Merge completed shards without decoding them:

```sh
tools/merge_ndf.py --output generation.ndf1 data/rank-*.ndf1
```

### Distributed A64FX trainer

The MPI trainer uses one rank and 48 OpenMP threads per node. Its synchronous
algorithm is:

1. Count records by 81 perspective-king buckets.
2. Greedily balance bucket ownership among ranks.
3. Route records once with chunked `MPI_Alltoallv`.
4. Preallocate each owned bucket exactly from the global census.
5. Build deterministic stratified global minibatches.
6. Compute sparse and dense gradients with OpenMP.
7. Keep board-feature gradients on their unique owner rank.
8. Allreduce replicated hand-feature and dense gradients.
9. Apply exact lazy sparse momentum and materialize its tail before export.
10. Reduce owner-held board weights to rank zero and save NNUE3.

One-node and twelve-node runs from identical shards and hyperparameters produced
byte-identical 94,228,157-byte NNUE3 models in the live validation.

Launch a complete PJM generation:

```sh
scripts/train_a64fx.py --nodes 12 --games 12000 \
  --simulations 100000 --model current.nnue \
  --output-dir runs/generation-001 --archive-data
```

`--archive-data` is optional. Avoiding a copy from each node's `/local`
filesystem back to shared storage can save substantial iteration time.

### Optimizers

Momentum SGD is the reproducible baseline. The distributed trainer also has
experimental Nesterov and Muon modes:

```sh
build-fcc-a64fx/train_nnue_mpi --data train.ndf1 --output next.nnue \
  --optimizer nesterov --learning-rate 0.001 --momentum 0.9

build-fcc-a64fx/train_nnue_mpi --data train.ndf1 --output next.nnue \
  --optimizer muon --learning-rate 0.001 \
  --muon-learning-rate 0.01 --momentum 0.9
```

Muon applies five quintic Newton-Schulz steps only to the hidden 32x256
matrices. Sparse embeddings, classifier weights, and biases retain momentum
SGD. Optimizer selection must be based on held-out loss and match strength, not
training loss alone.

A live 12-node smoke comparison used the same 136-record shard on every rank
(1,632 samples/epoch), global batch 2,304, momentum 0.9, and 1,000 epochs:

| Optimizer | Learning rate | Wall time | Final training MSE | Warm throughput |
|---|---:|---:|---:|---:|
| Momentum SGD | 0.001 | 23.53 s | 0.96737563 | 79.9k samples/s |
| Nesterov SGD | 0.001 | 23.37 s | 0.96736494 | 80.5k samples/s |
| Muon hybrid | 0.001 auxiliary, 0.01 matrix | 32.25 s | 0.05914961 | 49.4k samples/s |

All three produced finite, loadable NNUE3 models. Muon reduced training loss
much faster in this smoke test but was 38% slower in wall time. The dataset is
tiny, duplicated between ranks, and has no held-out split, so this result only
establishes implementation stability; it does not establish generalization or
playing-strength superiority.

### Real non-duplicated comparison

A live 12-node run generated 10,904 records from 96 distinct games using
disjoint rank game ranges. After removing 911 repeated opening positions, the
corpus contained 9,993 unique records. A deterministic 80/20 split produced
7,994 training records across 12 rank shards and 1,999 held-out records. Each
optimizer saw the same training shards, seed, global batch (2,304), and 1,000
epochs:

| Optimizer | Wall time | Final train MSE | Held-out MSE* | Final throughput |
|---|---:|---:|---:|---:|
| Momentum SGD | 46.55 s | 0.00990645 | 9,905.355 | 98.7k samples/s |
| Nesterov SGD | 46.92 s | 0.00990646 | 9,905.355 | 187.2k samples/s |
| Muon hybrid | 55.63 s | 0.00061604 | 10,935.603 | 159.4k samples/s |

\* `eval_nnue` reports the model's fixed-point output against the original
NDF1 value units. The absolute scale is less important here than the matched
comparison.

Muon fit the training records much more aggressively but had approximately 10%
higher held-out error than SGD. On this real, non-duplicated split, Muon is not
yet a quality improvement; it is a faster optimizer for fitting the training
set and needs regularization, lower matrix learning rate, or early stopping.
The next meaningful sweep is Muon matrix LR and checkpointed early stopping
against held-out loss, followed by playing-strength matches.

The follow-up sweep found that `--muon-learning-rate 0.005` was the most stable
tested setting. Held-out MSE over training duration was:

| Muon epochs | Held-out MSE |
|---:|---:|
| 100 | 9,909.750 |
| 300 | 10,014.342 |
| 600 | 10,532.301 |
| 1,000 | 9,962.271 |

The best Muon point is close to, but still slightly worse than, the Momentum
SGD baseline. The non-monotonic curve makes checkpointed early stopping
essential; the final checkpoint should be selected by held-out loss, followed
by a strength match rather than by training loss.

## 10. Performance methodology

Use three distinct gates:

1. **Correctness:** scalar/SIMD equality, rule tests, deterministic fixed-node
   searches, and one-rank/multi-rank optimizer identity.
2. **Kernel performance:** pinned cores, warm-up rounds, checksums, known clock,
   and arithmetic efficiency relative to the matching operation type.
3. **End-to-end performance and strength:** stratified real positions,
   persistent engine process, median and phase rates, then match/SPRT testing.

Do not compare INT8 measured throughput with an INT16 peak, report a batched
microkernel as whole-engine efficiency, or optimize only the opening position.

For simulator analysis, `scripts/run_clair_a64fx_pipeline.sh` can report cycles,
IPC, cache/TLB behavior, bandwidth, and execution stalls. Native hardware
measurements remain the final performance authority.

## 11. Current limitations and next work

- The bundled NNUE3 checkpoint is a performance fixture, not a strength model.
- Value-only MCTS has no learned policy head; root policy is derived from search.
- Training currently stores each rank's owned records in memory after routing.
  Exact preallocation avoids transient reallocations, but billion-position runs
  still require capacity planning.
- Muon and Nesterov are experimental until matched held-out and SPRT results are
  available.
- Peak kernel efficiency is already near the arithmetic target; larger gains
  now depend mainly on reducing non-kernel work, improving late-game batching,
  and increasing useful search quality per node.

## 12. Recommended configurations

For normal play:

```text
Threads = 48
MCTSMode = neural
A64FXMode = auto
LeafBatch = 5
```

For throughput-oriented self-play:

```text
Threads = 48
MCTSMode = neural
A64FXMode = auto
LeafBatch = 12
```

For distributed training, start with momentum SGD and a global batch divisible
enough to keep all ranks busy. Record the dataset hash, model hash, rank count,
seed, optimizer, global batch, learning rate, compiler, CPU frequency, and all
performance/strength gates for every candidate.
