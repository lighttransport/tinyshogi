# Independent policy/value engine

An independently authored policy/value engine and native training stack inspired
by published DLshogi/FukauraOu concepts. This is **not** source, feature, policy,
or weight compatible with those engines. New tinyshogi code is Apache-2.0; the
new GEMM neural module is MIT.

## Status

CPU forward/backward/AdamW, independent PyTorch parity, PUCT, concurrent self-play,
packed replay, resumable training and USI loading are tested. The default network
has 22,764,238 learned parameters. CUDA sm120 (RTX 5060 Ti) and HIP gfx1201
(RX 9070 XT) pass small, 9×9 C32, and full-network correctness/checkpoint tests.
Short native self-play/training campaigns also pass on both GPUs. No completed
336-hour campaign or strength claim is made. A retained correlated-input stress
case fails the strict gradient tolerance, including in the CUDA FP32 diagnostic
path; numerical qualification is not complete. See the [verification log](dl-worklog.md).

Remaining optimization/acceptance work: broader GPU numerical/race sweeps,
long-running memory/performance profiling, tiled attention/reductions, inference BN folding,
inference caching/subtree reuse, CPU backward parallelism and the strength
experiment. A64FX has a portable scalar route only; SVE and remote validation
are optional future work.

The sm120 training path has since been optimized; see the
[GEMM sm120 report](../third_party/gemm/nn/SM120.md) for before/after measurements,
explicit FLOP accounting and experimental INT8/INT16-style paths. The 95% peak
target is not achieved, and neither integer variant is qualified for full-size
training. The campaign still selects the validated `cuda` path with microbatch 16.

ROCm now has LDS-tiled WMMA and an optional `hip-blaslt` hybrid: measured
batch-16 training improves 45.7→371.1/387.4 examples/s. The 95% target is unmet.
A newly added full batch-16 gradient check fails in optimized, legacy and FP32
HIP paths; full ROCm campaigns now require this preflight and are blocked by
that unresolved qualification failure. See [RDNA4 report](../third_party/gemm/nn/RDNA4.md).

## Build

Requires POSIX, C11, pthreads, Make and Python 3.11+. CPU builds need neither
PyTorch nor GPU SDKs. GPU execution loads drivers and NVRTC/HIPRTC dynamically.

```sh
git submodule update --init third_party/gemm
make dl-check -j4
python3 -B tools/dl_campaign.py --run-dir build/my-dl-smoke \
    --backend cpu --smoke --hours 0.1 --generations 2
```

`make dl` builds `build/dl/tinyshogi`, `dl-selfplay`, `dl-test`, and the generic
GEMM tools in `third_party/gemm/nn/build`. Default `make` remains unchanged.

With a complete ROCm development SDK, `make dl HIPBLASLT=1` opts into the
external AMD library. `ROCM_PATH`, `HIPBLASLT_INCLUDE`, and `HIPBLASLT_LIB`
override its paths. Select `DLBackend=hip-blaslt` or the matching training
backend explicitly; plain `hip` remains vendor-BLAS-free. CMake uses
`-DGN_HIPBLASLT=ON` alongside `-DTINYSHOGI_DL=ON`. The current host's build-only
header workaround and numerical limitations are recorded in the RDNA4 report.

```sh
cmake -S . -B build/cmake-dl -DTINYSHOGI_DL=ON -DCMAKE_BUILD_TYPE=Debug
cmake --build build/cmake-dl -j4
ctest --test-dir build/cmake-dl --output-on-failure
```

Meson/xmake/WASM retain their existing non-DL builds. The GEMM submodule was
initialized from `/home/syoyo/work/gemm/main` at upstream commit
`e587f28d39f255be604864bdba655fa43bf257ab`; unrelated local changes there were
not copied or edited. The new NN commit must be published to the configured
GEMM remote before another machine can fetch the new gitlink. Nothing is pushed
automatically.

## Ownership and search

| Component | Location | Responsibility |
| --- | --- | --- |
| Rules, history, USI | `src/shogi.*`, `src/main.c` | Existing independent shogi engine |
| Encoding | `src/dl_features.*` | Versioned shogi features/action labels |
| Evaluator contract | `src/policy_value.h` | Legal-order logits, WDL batch API |
| Inference queue | `src/dl_eval.*` | Shared model, batch up to 32, 1 ms coalescing |
| PUCT | `src/puct_search.inc` | History-specific trees and visit targets |
| Neural math | `third_party/gemm/nn` | Generic NHWC operators and native training |
| Data/campaign | `tools/dl_selfplay.c`, `tools/dl_campaign.py` | Own games, replay, budgets |
| Opponent match | `tools/dl_match.py` | External black box; never training data |

The existing scalar evaluator plugin ABI is unchanged. PUCT uses worker-private
trees and aggregates root statistics; inference batches span workers/games.
Nodes are not merged by a history-blind board hash. One outstanding evaluation
per worker eliminates the need for shared-tree virtual visits in this version.
Inference failure aborts search and discards the unfinished shard; there is no
silent heuristic or CPU fallback.

## Version-1 encoding and network

NHWC layout, row-major squares. White-to-move rotates 180 degrees and swaps
relative colors.

| Planes | Meaning |
| --- | --- |
| 0–27 | 14 piece types × 2 relative colors |
| 28–55 | Geometric attack union per type/color, occupancy-aware, no pin test |
| 56–69 | P/L/N/S/G/B/R hands divided by 18/4/4/4/4/2/2, both colors |
| 70–71 | Check flags for mover/opponent |
| 72–74 | Previous matching positions ≥1, ≥2, ≥3 |
| 75–76 | Continuous checks since latest matching position, each relative color |
| 77 | `min(move_number / 512, 1)` |
| 78–79 | Canonical x/y coordinates in [-1,1] |

Continuous-check flags are zero without a previous occurrence or without a move
by that color. Repetition includes board/hands/side, excluding the current tail.

Action ID is `square*139+plane`. Normal moves use the **source** square; drops
use the **destination**. For N/NE/E/SE/S/SW/W/NW direction d, distance r=1..8 and
promotion p=0/1, the plane is `(d*8+r-1)*2+p`. Forward knights (-1,-2)/(+1,-2)
use `128+2*jump+p`; drops use `132+hand`. Only legal moves enter softmax/targets.
Illegal targets are exactly -1; legal entries, including zero-visit moves, sum to one.

Default: 5×5 C256 Conv/BN/ReLU stem, then 20 blocks. Every fifth block is pre-LN
attention over 81 tokens, 8 heads of width 32, learned 17×17 relative bias, and
width-512 SwiGLU. Other blocks have two 3×3 Conv/BN layers, ReLU after the first
and after residual addition. Policy is a per-square 139-way linear projection.
Value is per-square 32-way ReLU, flatten, hidden-256 ReLU, then WDL. WDL order
is win/draw/loss **for the mover**; backup negates W−L per ply.

CPU uses FP32 and runtime AVX2/FMA projections with up to eight persistent
workers. CUDA uses custom BF16 `mma.sync` sm120 kernels; HIP uses gfx12 BF16
WMMA wave32 (gfx1201, RX 9070 XT). Inference rounds operands to BF16. Training
decomposes FP32 operands into three BF16 components and accumulates six products
with a separate correction accumulator: this avoids the observed deep-network
gradient drift of plain BF16 and the less accurate three-product variant.
Matrix accumulators, master weights, gradients and moments stay FP32. `cuda-fp32`/`hip-fp32` are
diagnostic GPU paths. Default backends use no cuBLAS, rocBLAS, cuDNN, TensorRT or
ONNX Runtime. Optional `hip-blaslt` uses AMD hipBLASLt, with native WMMA for
short-K/small training matrices. GPU attention/reductions are now parallelized.

## Data, training and recovery

Safetensors checkpoints contain every parameter, BN statistics, AdamW moments,
optimizer step, RNG and architecture. Conv weights are flattened OHWI. Save
requires an optimizer boundary and uses fsync+rename. Campaign JSON sidecars
pin model/parent/replay/executable hashes; safetensors is authoritative. Bare
native `gn_save` does not produce JSON. Same-backend CPU resume, including the
next optimizer update, is tested bit-for-bit. Cross-backend and multithreaded
self-play bitwise determinism is not promised.

GNR1 replay is our little-endian format, not HCPE. Records store game/generation
IDs, ply, WDL, packed feature planes and sparse action/visit pairs. Binary planes
are bit-packed, scalars broadcast FP32, coordinates reconstructed. Finished
games also have USI traces. Shutdown discards unfinished games rather than labelling them draws.

```sh
third_party/gemm/nn/build/gn_tool init build/dl/initial.safetensors
build/dl/dl-selfplay build/dl/initial.safetensors build/dl/games.gnr \
    64 400 1 512 1 cuda 1 8
third_party/gemm/nn/build/gn_tool train build/dl/games.gnr \
    build/dl/initial.safetensors build/dl/trained.safetensors 16 256 .001 cuda 16 300
third_party/gemm/nn/build/gn_tool validate build/dl/games.gnr \
    build/dl/trained.safetensors cuda 512
```

Training arguments end with steps, effective batch, LR, backend, optional
microbatch and checkpoint seconds. BN uses **microbatch**, not accumulated-batch,
statistics. AdamW β=(.9,.999), ε=1e-8, decay=1e-4 on all learned parameters,
global norm clip=1. Self-play uses cpuct=1.5, Dirichlet α=10/legal-count at .25,
temperature 1 for 30 plies then argmax visits, 512-ply cap, no bootstrap resign.

Campaign: random initialization, latest million positions (including validation),
50,000-position warmup, four sampled examples per new non-validation position.
`game_id % 20 == 0` is validation-only. Validation reports masked policy/value
loss and WDL Brier score for up to 512 validation positions in the active window.
Archives remain for audit; **disk usage grows**, only the active window is bounded.
There is no automatic deletion of old models or games.

```sh
python3 -B third_party/gemm/nn/compile_gpu.py
third_party/gemm/nn/build/test_gpu cuda-fp32
third_party/gemm/nn/build/test_gpu cuda
third_party/gemm/nn/build/test_gpu cuda build/dl/full-check.safetensors full
# After hardware validation and throughput/memory review:
python3 -B tools/dl_campaign.py --run-dir build/dl-run --backend cuda --hours 336
```

Use `hip` on RX 9070 XT. GPU execution requires access to device nodes; in this
Codex environment it works outside the filesystem/device sandbox. Current ROCm
installations under `/opt/rocm/core/lib` are recognized by the loader; a custom
installation can use `ROCEW_ROCM_LIB` for its library directory.
The runner requires device preflight success and prepays
each phase from a persisted wall-time budget. GNU `timeout` survives supervisor
failure. Interrupted leases are charged in full; completed phases refund unused
time. Resume with identical configuration/binaries. Orphan outputs are not
automatically imported. SIGTERM requests an optimizer-boundary checkpoint or
finished-game publication; a hard kill may lose work since the last checkpoint.
GPU-phase time includes loading/indexing/validation, conservatively overcounting
usage. Match time is separate. Host/device tensor budgets are each 6 GiB, not
a combined process/driver RSS cap.

## USI

```text
usi
setoption name DLBackend value cuda
setoption name DLDevice value 0
setoption name DLModel value /absolute/path/trained.safetensors
setoption name DLBatchSize value 32
setoption name SearchMode value puct
setoption name Threads value 8
isready
position startpos
go movetime 1000
```

Use backend `cpu` for CPU. Model changes drain the previous search and replace
its queue/model. Loading a model does not automatically select PUCT.

## Strength protocol (not run)

`tools/dl_match.py freeze --help` freezes the candidate, supplied FukauraOu
v9.40 binary/commit, supplied `model-dr2_exhi.onnx`, 500 unique held-out SFENs,
disjoint development SFENs, eight CPU IDs, GPU UUID and operator provenance.
`run --lock ... --output ...` verifies hashes and runs sequential 1-second
searches on the same RTX 5060 Ti, no book/ponder, 512-ply cap. All decisions are
recorded; the referee retains complete history. Crashes, illegal moves and time
overruns invalidate the experiment, not manufacture wins. Finished games can
resume; a truncated final JSON line needs manual recovery. This does not change
the older NNUE benchmark protocol.

Gate: lower 95% paired-bootstrap **score** bound ≥.36 over 500 color pairs
(1,000 games). Draws score .5. This approximates a 100-Elo noninferiority goal,
not universal engine strength. Local hashes pin supplied artifacts, not upstream
authenticity; verify operator build/model provenance before calling a result official.

## Provenance boundary

Only public descriptions/interfaces were consulted for upstream shogi projects.
No GPL engine source, upstream Python model code, weights or HCPE data was copied,
translated, linked or used for training. This implementation record is not legal
certification of clean-room status. References:

- [DLshogi project](https://github.com/TadaoYamaoka/DeepLearningShogi)
- [FukauraOu v9.40 release](https://github.com/yaneurao/YaneuraOu/releases/tag/v9.40)
- [Public USI option documentation](https://github.com/yaneurao/YaneuraOu/wiki/思考エンジンオプション)
- [AlphaZero paper](https://arxiv.org/abs/1712.01815)
- [Public model usage notice](https://tadaoyamaoka.hatenablog.com/entry/2021/08/17/000710)

Opponent engines and models remain separately obtained/licensed black boxes;
the tools do not download or redistribute them. The compiled GEMM dependency
closure is new MIT `nn/*`, MIT `common/safetensors*.h`, Apache-2.0 `cuda/cuew.*`
(Blender Foundation), Apache-2.0 `rdna4/rocew.*` (vision-language.cpp authors),
plus system/driver libraries. Preserve their notices. Other GEMM experiments
are not linked. `nn/reference.py` is an original optional PyTorch mathematical
oracle, never a production training dependency.
