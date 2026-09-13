# Native DL implementation: verification record

Date: 2026-09-13. This records implementation checks, not a strength result.

GEMM base: `e587f28d39f255be604864bdba655fa43bf257ab`.
Initial local GEMM commit: `6b19f8287e2c7dcf3028d5f90feb262e0853a4ea`, branch
`tinyshogi-native-nn`: 18 new files, 3,011 lines in `nn/` (runtime, kernels,
native trainer/replay, PyTorch oracle, tests, builds and documentation).
Follow-up commit `1dceea19f6d6ebdaed4f7595c724df137961dfc6`: 5 files,
149 insertions / 46 deletions, adding compensated BF16 training, full-size tests
and recognition of the installed ROCm library layout. This was the initial
hardware-qualified pin; the later sm120 optimization is recorded in
[GEMM's optimization report](../third_party/gemm/nn/SM120.md). No remote push was performed;
publish the GEMM commits before expecting a fresh remote clone to retrieve them.
The original dirty `/home/syoyo/work/gemm/main` working tree is unchanged.

Previous local GEMM pin: `e6fca99226091298ec23248c29a31246aa1172d9` (sm120
optimization: 14 files, 991 insertions / 25 deletions). This adds tiled asynchronous
MMA, parallel training reductions/attention, FLOP-accounted benchmarks and
explicit experimental integer operand paths. Standard full-network tests and
CUDA C32 memory/race checks pass. Representative steady-state training improved
57.4→219.7 examples/s; the 95% peak target and integer-path full-network
qualification remain unmet. See the report linked above for exact measurements,
test limitations and the retained FP32 stress discrepancy. This commit is also
local only; no push was performed.

## ROCm optimization follow-up

Previous local GEMM pin: `4d982b9dd9bd4cae84f3c447e711db81cc92151f`:
18 files, 976 insertions / 56 deletions. The parent gitlink is updated;
the commit is local only and has not been pushed.

See [GEMM RDNA4 report](../third_party/gemm/nn/RDNA4.md) for source/build details,
matrix timings, peak accounting and the integer-path follow-up plan. Original
WMMA tiles and parallel training operations improve microbatch-16 full-model
training from 45.7173 to 371.092 examples/s; opt-in hipBLASLt hybrid reaches
387.378. Batch 64 reaches 464.597, without changing the campaign's BN setting.
No 95% peak, convergence, long-campaign or strength claim is made.

C32 and full batch-2 gradients/checkpoints pass, both Make/CMake configurations
build, CPU/PyTorch regressions pass, and CTest passes 14/14 with and without Lt.
Tail/transpose/accumulation and larger matrix checks pass. Two real-replay
updates per ROCm backend saved independent checkpoints under `build/dl/`.
The hybrid checkpoint also completed an eight-ply native self-play reload smoke
test. Switching the optional Make build back off removes the vendor/C++ runtime
dependencies from the default GN library, verified with its ELF dependencies.

The new **full batch-16** CPU gradient check fails: legacy 0.00289522934,
optimized native 0.00289523382, hybrid 0.00383229931, FP32 0.006368942, against
the unchanged 0.001 gate. Native error predates this optimization. Cause is
not fully diagnosed. Full ROCm campaign preflight now checks the actual
microbatch and prevents silently accepting this failure. Six offline tooling
tests include the new preflight routing. ROCm SDK headers were downloaded only
into ignored build storage; no system installation or GPU settings changed.

## ROCm accumulator and packing follow-up

Previous local GEMM pin: `3fd65cd742026cb98085e550a156718c64cb2b60`:
14 files, 1,084 insertions / 66 deletions. Local only; no push. This adds
bit-exact fused forward convolution/BF16 packing, coalesced default attention,
coalesced transposes for integer row scaling, tuned 64×32 INT16-style WMMA,
and explicit BF16/INT32/INT64 accumulator experiments. All authored code is MIT;
no GPL engine code, shogi weights or new runtime dependency was introduced.

Three alternating before/after runs (50 steps, full model, microbatch 16) give
median native training 369.981→383.233 examples/s (+3.58%), and optional
hipBLASLt hybrid 385.503→400.245 (+3.82%). Hybrid inference is 8.30386→6.93760 ms.
Whole-step hybrid useful GEMM throughput is 4.29105 TFLOP/s (2.20054% of nominal
dense BF16 peak); six-product work is 25.7463 TFLOP/s (13.2032%). FP32 attention
is accounted separately. JSON now reports useful versus product operations,
correct FLOP/IOP units and explicit dense-peak percentages.

Experimental 50-step runs: BF16/FP32 accumulation 598.068 examples/s;
native BF16 accumulation 592.145; BF16 partials K128→FP32 584.832;
INT8/INT32 521.243; INT8/INT64 partials 518.739; INT16-style/INT64 442.432.
INT16 uses four signed/unsigned INT8 WMMA products with bounded INT32 partials
and exact INT64 recombination, not native INT16 or INT64 WMMA. FP32 master
weights, optimizer, stored gradients and non-matrix work remain in every mode.
See the [complete measured report](../third_party/gemm/nn/RDNA4.md#precision-follow-up).

Exact integer overflow/endpoints, BF16 representable-value cases, fused packing,
all transpose/tail cases, CPU/PyTorch, CUDA regression and CTest 14/14 in both
build modes pass. Release GN tests now retain assertions. The strict C32 INT16
gradient gate passes (0.000190985), but full-model batch-2 fails (0.0612931).
BF16 accumulation causes 0.50604 convolution relative error (0.0526036 with
K128 partials) and fails network qualification. Report mode continues diagnostics
but returns failure; experimental checkpoints are not promoted. Normal batch-16
gradient error remains exactly 0.00289523382, so the campaign gate still blocks.

Best large-GEMM measurement this iteration is hipBLASLt BF16/FP32:
125.649 TFLOP/s, 64.4353% of dense peak. INT16's four INT8 products reach
104.868 TIOP/s (26.9584%) on the weight-gradient shape. Neither is whole-training
throughput. **95% peak, reduced-precision full-training acceptance, convergence,
and playing strength remain unachieved.** No long campaign or GPU settings change.

## BF16 operands / FP32 accumulation follow-up

Current local GEMM pin: `62121013f7551522d2fdfa4e3d765bb237ba73b4`:
16 files, 637 insertions / 105 deletions. The parent gitlink is updated;
no push was performed and the original dirty GEMM checkout remains untouched.

Fused backward im2col/BF16 packing, specialized default indexing and coalesced
BN improve standard six-product hybrid training **398.975→439.431 examples/s
(+10.14%)** at batch 16, medians of three alternating 100-step measurements.
The ordinary training precision contract and all acceptance gates are unchanged.

New experimental Lt backends retain FP32 accumulators, master weights,
gradients and optimizer state. At batch 64, medians of three 100-step runs:

| Backend | Examples/s | BF16 matrix-product TFLOP/s | % nominal dense peak |
|---|---:|---:|---:|
| `hip-bf16-blaslt`, one product | 1133.28 | 12.1499 | 6.23073% |
| `hip-bf16x3-blaslt`, three products | 782.170 | 25.1570 | 12.9011% |
| `hip-bf16-mixed-blaslt`, six forward / three backward | 703.266 | 30.1590 | 15.4662% |

These are whole-step synthetic timings, including clipping/AdamW, excluding
data decoding and checkpoint I/O. Product counts exclude padding; mixed uses
an average multiplier of four over forward/backward, not more useful work.
The denominator is 195 TFLOP/s dense 16-bit matrix peak. **The 1,000 examples/s
rate target is met only by the unqualified one-product path; 75% is unmet.**
Final post-cache-correction spot checks measured 1139.33 / 703.869 examples/s
for one-product / mixed, without changing the reported three-run medians.

Full-model batch-16 gradient relative errors: one-product 0.38367618,
three-product 0.013713891, mixed 0.0038323371. Mixed cuts error roughly 100x
versus one-product, but still fails the unchanged 0.001 gate. Mixed full
batch-2 passes at 0.000024398431, including update and exact reload. Batch-64
accuracy and convergence are not claimed. Native six-product batch-16 remains
0.00289523382, unchanged. Per-node snapshots locate gradient amplification
at a handful of near-zero ReLU sign differences; this is evidence, not a
reason to bypass qualification or change activations.

The matrix diagnostic now supports three-product compensation, exact mode
selection, bounded 32-candidate Lt tuning and explicit pass records. Tuning
keeps a single algorithm per shape to preserve accumulation tests, and uses
separate scratch output so trials do not overwrite C. Model execution uses
deterministic first-supported algorithms: timed selection had broken exact
checkpoint reload and was removed from model execution. An SDK/ROCEW event
symbol collision found during bring-up was fixed in the optional adapter.

Final fail-fast transpose/tail/add sweeps (including M3/N2/K1), packing and
integer/BF16 exact checks, native/mixed/INT16 C32 regressions, CUDA C32,
CPU/PyTorch, both RTC compilers, CTest 14/14 in both build configurations and
six offline tool tests pass. No AMD race-tool, long campaign or playing-strength
qualification is claimed. See [the complete report and reproduction commands](../third_party/gemm/nn/RDNA4.md#bf16fp32-follow-up).

## Passed

- `make check -j4`: existing C engine/rules/search/NNUE/SIMD/integer suites,
  all 30 match-tool Python tests, native MCP adapter.
- `make dl-check -j4`: explicit feature/action/history fixtures, promotion,
  drops, repetition and perpetual check; PUCT sign/budget, multithreading,
  cancellation and inference failure; native self-play→replay→microbatch
  training→USI reload; truncated replay rejection; campaign resume; five
  offline replay/budget/paired-score/referee tests.
- `cmake -S . -B build/cmake-dl -DTINYSHOGI_DL=ON -DCMAKE_BUILD_TYPE=Debug`,
  build and `ctest --test-dir build/cmake-dl --output-on-failure -j4`:
  14/14 tests. Fixed the pre-existing MCP test's build-directory-relative
  working directory while integrating the new build.
- `make -C third_party/gemm/nn check`: central differences in all 35 learned
  tensors of a small CNN+Transformer network, overfit loss 2.587411→0.771658,
  exact checkpoint inference and next-update resume, invalid input/memory checks.
- `nn/reference.py` using the existing local PyTorch 2.10.0+cu128 environment:
  C=4 and C=32 forward, training loss, **every element** of all 35 learned
  tensor gradients, and AdamW parity. Optimizer comparison uses identical
  already-compared gradients so cancellation noise in theoretically zero
  BN/key-bias gradients is not amplified differently by Adam epsilon.
- AddressSanitizer + UndefinedBehaviorSanitizer: native math tests, feature/PUCT
  tests, and four concurrent self-play games. LeakSanitizer itself fails in
  this ptraced sandbox; reruns used `ASAN_OPTIONS=detect_leaks=0`. Consequently
  this is **not** a leak-check pass.
- `python3 -B third_party/gemm/nn/compile_gpu.py`: NVRTC sm120 and HIPRTC gfx1201
  compile the complete custom forward/backward/optimizer source. Offline
  `nvcc -ptx -arch=sm_120` and `hipcc --offload-arch=gfx1201 --genco` also compiled
  during initial backend bring-up. Physical device checks followed, below.
- `git diff --check` and GEMM staged whitespace checks.

## Physical GPU verification

Hardware: RTX 5060 Ti (sm120, NVIDIA driver 615.71.09) and RX 9070 XT (gfx1201,
ROCm libraries under `/opt/rocm/core/lib`). Device execution initially returned
77 inside the sandbox. Approved execution outside that sandbox reached both
GPUs; unavailability was a sandbox limitation, not missing hardware.

- Small and 9×9 C32 forward/backward tests pass on CUDA and HIP, including their
  diagnostic FP32 paths. The final CUDA C32 compensated-BF16 run has policy
  relative L2 0.0085298163 and global gradient relative L2 0.0000014056353.
- Full C256/20-block tests with deterministic independent inputs pass:

  | Backend | Policy relative L2 | Global gradient relative L2 |
  | --- | ---: | ---: |
  | CUDA compensated BF16 | 0.005719826 | 0.00091500544 |
  | HIP compensated BF16 | 0.005736607 | 0.000015331235 |
  | CUDA diagnostic FP32 | 0.0000017360455 | 0.00091431203 |

  Gates are global gradient relative L2 ≤0.001, inference relative L2 ≤0.01
  (BF16) or ≤0.0001 (FP32), and matching legal-mask/WDL loss. A global gradient
  pass does **not** mean every parameter tensor meets that relative tolerance.
  AdamW is checked elementwise using identical already-compared gradients;
  checkpoint reload inference is bit-exact on the tested same backend.
- CUDA Compute Sanitizer `memcheck` on the C32 network reports zero errors.
  This is not a GPU race-check or full-size memory qualification.
- Small end-to-end GPU campaigns pass on both devices, each publishing 32
  positions and reaching optimizer step 16. Final run directories are
  `build/dl-cuda-final-smoke` and `build/dl-hip-final-smoke`.
- The full network generated four 16-ply games (64 positions) with concurrent
  native CUDA PUCT self-play. Both GPU backends trained one effective batch-256,
  microbatch-16 update from that replay and saved a checkpoint:

  | Backend | Policy loss | Value loss | Pre-clip gradient norm | Examples/s |
  | --- | ---: | ---: | ---: | ---: |
  | CUDA | 6.98197114 | 4.70389828 | 1131.05017 | 75.2931 |
  | HIP | 6.98195222 | 4.70390844 | 1131.11206 | 40.9459 |

  These are smoke checks from random initialization, **not** strong trained
  models. Both use host tensor allocation 877,219,808 bytes at the training
  boundary. Checkpoints are `build/dl/full-{cuda,hip}-trained.safetensors`.

Plain BF16 operands produced substantial gradient drift; three-product
compensation passed the small network but failed the deeper model. Training
now decomposes each FP32 operand into three BF16 components and accumulates six
products (component indices i+j≤2), separating the high-product accumulator
from corrections. Inference still uses one BF16 product. Sensitive attention
reductions use doubles, while matrix accumulators and model state remain FP32.

### Retained numerical failure

`test_gpu cuda-fp32 CHECKPOINT stress` uses a highly correlated sinusoidal input
in the full network and fails the strict global gradient gate: relative L2
0.0073117658 versus the required 0.001. Forward/loss agreement is much closer.
Reduction order and ReLU boundaries are suspected, but the discrepancy has not
been fully diagnosed. The original stress case remains runnable; passing the
independent-input case does not supersede this failure or certify all inputs.

## Initial full-network measurements (before sm120 optimization)

Host: AMD Ryzen Threadripper 1950X. GCC 13.3, `-O2`, runtime AVX2/FMA projections,
up to eight forward workers. Not an isolated or statistically robust benchmark.

```sh
third_party/gemm/nn/build/gn_tool init build/dl/full-initial.safetensors
third_party/gemm/nn/build/gn_tool bench build/dl/full-initial.safetensors cpu 1 2
```

GPU command: `gn_tool bench build/dl/full-initial.safetensors BACKEND 16 3`.
20 blocks, C256, 22,764,238 learned parameters. Two warm-up inferences followed
by two measured iterations on CPU and three on each GPU:

| Backend | Batch | Inference ms/batch | Inference positions/s | Training examples/s | Host tensor bytes |
| --- | ---: | ---: | ---: | ---: | ---: |
| Ryzen CPU | 1 | 74.402 | 13.4405 | 0.947711 | 396,416,528 |
| RTX 5060 Ti | 16 | 41.8214 | 382.58 | 64.3138 | 877,219,808 |
| RX 9070 XT | 16 | 37.3034 | 428.915 | 37.5495 | 877,219,808 |

These are short, non-isolated observations, not sustained-throughput guarantees.
The CPU measurement does not establish a useful CPU-only strength-training budget.
Smoke checkpoints and generated games are only build artifacts, not published
trained weights.

## Not completed / not claimed

GPU hardware execution, full-size parity and effective batch-256 microbatch
training were exercised, but broader input/seed/shape sweeps, resolution of the
stress failure, race tooling and long-running performance/memory qualification
remain outstanding.

No 336-hour GPU campaign, trained-model promotion, FukauraOu match, bootstrap
strength acceptance, A64FX execution, SVE optimization, BN folding, inference
cache or subtree reuse was completed. The separate match runner's transport
uses existing tested USI tools, and its score gate has offline tests; the new
runner has not been exercised against a real FukauraOu binary. The supplied
documentation and preflight gates keep these outstanding items explicit.

## 2026-09-13 RDNA4 accuracy/performance follow-up

- Added checkpointed configuration version 2, using SiLU for configurable
  activations while preserving version-1 ReLU semantics.
- Qualified `hip-bf16x3-blaslt` on the full C256/20 version-2 model at batch
  16: output relative L2 0.000019643069 and global parameter-gradient relative
  L2 0.00041490896 (gate 0.001), including AdamW and exact same-backend reload.
- Three final batch-64 100-step runs measured 807.838 examples/s median
  (806.399--809.994), 8.72600 useful matrix TFLOP/s and 25.9826 BF16 product
  TFLOP/s, or 13.3244% of the RX 9070 XT nominal 195-TFLOP/s dense peak. The
  requested 1,000 examples/s and 75%-of-peak thresholds remain unmet for a
  qualified path.
- Added an explicit FP16-input/FP32-accumulate rocBLASLt experiment. It reaches
  1,148.55 examples/s and 6.31471% of nominal peak, but fails qualification
  with batch-16 gradient error 0.0241998443; it is not a training default.
- Grouped eight-query forward attention shares K/V, and grouped score backward
  reduced its profiled aggregate from 67.2 ms to 37.1 ms. Rejected broad and
  shape-specific K=256 rocBLASLt routing after whole-step regressions.
