# tinyshogi

`tinyshogi` is a clean-room standard 9×9 shogi engine written in C11. It is
currently a CLI/USI engine using CPU-based, shared-tree Monte Carlo Tree Search
(UCT with heuristic rollouts and virtual loss).

The implementation includes orthodox move legality: promotion, drops, nifu,
dead-rank drops, uchifuzume, check and checkmate, fourfold repetition, and the
27-point entering-king declaration profile. The declaration profile requires
the king to be in the enemy camp, at least ten other pieces in that camp, no
check on the king, and 28 points for Sente or 27 for Gote. Rooks, bishops,
dragons, and horses are worth five points; other non-king pieces are worth one.

## Build

Meson:

```sh
meson setup build
meson compile -C build
meson test -C build
```

xmake:

```sh
xmake f -m release
xmake
```

Browser demo (requires `emcc` in `PATH`):

```sh
make -C web
python3 -m http.server -d web 8000
# open http://localhost:8000/
```

Vite development and production builds are also supported:

```sh
cd web
npm install
npm run dev       # http://localhost:5173
npm run build     # writes web/dist/
npm run preview
```

The browser build links the rules, evaluator, and search sources and does not
enable pthreads by default. It provides a small human-vs-human click-to-move
app in `web/`; select a piece and a highlighted destination, or select a
captured piece from a hand to make a drop. Every destination comes from the
engine's legal-move generator, including promotion and drop restrictions. The
app also supports undo/redo, Ctrl/Cmd-Z, SFEN import/export, and an optional
single-thread engine move running in a Web Worker. The Makefile-generated
Emscripten files are written to `web/build/`; Vite's production bundle is
written to `web/dist/`.

The core is C11. The initial threading and CLI backend uses POSIX pthreads and
`poll`; no third-party runtime or source dependency is required.

## USI commands

Supported commands include:

```text
usi
isready
setoption name Threads value N
setoption name Seed value N
setoption name MaxTreeNodes value N
setoption name RolloutDepth value N
setoption name UCTExploration value N
setoption name MultiPV value N
usinewgame
position startpos [moves ...]
position sfen <board> <side> <hand> <move-number> [moves ...]
go movetime <ms>
go searchmoves <move> ... [other go limits]
go btime <ms> wtime <ms> [byoyomi <ms>] [binc <ms>] [winc <ms>]
go nodes <count>
go depth <plies>
go infinite
go ponder [other go limits]
ponderhit
stop
d
quit
```

Without an explicit search limit, `go` searches for five seconds. The default
thread count is `min(available CPUs, 8)`. Set `Threads` to `1` and provide a
nonzero `Seed` for reproducible searches.
`RolloutDepth` controls the heuristic rollout horizon (default 256 plies), and
`UCTExploration` is the UCT exploration constant in thousandths (default 1414).
`QuiescenceDepth` adds a small tactical capture/promotion/check search at rollout
leaves (default 2 plies; set it to 0 to disable it).
`MultiPV` controls how many root candidates are reported in periodic `info`
lines; `bestmove` remains the top-ranked candidate.
`go ponder` keeps searching without a clock deadline until `ponderhit` changes
to the supplied clock/move-time limits, or until `stop` is received.

Example:

```sh
printf 'usi\nisready\nposition startpos\ngo nodes 1000\n' | ./build/tinyshogi
```

Self-play data export is available as a separate command. It writes one JSONL
record per position, including the SFEN, selected move, game result from the
side-to-move perspective, and the complete root visit distribution:

```sh
./build/tinyshogi --selfplay --games 100 --simulations 256 \
  --threads 1 --seed 7 --temperature 1000 --temperature-cutoff 30 \
  --output selfplay.jsonl

# Continue self-play with a native NNUE evaluator:
./build/tinyshogi --selfplay --eval-model model.nnue --games 100 \
  --simulations 256 --output selfplay.nnue.jsonl
```

Use `--temperature 0` for deterministic visit-max move selection. Games that
reach `--max-plies` without a terminal result are recorded as draws. The JSONL
format is versioned with `"version":1` and is intended for external training
pipelines.

The optional no-SDK CUDA handoff is documented in [cuda/README.md](cuda/README.md).
It uses a CUEW-style runtime loader and builds the CUDA probe with only `cc` and
`-ldl`; the normal CPU engine remains independent of CUDA.

An external Linux YaneuraOu NNUE engine can be downloaded and built with:

```sh
./scripts/download_yaneuraou.sh
```

The script uses the upstream `YANEURAOU_ENGINE_NNUE` edition, `AVX2`, and
`clang++` by default. Override `YANEURAOU_REF`, `YANEURAOU_TARGET_CPU`,
`YANEURAOU_COMPILER`, `JOBS`, `YANEURAOU_SOURCE_DIR`, or
`YANEURAOU_OUTPUT_DIR` as needed. The checkout is placed under ignored
`third_party/YaneuraOu/`, and the executable under `build/yaneuraou/`.
NNUE weights are separate from the source build; place the upstream `nn.bin`
where YaneuraOu expects it before running the engine.

To run a local USI self-play match, first build a YaneuraOu variant, then run:

```sh
YANEURAOU_EDITION=YANEURAOU_ENGINE_MATERIAL \
  ./scripts/download_yaneuraou.sh
python3 scripts/selfplay_match.py --games 10 --nodes 256 \
  --output selfplay-tiny-yaneuraou.jsonl
```

The match runner alternates colors, disables YaneuraOu opening-book use, and
writes one JSONL record per played position. Use the NNUE binary instead after
placing a compatible `eval/nn.bin` beside it with
`--yaneuraou build/yaneuraou/YaneuraOu`.

For another YaneuraOu-compatible NNUE, such as AobaNNUE, pass its Linux build
and evaluation directory explicitly:

```sh
python3 scripts/selfplay_match.py --games 2 --nodes 64 \
  --yaneuraou eval/AobaNNUE/source/YaneuraOu-by-gcc \
  --yaneuraou-eval-dir "$PWD/eval/AobaNNUE/eval" \
  --output selfplay-tiny-aobannue.jsonl
```

When driving an external engine through a pipe, wait for its `bestmove`
response before sending `quit` or closing the engine's standard input.

## External evaluators

The search accepts an optional external evaluator through the small C ABI in
[`src/eval.h`](src/eval.h). A shared library exports
`tinyshogi_eval_plugin()`, which returns a `TinyShogiEvalPlugin`. Its
`evaluate` callback receives an immutable `ShogiPosition` and the perspective
color, and returns a perspective-relative centipawn score. This makes an NNUE
or another model usable without adding its representation to the engine.

The callback may be called concurrently by search threads, so plugin state must
be immutable or internally synchronized. The example plugin can be built and
loaded as follows:

```sh
cc -shared -fPIC -Isrc examples/tinyshogi_eval_plugin.c -o /tmp/tinyshogi-eval.so
printf 'usi\nsetoption name EvalPlugin value /tmp/tinyshogi-eval.so\nposition startpos\ngo nodes 100\nquit\n' \
  | ./build/tinyshogi
```

The equivalent runtime option is `setoption name EvalPlugin value <path>`;
use `value none` to return to the built-in material/mobility evaluator.

For YaneuraOu NNUE compatibility, build the included USI adapter:

```sh
./scripts/build_yaneuraou_eval_adapter.sh
printf 'setoption name EvalPlugin value %s\\n' \
  "$PWD/build/yaneuraou-eval-adapter.so" | \
  env YANEURAOU_EVAL_ENGINE=$PWD/build/yaneuraou/YaneuraOu \
      YANEURAOU_EVAL_DIR=$PWD/build/yaneuraou/eval build/tinyshogi
```

The adapter keeps one YaneuraOu process alive and translates TinyShogi
positions to SFEN/USI. It uses YaneuraOu's `nn.bin` through its normal NNUE
loader; this is intentionally a process adapter rather than a reimplementation
of YaneuraOu's private binary format. Set `YANEURAOU_EVAL_DIR` to the directory
containing `nn.bin`.

CUDA `TSM2` checkpoints can be quantized for deterministic CPU inference:

```sh
python3 tools/quantize_tsm2.py model.tsm model.tsm3
```

The `TSM3` evaluator in `src/int_model.c` uses fixed integer arithmetic,
fixed-point softmax/exp/log/tanh helpers, and runtime AVX2 dispatch with a
portable scalar fallback. Its output is deterministic for a fixed model and
feature buffer.

An integer-only CPU SGD baseline is available for reproducible calibration and
small datasets:

```sh
make -C cpu train-int
make -C cpu eval-int
cpu/train_int selfplay.tsf selfplay.tfe model-int.tsm3 10
cpu/eval_int model-int.tsm3 selfplay.tfe
```

`eval-int` prints fixed-point value/policy results and a checksum, which is
useful for cross-machine reproducibility checks.

## Native NNUE training

TinyShogi includes a native value-only NNUE path using a versioned `NNUE1`
artifact, HalfKP-style sparse features, two perspective accumulators, and a
default 256-unit hidden layer:

```sh
python3 tools/prepare_nnue.py selfplay.jsonl -o selfplay.ndf1 --shuffle
make -C cpu train-nnue
cpu/train_nnue selfplay.ndf1 model.nnue 5 0.01
printf 'setoption name EvalModel value %s\n' "$PWD/model.nnue" | build/tinyshogi
```

The converter accepts TinyShogi self-play records, older USI-match records with
`result`, and records containing `teacher_value`. Bounded USI search can add
teacher labels:

```sh
python3 tools/bruteforce_teacher.py positions.jsonl teacher.jsonl \
  --engine build/tinyshogi --nodes 256
python3 tools/prepare_nnue.py selfplay.jsonl teacher.jsonl -o mixed.ndf1 --shuffle
```

CUDA and HIP/ROCm use the same sparse trainer and emit the same artifact:

```sh
make -C gpu cuda       # or: make -C gpu rocm
gpu/build/tinyshogi-train-nnue-cuda mixed.ndf1 model.nnue 5 0.01
```

The GPU trainer is a correctness/reference implementation using atomic sparse
updates and is suitable for a roughly 16 GB card. Larger-scale training can
later add gradient reduction and mixed precision without changing the dataset
or model format.

One generation can be automated with optional match gating:

```sh
python3 scripts/nnue_iteration.py --games 100 --match-games 100
python3 scripts/nnue_iteration.py --current nnue-runs/gen-001/candidate.nnue \
  --output-dir nnue-runs/gen-002 --games 100 --match-games 100
```

## Fuzzing

The rules parser and state transitions have a standalone libFuzzer harness.
It requires Clang with the libFuzzer runtime:

```sh
make -C fuzz
make -C fuzz run
```

The harness uses the seed corpus in `fuzz/corpus/` and enables AddressSanitizer
and UndefinedBehaviorSanitizer. To run longer, pass options directly to the
target, for example `fuzz/shogi-fuzz -max_total_time=300 fuzz/corpus`.

For local automation and LLM-assisted play, `tools/tinyshogi_mcp.py` provides
a dependency-free stdio MCP server. It exposes board queries, legal move
control, search, background self-play start/status/stop, and an LLM context
bridge. The bridge returns context to the connected client; it does not make
an undocumented external LLM call.

```sh
python3 tools/tinyshogi_mcp.py
```

Set `TINYSHOGI_ENGINE` when the engine is elsewhere. MCP clients should launch
the script as a stdio server and call `tools/list` followed by `tools/call`.

## License and provenance

The project is distributed under the Apache License 2.0 in `LICENSE`.

The shipped engine is a clean-room implementation and contains no GPL-sourced
code and no third-party runtime dependency. The rules tests are project-owned;
independent external validators may be used for test-only comparison, but
their source is not copied, linked, or distributed with this project. Any
future permissively licensed dependency or test fixture will be listed here
with its license and required attribution.
