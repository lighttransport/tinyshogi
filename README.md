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

The browser build links only the rules library (`src/shogi.c`) and does not
enable pthreads by default. It provides a small human-vs-human click-to-move
app in `web/`; select a piece and a highlighted destination, or select a
captured piece from a hand to make a drop. Every destination comes from the
engine's legal-move generator, including promotion and drop restrictions. The
generated files are written to `web/build/`.

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
```

Use `--temperature 0` for deterministic visit-max move selection. Games that
reach `--max-plies` without a terminal result are recorded as draws. The JSONL
format is versioned with `"version":1` and is intended for external training
pipelines.

The optional no-SDK CUDA handoff is documented in [cuda/README.md](cuda/README.md).
It uses a CUEW-style runtime loader and builds the CUDA probe with only `cc` and
`-ldl`; the normal CPU engine remains independent of CUDA.

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
