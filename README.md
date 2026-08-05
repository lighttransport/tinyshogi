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
