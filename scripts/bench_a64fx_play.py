#!/usr/bin/env python3
"""Benchmark persistent-USI neural MCTS on a stratified exact-play corpus."""

import argparse
import hashlib
import json
import random
import statistics
import subprocess
import sys
import time
from pathlib import Path


def run_selfplay(args, output):
    command = [str(args.engine), "--selfplay", "--games", str(args.games),
               "--simulations", str(args.generation_nodes), "--threads", "1",
               "--seed", str(args.seed), "--max-plies", "192", "--output", str(output),
               "--eval-model", str(args.model)]
    subprocess.run(command, check=True)


def stratify(records, per_phase, seed):
    phases = {"opening": [], "middlegame": [], "late": []}
    for record in records:
        ply = int(record.get("ply", -1))
        if ply < 0 or not isinstance(record.get("sfen"), str):
            continue
        phase = "opening" if ply <= 30 else "middlegame" if ply <= 80 else "late"
        phases[phase].append(record["sfen"])
    rng = random.Random(seed)
    selected = []
    for phase in ("opening", "middlegame", "late"):
        unique = list(dict.fromkeys(phases[phase]))
        rng.shuffle(unique)
        if len(unique) < per_phase:
            raise RuntimeError(f"need {per_phase} {phase} positions, found {len(unique)}")
        selected.extend({"phase": phase, "sfen": sfen} for sfen in unique[:per_phase])
    return selected


class Engine:
    def __init__(self, args):
        command = ["taskset", "-c", args.cpus, str(args.engine)] if args.cpus else [str(args.engine)]
        self.process = subprocess.Popen(command, stdin=subprocess.PIPE, stdout=subprocess.PIPE,
                                        stderr=subprocess.PIPE, universal_newlines=True, bufsize=1)
        self.send("usi")
        self.read_until("usiok")
        for name, value in (("Threads", args.threads), ("MaxTreeNodes", args.max_tree_nodes),
                            ("EvalModel", args.model), ("MCTSMode", "neural"),
                            ("LeafBatch", args.leaf_batch), ("A64FXMode", args.a64fx_mode)):
            self.send(f"setoption name {name} value {value}")
        self.send("isready")
        self.read_until("readyok")

    def send(self, command):
        self.process.stdin.write(command + "\n")
        self.process.stdin.flush()

    def read_until(self, prefix):
        lines = []
        while True:
            line = self.process.stdout.readline()
            if not line:
                error = self.process.stderr.read().strip()
                raise RuntimeError(f"engine exited while waiting for {prefix}: {error}")
            line = line.strip()
            lines.append(line)
            if line == prefix or line.startswith(prefix + " "):
                return lines

    def search(self, sfen, movetime_ms):
        self.send("position sfen " + sfen)
        started = time.monotonic()
        self.send(f"go movetime {movetime_ms}")
        lines = self.read_until("bestmove")
        wall_ms = (time.monotonic() - started) * 1000.0
        nodes = nps = elapsed = 0
        for line in lines:
            fields = line.split()
            if fields[:1] != ["info"]:
                continue
            for key, target in (("nodes", "nodes"), ("nps", "nps"), ("time", "elapsed")):
                if key in fields:
                    try:
                        value = int(fields[fields.index(key) + 1])
                    except (ValueError, IndexError):
                        continue
                    if target == "nodes": nodes = value
                    elif target == "nps": nps = value
                    else: elapsed = value
        best = lines[-1].split()[1]
        return {"nodes": nodes, "nps": nps, "time_ms": elapsed,
                "wall_ms": wall_ms, "bestmove": best}

    def close(self):
        if self.process.poll() is None:
            self.send("quit")
            self.process.wait(timeout=5)


def percentile(values, fraction):
    ordered = sorted(values)
    return ordered[min(len(ordered) - 1, int((len(ordered) - 1) * fraction))]


def main():
    root = Path(__file__).resolve().parents[1]
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--engine", type=Path, required=True)
    parser.add_argument("--model", type=Path, required=True)
    parser.add_argument("--work-dir", type=Path, default=root / "build/perf")
    parser.add_argument("--games", type=int, default=64)
    parser.add_argument("--generation-nodes", type=int, default=32)
    parser.add_argument("--positions-per-phase", type=int, default=32)
    parser.add_argument("--movetime-ms", type=int, default=1000)
    parser.add_argument("--threads", type=int, default=48)
    parser.add_argument("--max-tree-nodes", type=int, default=4_000_000)
    parser.add_argument("--cpus", default="12-59")
    parser.add_argument("--a64fx-mode", choices=("auto", "off"), default="auto")
    parser.add_argument("--leaf-batch", type=int, choices=range(1, 13), default=5)
    parser.add_argument("--seed", type=int, default=7)
    parser.add_argument("--regenerate", action="store_true")
    args = parser.parse_args()
    if not args.engine.is_file() or not args.model.is_file():
        parser.error("engine and model must exist")
    args.work_dir.mkdir(parents=True, exist_ok=True)
    raw = args.work_dir / "play-corpus-raw.jsonl"
    corpus_path = args.work_dir / "play-corpus.json"
    if args.regenerate or not raw.exists():
        run_selfplay(args, raw)
    records = [json.loads(line) for line in raw.read_text().splitlines() if line.strip()]
    corpus = stratify(records, args.positions_per_phase, args.seed)
    corpus_path.write_text(json.dumps(corpus, indent=2) + "\n")
    engine = Engine(args)
    results = []
    try:
        for index, item in enumerate(corpus):
            result = engine.search(item["sfen"], args.movetime_ms)
            result.update(item)
            results.append(result)
            print(f"{index + 1}/{len(corpus)} {item['phase']} nps={result['nps']}", file=sys.stderr)
    finally:
        engine.close()
    nps = [item["nps"] for item in results]
    overshoot = [max(0.0, item["wall_ms"] - args.movetime_ms) for item in results]
    summary = {
        "engine": str(args.engine), "model": str(args.model),
        "model_sha256": hashlib.sha256(args.model.read_bytes()).hexdigest(),
        "positions": len(results), "median_nps": int(statistics.median(nps)),
        "p10_nps": percentile(nps, 0.10), "min_nps": min(nps),
        "p99_wall_overshoot_ms": percentile(overshoot, 0.99),
        "max_wall_overshoot_ms": max(overshoot),
        "phase_median_nps": {phase: int(statistics.median(
            item["nps"] for item in results if item["phase"] == phase))
            for phase in ("opening", "middlegame", "late")},
    }
    (args.work_dir / "play-results.json").write_text(
        json.dumps({"summary": summary, "results": results}, indent=2) + "\n")
    print(json.dumps(summary, indent=2))


if __name__ == "__main__":
    main()
