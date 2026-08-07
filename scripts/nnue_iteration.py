#!/usr/bin/env python3
"""Generate, train, and optionally gate one native NNUE generation."""

import argparse
import json
import subprocess
import sys
from collections import Counter
from pathlib import Path


def run(command):
    print("+", " ".join(map(str, command)), file=sys.stderr)
    subprocess.run([str(item) for item in command], check=True)


def main():
    root = Path(__file__).resolve().parents[1]
    parser = argparse.ArgumentParser()
    parser.add_argument("--engine", type=Path, default=root / "build/tinyshogi")
    parser.add_argument("--current", type=Path)
    parser.add_argument("--output-dir", type=Path, default=root / "nnue-runs/gen-001")
    parser.add_argument("--games", type=int, default=100)
    parser.add_argument("--simulations", type=int, default=256)
    parser.add_argument("--epochs", type=int, default=5)
    parser.add_argument("--match-games", type=int, default=100)
    parser.add_argument("--match-nodes", type=int, default=256)
    parser.add_argument("--seed", type=int, default=7)
    args = parser.parse_args()
    if args.games < 1 or args.simulations < 1 or args.epochs < 1 or args.match_games < 2:
        parser.error("games, simulations, epochs, and match-games must be positive")
    if not args.engine.is_file():
        parser.error(f"engine not found: {args.engine}")
    if args.current is not None and not args.current.is_file():
        parser.error(f"current model not found: {args.current}")
    args.output_dir.mkdir(parents=True, exist_ok=True)
    raw = args.output_dir / "selfplay.jsonl"
    data = args.output_dir / "selfplay.ndf1"
    candidate = args.output_dir / "candidate.nnue"
    run([args.engine, "--selfplay", "--games", args.games, "--simulations", args.simulations,
         "--threads", 1, "--seed", args.seed, "--output", raw] +
        (["--eval-model", args.current] if args.current else []))
    run([sys.executable, root / "tools/prepare_nnue.py", raw, "-o", data, "--shuffle", "--seed", args.seed])
    run(["make", "-C", root / "cpu", "train-nnue"])
    run([root / "cpu/train_nnue", data, candidate, args.epochs, "0.01"])
    if args.current is None:
        print(f"initial NNUE generation written to {candidate}")
        return 0
    match = args.output_dir / "match.jsonl"
    run([sys.executable, root / "scripts/selfplay_match.py", "--games", args.match_games,
         "--nodes", args.match_nodes, "--tinyshogi", args.engine, "--yaneuraou", args.engine,
         "--tinyshogi-eval-model", candidate, "--yaneuraou-eval-model", args.current,
         "--output", match])
    results = {}
    with match.open(encoding="utf-8") as source:
        for line in source:
            record = json.loads(line)
            results[record["game"]] = record["result"]
    candidate_results = []
    for game, result in results.items():
        if result == "draw":
            candidate_results.append("draw")
        elif (result == "black") == (game % 2 == 0):
            candidate_results.append("candidate")
        else:
            candidate_results.append("current")
    summary = Counter(candidate_results)
    print("match:", dict(summary))
    if summary["candidate"] <= summary["current"]:
        print("candidate rejected: it did not win more games than the current model", file=sys.stderr)
        return 1
    print(f"candidate accepted: {candidate}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
