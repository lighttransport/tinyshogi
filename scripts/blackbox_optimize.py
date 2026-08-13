#!/usr/bin/env python3
"""Black-box search-parameter optimization against an external USI engine."""

import argparse
import hashlib
import json
import subprocess
import sys
from pathlib import Path


DEFAULT_CANDIDATES = [
    {"name": "ab-q0", "search_mode": "alphabeta", "quiescence_depth": 0},
    {"name": "ab-q1", "search_mode": "alphabeta", "quiescence_depth": 1},
    {"name": "ab-q2", "search_mode": "alphabeta", "quiescence_depth": 2},
    {"name": "ab-q2-wide", "search_mode": "alphabeta", "quiescence_depth": 2,
     "aspiration_window": 512},
    {"name": "ab-q2-narrow", "search_mode": "alphabeta", "quiescence_depth": 2,
     "aspiration_window": 64},
    {"name": "ab-q2-no-margin", "search_mode": "alphabeta", "quiescence_depth": 2,
     "quiescence_margin": 0},
    {"name": "ab-q2-wide-margin", "search_mode": "alphabeta", "quiescence_depth": 2,
     "quiescence_margin": 240},
    {"name": "mcts-rollout", "search_mode": "mcts", "mcts_mode": "rollout",
     "uct_exploration": 1414, "rollout_depth": 128},
    {"name": "mcts-neural", "search_mode": "mcts", "mcts_mode": "neural",
     "uct_exploration": 1000, "rollout_depth": 128},
    {"name": "mcts-neural-wide", "search_mode": "mcts", "mcts_mode": "neural",
     "uct_exploration": 1800, "rollout_depth": 128},
]


def sha256(path):
    digest = hashlib.sha256()
    with path.open("rb") as stream:
        for block in iter(lambda: stream.read(1024 * 1024), b""):
            digest.update(block)
    return digest.hexdigest()


def run_candidate(args, candidate, output):
    command = [sys.executable, str(args.match_script),
               "--tinyshogi", str(args.tinyshogi.resolve()),
               "--tinyshogi-eval-plugin", str(args.tinyshogi_eval_plugin.resolve()),
               "--tinyshogi-nn-bin", str(args.nn_bin.resolve()),
               "--yaneuraou", str(args.yaneuraou.resolve()),
               "--yaneuraou-eval-dir", str(args.yaneuraou_eval_dir.resolve()),
               "--tinyshogi-search-mode", candidate.get("search_mode", "alphabeta"),
               "--tinyshogi-mcts-mode", candidate.get("mcts_mode", "auto"),
               "--tinyshogi-quiescence-depth",
               str(candidate.get("quiescence_depth", 2)),
               "--tinyshogi-uct-exploration", str(candidate.get("uct_exploration", 1414)),
               "--tinyshogi-rollout-depth", str(candidate.get("rollout_depth", 256)),
               "--tinyshogi-aspiration-window",
               str(candidate.get("aspiration_window", 2000)),
               "--tinyshogi-quiescence-margin",
               str(candidate.get("quiescence_margin", 0)),
               "--tinyshogi-threads", str(args.tinyshogi_threads),
               "--opponent-threads", str(args.opponent_threads),
               "--tinyshogi-nodes", str(args.tinyshogi_nodes),
               "--opponent-nodes", str(args.opponent_nodes),
               "--games", str(args.games), "--max-plies", str(args.max_plies),
               "--paired-openings", "--seed", str(args.seed),
               "--timeout", str(args.timeout), "--output", str(output)]
    subprocess.run(command, check=True)


def summarize(path, candidate):
    games = {}
    with path.open(encoding="utf-8") as stream:
        for line in stream:
            if line.strip():
                item = json.loads(line)
                games.setdefault(int(item["game"]), []).append(item)
    wins = draws = losses = 0
    for records in games.values():
        result = records[0].get("result", "draw")
        sides = {item["side"] for item in records
                 if item.get("engine") == "tinyshogi"}
        side = next(iter(sides), None) if len(sides) == 1 else None
        if result == "draw" or side is None:
            draws += 1
        elif (result == "black" and side == "b") or (result == "white" and side == "w"):
            wins += 1
        else:
            losses += 1
    count = wins + draws + losses
    return {"name": candidate["name"], "config": candidate, "games": count, "wins": wins,
            "draws": draws, "losses": losses,
            "win_rate": wins / count if count else 0.0,
            "score": (wins + draws / 2) / count if count else 0.0,
            "record": str(path)}


def main():
    root = Path(__file__).resolve().parents[1]
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--tinyshogi", type=Path, required=True)
    parser.add_argument("--tinyshogi-eval-plugin", type=Path, required=True)
    parser.add_argument("--nn-bin", type=Path, required=True)
    parser.add_argument("--yaneuraou", type=Path, required=True)
    parser.add_argument("--yaneuraou-eval-dir", type=Path, required=True)
    parser.add_argument("--match-script", type=Path, default=root / "scripts/selfplay_match.py")
    parser.add_argument("--games", type=int, default=10)
    parser.add_argument("--tinyshogi-nodes", type=int, default=1000)
    parser.add_argument("--opponent-nodes", type=int, default=512)
    parser.add_argument("--tinyshogi-threads", type=int, default=1)
    parser.add_argument("--opponent-threads", type=int, default=1)
    parser.add_argument("--max-plies", type=int, default=256)
    parser.add_argument("--timeout", type=float, default=30.0)
    parser.add_argument("--seed", type=int, default=1)
    parser.add_argument("--output-dir", type=Path, default=root / "optimization")
    parser.add_argument("--candidates", type=Path)
    args = parser.parse_args()
    for path in (args.tinyshogi, args.tinyshogi_eval_plugin, args.nn_bin,
                 args.yaneuraou, args.yaneuraou_eval_dir):
        if not path.exists():
            parser.error(f"path does not exist: {path}")
    candidates = DEFAULT_CANDIDATES if args.candidates is None else json.loads(
        args.candidates.read_text(encoding="utf-8"))
    args.output_dir.mkdir(parents=True, exist_ok=True)
    manifest = {"settings": {
                    "tinyshogi_nodes": args.tinyshogi_nodes,
                    "opponent_nodes": args.opponent_nodes,
                    "games": args.games,
                    "max_plies": args.max_plies,
                    "seed": args.seed,
                },
                "nn_bin": str(args.nn_bin.resolve()),
                "nn_sha256": sha256(args.nn_bin), "candidates": []}
    for candidate in candidates:
        output = args.output_dir / f"{candidate['name']}.jsonl"
        print(f"running {candidate['name']}", flush=True)
        valid = True
        error = None
        try:
            run_candidate(args, candidate, output)
        except subprocess.CalledProcessError as failure:
            valid = False
            error = f"match exited with status {failure.returncode}"
            print(f"candidate {candidate['name']} invalid: {error}", flush=True)
        result = summarize(output, candidate) if output.exists() else {
            "name": candidate["name"], "config": candidate, "games": 0,
            "wins": 0, "draws": 0, "losses": 0, "win_rate": 0.0,
            "score": 0.0, "record": str(output)}
        result["valid"] = valid and result["games"] == args.games
        if error is not None:
            result["error"] = error
        manifest["candidates"].append(result)
        print(json.dumps(result, sort_keys=True), flush=True)
    (args.output_dir / "results.json").write_text(
        json.dumps(manifest, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    valid_candidates = [item for item in manifest["candidates"] if item["valid"]]
    if valid_candidates:
        best = max(valid_candidates, key=lambda item: (item["wins"], item["score"]))
        print(f"best={best['name']} wins={best['wins']} score={best['score']:.3f}")
    else:
        print("best=none (all candidates invalid)")


if __name__ == "__main__":
    main()
