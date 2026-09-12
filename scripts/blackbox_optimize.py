#!/usr/bin/env python3
"""Development-only search-parameter experiments; never consumes the held-out split."""

import argparse
import json
from pathlib import Path
import re
import subprocess
import sys

from match_gate import bootstrap_interval, load_match, paired_counts, summarize
from selfplay_match import sha256
from strength_protocol import validate_tuning_openings, fatal_violations

DEFAULT_CANDIDATES = [
    {"name": "promoted-q4", "policy": "selective", "quiescence_depth": 4,
     "transposition_history": "shallow", "quiescence_history": True,
     "quiescence_pruning": True, "completed_results": True, "bucket_hash": True,
     "recaptures": False},
    {"name": "classic-q2", "policy": "classic", "quiescence_depth": 2},
    {"name": "ordered-q1", "policy": "ordered", "quiescence_depth": 1},
    {"name": "ordered-q2", "policy": "ordered", "quiescence_depth": 2},
    {"name": "ordered-q2-asp512", "policy": "ordered", "aspiration_window": 512},
    {"name": "selective-q2", "policy": "selective", "quiescence_depth": 2},
]
for candidate in DEFAULT_CANDIDATES:
    for feature in ("completed_results", "bucket_hash", "recaptures", "root_reductions",
                    "quiescence_history", "quiescence_pruning"):
        candidate.setdefault(feature, False)


def run_candidate(args, candidate, output):
    command = [sys.executable, "-B", str(args.match_script),
               "--tinyshogi", str(args.tinyshogi.resolve()),
               "--tinyshogi-eval-plugin", str(args.tinyshogi_eval_plugin.resolve()),
               "--tinyshogi-nn-bin", str(args.nn_bin.resolve()),
               "--yaneuraou", str(args.yaneuraou.resolve()),
               "--yaneuraou-eval-dir", str(args.yaneuraou_eval_dir.resolve()),
               "--tinyshogi-search-mode", candidate.get("search_mode", "alphabeta"),
               "--tinyshogi-mcts-mode", candidate.get("mcts_mode", "auto"),
               "--tinyshogi-option", "AlphaBetaPolicy=" + candidate.get("policy", "ordered"),
               "--tinyshogi-option", "QuiescenceChecks=" +
                    str(candidate.get("quiescence_checks", True)).lower(),
               "--tinyshogi-option", "QuiescenceHash=" +
                    str(candidate.get("quiescence_hash", True)).lower(),
               "--tinyshogi-option", "RootUpdates=" + candidate.get("root_updates", "partial"),
               "--tinyshogi-option", "TranspositionHistory=" + candidate.get("transposition_history", "exact"),
               "--tinyshogi-quiescence-depth", str(candidate.get("quiescence_depth", 2)),
               "--tinyshogi-uct-exploration", str(candidate.get("uct_exploration", 1414)),
               "--tinyshogi-rollout-depth", str(candidate.get("rollout_depth", 256)),
               "--tinyshogi-aspiration-window", str(candidate.get("aspiration_window", 2000)),
               "--tinyshogi-quiescence-margin", str(candidate.get("quiescence_margin", 0)),
               "--tinyshogi-node-overrun", str(candidate.get("node_overrun", 0)),
               "--tinyshogi-threads", str(args.tinyshogi_threads),
               "--opponent-threads", str(args.opponent_threads),
               "--tinyshogi-nodes", str(args.tinyshogi_nodes),
               "--opponent-nodes", str(args.opponent_nodes),
               "--games", str(args.games), "--max-plies", str(args.max_plies),
               "--openings", str(args.openings.resolve()),
               "--opening-offset", str(args.opening_offset), "--jobs", str(args.jobs),
               "--fv-scale", str(args.fv_scale), "--hash-mb", "64", "--seed", str(args.seed),
               "--timeout", str(args.timeout), "--output", str(output)]
    if "null_move" in candidate:
        command += ["--tinyshogi-option", "NullMove=" + str(candidate["null_move"]).lower()]
    if "root_move_limit" in candidate:
        command += ["--tinyshogi-option", "RootMoveLimit=" + str(candidate["root_move_limit"])]
    if candidate.get("random_openings", False):
        command.append("--random-openings")
    for key, option in (("recaptures", "QuiescenceRecaptures"),
                        ("root_reductions", "RootReductions"), ("quiescence_history", "QuiescenceHistory"),
                        ("quiescence_pruning", "QuiescencePruning"),
                        ("bucket_hash", "BucketHash"), ("completed_results", "CompletedResults")):
        if key in candidate:
            command += ["--tinyshogi-option", option + "=" + str(candidate[key]).lower()]
    if args.protocol:
        command += ["--protocol", str(args.protocol.resolve())]
    elif not args.diagnostic:
        command.append("--strict")
    subprocess.run(command, check=True)


def main():
    root = Path(__file__).resolve().parents[1]
    parser = argparse.ArgumentParser(description=__doc__)
    for name in ("tinyshogi", "tinyshogi-eval-plugin", "nn-bin", "yaneuraou", "yaneuraou-eval-dir"):
        parser.add_argument("--" + name, type=Path, required=True)
    parser.add_argument("--match-script", type=Path, default=root / "scripts/selfplay_match.py")
    parser.add_argument("--openings", type=Path, default=root / "runs/strength/openings/development.sfens")
    parser.add_argument("--opening-offset", type=int, default=0)
    parser.add_argument("--jobs", type=int, default=1)
    parser.add_argument("--games", type=int, default=100)
    parser.add_argument("--tinyshogi-nodes", type=int, default=1000)
    parser.add_argument("--opponent-nodes", type=int, default=1000)
    parser.add_argument("--tinyshogi-threads", type=int, default=1)
    parser.add_argument("--opponent-threads", type=int, default=1)
    parser.add_argument("--fv-scale", type=int, default=20)
    parser.add_argument("--max-plies", type=int, default=512)
    parser.add_argument("--timeout", type=float, default=30)
    parser.add_argument("--seed", type=int, default=1)
    parser.add_argument("--output-dir", type=Path, default=root / "optimization")
    parser.add_argument("--candidates", type=Path)
    parser.add_argument("--protocol", type=Path)
    parser.add_argument("--diagnostic", action="store_true",
                        help="Continue despite reported node overruns; results are never target passes")
    args = parser.parse_args()
    validate_tuning_openings(args.openings, args.protocol)
    candidates = DEFAULT_CANDIDATES if args.candidates is None else json.loads(args.candidates.read_text())
    names = [candidate["name"] for candidate in candidates]
    if len(set(names)) != len(names) or any(not re.fullmatch(r"[A-Za-z0-9_-]+", name) for name in names):
        parser.error("candidate names must be unique and contain only letters, digits, hyphens or underscores")
    args.output_dir.mkdir(parents=True, exist_ok=True)
    report_path = args.output_dir / "results.json"
    outputs = [args.output_dir / (name + ".jsonl") for name in names]
    if report_path.exists() or any(Path(str(path) + suffix).exists()
                                  for path in outputs for suffix in ("", ".manifest.json", ".games.jsonl")):
        parser.error("refusing to overwrite an existing experiment")
    report = {"diagnostic_only": args.diagnostic, "target_accepted": False,
              "settings": vars(args), "model_sha256": sha256(args.nn_bin),
              "openings_sha256": sha256(args.openings), "candidates": []}
    for candidate, output in zip(candidates, outputs):
        result = {"name": candidate["name"], "config": candidate, "record": str(output), "complete": False}
        try:
            run_candidate(args, candidate, output)
            _, games, violations, _, _ = load_match(output)
            result.update(summarize(games), complete=True, node_violations=len(violations),
                          node_audit_passed=not fatal_violations(violations, bool(args.protocol)),
                          win_rate_95_interval=bootstrap_interval(paired_counts(games)))
        except (subprocess.CalledProcessError, ValueError, OSError, KeyError) as error:
            result["error"] = str(error)
        report["candidates"].append(result)
        report_path.write_text(json.dumps(report, indent=2, default=str) + "\n")
        print(json.dumps(result), flush=True)
    eligible = [result for result in report["candidates"]
                if result["complete"] and (args.diagnostic or result["node_audit_passed"])]
    if eligible:
        best = max(eligible, key=lambda result: result["win_rate"])
        print("development best=" + best["name"] +
              "; selection is exploratory, not evidence of held-out strength")
    else:
        print("best=none (no completed eligible matches)")


if __name__ == "__main__":
    main()
