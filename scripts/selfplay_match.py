#!/usr/bin/env python3
"""Reproducible USI matches with complete history, a referee, and audit records."""

import argparse
from collections import Counter
from concurrent.futures import ThreadPoolExecutor
import hashlib
import json
import os
import random
from pathlib import Path
import platform
import subprocess
import sys
import time

from usi_engine import Engine

PAIRED_OPENINGS = (
    (), ("7g7f", "3c3d"), ("2g2f", "8c8d"),
    ("7g7f", "8c8d", "2g2f", "3c3d"),
    ("7g7f", "3c3d", "6g6f", "8c8d"),
    ("7g7f", "3c3d", "2g2f", "8c8d"),
    ("7g7f", "8c8d", "6g6f", "3c3d"),
    ("2g2f", "3c3d", "7g7f", "8c8d"),
    ("7g7f", "3c3d", "9g9f", "9c9d"),
    ("7g7f", "3c3d", "5g5f", "5c5d"),
)


def sha256(path):
    digest = hashlib.sha256()
    with Path(path).open("rb") as stream:
        for block in iter(lambda: stream.read(1024 * 1024), b""):
            digest.update(block)
    return digest.hexdigest()


def query_sfen(engine, position, moves=None):
    engine.set_position(position, moves)
    engine.send("sfen")
    return engine.read_sfen()


def parse_args(argv=None):
    root = Path(__file__).resolve().parents[1]
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--tinyshogi", type=Path, default=root / "build/make/tinyshogi")
    parser.add_argument("--referee", type=Path, help="TinyShogi rules referee; defaults to candidate")
    parser.add_argument("--tinyshogi-eval-plugin", type=Path)
    parser.add_argument("--tinyshogi-nn-bin", type=Path)
    parser.add_argument("--tinyshogi-eval-model", type=Path)
    parser.add_argument("--yaneuraou", type=Path, default=root / "build/yaneuraou/YaneuraOu")
    parser.add_argument("--yaneuraou-eval-dir", type=Path)
    parser.add_argument("--yaneuraou-eval-model", type=Path)
    parser.add_argument("--opponent-eval-plugin", type=Path,
                        help="Use the same nn.bin when comparing two TinyShogi builds")
    parser.add_argument("--games", type=int, default=2)
    parser.add_argument("--tinyshogi-threads", type=int, default=1)
    parser.add_argument("--opponent-threads", type=int, default=1)
    parser.add_argument("--tinyshogi-search-mode", choices=("mcts", "alphabeta"), default="alphabeta")
    parser.add_argument("--tinyshogi-mcts-mode", choices=("auto", "neural", "rollout"), default="auto")
    parser.add_argument("--tinyshogi-uct-exploration", type=int, default=1414)
    parser.add_argument("--tinyshogi-rollout-depth", type=int, default=256)
    parser.add_argument("--tinyshogi-aspiration-window", type=int, default=2000)
    parser.add_argument("--tinyshogi-quiescence-margin", type=int, default=0)
    parser.add_argument("--tinyshogi-quiescence-depth", type=int, default=2)
    parser.add_argument("--tinyshogi-leaf-batch", type=int, default=5)
    parser.add_argument("--opponent-leaf-batch", type=int, default=5)
    parser.add_argument("--tinyshogi-option", action="append", default=[], metavar="NAME=VALUE")
    parser.add_argument("--nodes", type=int, default=1000)
    parser.add_argument("--tinyshogi-nodes", type=int)
    parser.add_argument("--tinyshogi-node-overrun", type=int, default=0,
                        help="Allow this percentage of extra nodes to finish a search iteration")
    parser.add_argument("--opponent-nodes", type=int)
    parser.add_argument("--tinyshogi-node-tolerance", type=float, default=0.05)
    parser.add_argument("--opponent-node-tolerance", type=float, default=0.05)
    parser.add_argument("--hash-mb", type=int, default=64)
    parser.add_argument("--fv-scale", type=int, default=20)
    parser.add_argument("--movetime-ms", type=int)
    parser.add_argument("--max-plies", type=int, default=512)
    parser.add_argument("--output", type=Path, default=root / "selfplay-tiny-yaneuraou.jsonl")
    parser.add_argument("--timeout", type=float, default=30.0)
    parser.add_argument("--seed", type=int, default=1)
    parser.add_argument("--paired-openings", action="store_true")
    parser.add_argument("--openings", type=Path, help="One SFEN per line; each position is played twice")
    parser.add_argument("--random-openings", action="store_true",
                        help="Deterministically sample openings using --seed")
    parser.add_argument("--opening-offset", type=int, default=0)
    parser.add_argument("--jobs", type=int, default=1)
    parser.add_argument("--reuse-processes", action="store_true",
                        help="Deprecated: processes are restarted for every game to isolate state")
    parser.add_argument("--strict", action="store_true",
                        help="Require the agreed shared-NNUE, equal-1000-node protocol")
    parser.add_argument("--verbose", action="store_true")
    return parser.parse_args(argv)


def validate_args(args):
    for field in ("games", "max_plies", "nodes", "tinyshogi_threads", "opponent_threads",
                  "jobs", "hash_mb"):
        if getattr(args, field) < 1:
            raise ValueError(f"{field} must be positive")
    for field in ("tinyshogi_nodes", "opponent_nodes", "movetime_ms"):
        if getattr(args, field) is not None and getattr(args, field) < 1:
            raise ValueError(f"{field} must be positive")
    if not 0 <= args.tinyshogi_node_overrun <= 10:
        raise ValueError("tinyshogi_node_overrun must be between 0 and 10")
    if args.timeout <= 0 or args.opening_offset < 0 or not 1 <= args.fv_scale <= 128:
        raise ValueError("invalid timeout, opening offset, or evaluation scale")
    if not 0 <= args.tinyshogi_node_tolerance <= 1 or not 0 <= args.opponent_node_tolerance <= 1:
        raise ValueError("node tolerances must be between 0 and 1")
    if not 0 <= args.tinyshogi_quiescence_depth <= 8:
        raise ValueError("quiescence depth must be between 0 and 8")
    if not 16 <= args.tinyshogi_aspiration_window <= 8000:
        raise ValueError("aspiration window must be between 16 and 8000")
    if not 0 <= args.tinyshogi_quiescence_margin <= 1000:
        raise ValueError("quiescence margin must be between 0 and 1000")
    if not 1 <= args.tinyshogi_uct_exploration <= 3000:
        raise ValueError("UCT exploration must be between 1 and 3000")
    if not 1 <= args.tinyshogi_rollout_depth <= 512:
        raise ValueError("rollout depth must be between 1 and 512")
    if not 1 <= args.tinyshogi_leaf_batch <= 12 or not 1 <= args.opponent_leaf_batch <= 12:
        raise ValueError("leaf batch must be between 1 and 12")
    args.referee = args.referee or args.tinyshogi
    for path in (args.tinyshogi, args.yaneuraou, args.referee):
        if not path.is_file() or not os.access(path, os.X_OK):
            raise ValueError(f"executable not found: {path}")
    if (args.paired_openings or args.openings) and args.games % 2:
        raise ValueError("paired matches need an even number of games")
    if args.strict:
        if (args.movetime_ms is not None or
                (args.tinyshogi_nodes or args.nodes) != 1000 or
                (args.opponent_nodes or args.nodes) != 1000 or
                args.tinyshogi_threads != 1 or args.opponent_threads != 1 or
                args.hash_mb != 64 or args.fv_scale != 20 or args.max_plies != 512 or
                args.tinyshogi_search_mode != "alphabeta" or
                args.tinyshogi_nn_bin is None or args.tinyshogi_eval_plugin is None or
                args.yaneuraou_eval_dir is None or args.openings is None or
                args.opponent_eval_plugin is not None):
            raise ValueError("strict matches require shared NNUE, paired SFENs, 1000 nodes, "
                             "one thread, 64 MiB hash, FV_SCALE 20 and 512 plies")
    if args.tinyshogi_nn_bin:
        if args.tinyshogi_eval_plugin is None:
            raise ValueError("nn.bin requires --tinyshogi-eval-plugin")
        if args.tinyshogi_eval_model or args.yaneuraou_eval_model:
            raise ValueError("nn.bin cannot be combined with a native EvalModel")
        if args.yaneuraou_eval_dir:
            other = args.yaneuraou_eval_dir / "nn.bin"
            if sha256(args.tinyshogi_nn_bin) != sha256(other):
                raise ValueError("engines must use identical nn.bin weights")
        elif args.opponent_eval_plugin is None:
            raise ValueError("shared nn.bin requires the opponent evaluation directory")


def load_openings(args):
    if args.openings:
        positions = [line.strip().removeprefix("sfen ") for line in
                     args.openings.read_text(encoding="utf-8-sig").splitlines()
                     if line.strip() and not line.lstrip().startswith("#")]
        if args.opening_offset + args.games // 2 > len(positions):
            raise ValueError("not enough distinct openings for this match")
        if args.random_openings:
            if args.games // 2 > len(positions):
                raise ValueError("not enough openings for random sample")
            selected = random.Random(args.seed).sample(positions, args.games // 2)
        else:
            selected = positions[args.opening_offset:args.opening_offset + args.games // 2]
        keys = [" ".join(sfen.split()[:3]) for sfen in selected]
        if len(set(keys)) != len(keys):
            raise ValueError("duplicate paired openings")
        return selected
    if args.strict:
        raise ValueError("strict matches require a held-out opening file")
    return [PAIRED_OPENINGS[(args.opening_offset + i) % len(PAIRED_OPENINGS)]
            if args.paired_openings else () for i in range((args.games + 1) // 2)]


def engine_options(args):
    tiny = {"Threads": args.tinyshogi_threads, "Seed": args.seed,
            "SearchMode": args.tinyshogi_search_mode, "MCTSMode": args.tinyshogi_mcts_mode,
            "UCTExploration": args.tinyshogi_uct_exploration,
            "RolloutDepth": args.tinyshogi_rollout_depth,
            "AspirationWindow": args.tinyshogi_aspiration_window,
            "QuiescenceMargin": args.tinyshogi_quiescence_margin,
            "QuiescenceDepth": args.tinyshogi_quiescence_depth, "USI_Hash": args.hash_mb,
            "RootPrepass": "true",
            "NullMove": "true",
            "NodeOverrun": args.tinyshogi_node_overrun,
            "MultiPV": 1, "PerpetualCheck": "on"}
    if args.tinyshogi_eval_plugin:
        tiny["EvalPlugin"] = args.tinyshogi_eval_plugin.resolve()
    if args.tinyshogi_eval_model:
        tiny.update(EvalModel=args.tinyshogi_eval_model.resolve(), MCTSMode="neural",
                    LeafBatch=args.tinyshogi_leaf_batch)
    protected = {"Threads", "SearchMode", "USI_Hash", "MultiPV", "PerpetualCheck",
                 "EvalPlugin", "EvalModel"}
    for item in args.tinyshogi_option:
        key, separator, value = item.partition("=")
        if not separator or not key or key in protected:
            raise ValueError(f"invalid or protected option override: {item}")
        tiny[key] = value
    other = {"Threads": args.opponent_threads, "USI_Hash": args.hash_mb, "MultiPV": 1}
    if args.opponent_eval_plugin:
        other.update(SearchMode="alphabeta", EvalPlugin=args.opponent_eval_plugin.resolve(),
                     Seed=args.seed, PerpetualCheck="on")
    elif args.yaneuraou_eval_model:
        other.update(EvalModel=args.yaneuraou_eval_model.resolve(), MCTSMode="neural",
                     LeafBatch=args.opponent_leaf_batch)
    else:
        other.update(USI_OwnBook="false", BookFile="no_book", USI_Ponder="false",
                     EnteringKingRule="CSARule27")
        if args.yaneuraou_eval_dir:
            other.update(EvalDir=args.yaneuraou_eval_dir.resolve(), FV_SCALE=args.fv_scale)
    return tiny, other


def play_game(args, game, opening, model_sha, options):
    engines = []
    try:
        environment = os.environ.copy()
        if args.tinyshogi_nn_bin:
            environment["YANEURAOU_NN_BIN"] = str(args.tinyshogi_nn_bin.resolve())
            environment["YANEURAOU_FV_SCALE"] = str(args.fv_scale)
        affinities = [None, None]
        if args.jobs > 1 and hasattr(os, "sched_getaffinity"):
            cpus = sorted(os.sched_getaffinity(0))
            slot = game % args.jobs
            width = args.tinyshogi_threads + args.opponent_threads
            for index, threads in enumerate((args.tinyshogi_threads, args.opponent_threads)):
                start = slot * width + (args.tinyshogi_threads if index else 0)
                affinities[index] = {cpus[(start + offset) % len(cpus)] for offset in range(threads)}
        tiny = Engine("tinyshogi", args.tinyshogi.resolve(), options[0], args.timeout,
                      environment, affinities[0])
        engines.append(tiny)
        other = Engine("YaneuraOu", args.yaneuraou.resolve(), options[1], args.timeout,
                       environment, affinities[1])
        engines.append(other)
        referee = Engine("referee", args.referee.resolve(), {}, args.timeout)
        engines.append(referee)
        for engine in engines:
            engine.new_game()
        colors = (tiny, other) if game % 2 == 0 else (other, tiny)
        moves = []
        records = []
        violations = []
        state = referee.status(opening, moves)
        initial_sfen = state["sfen"]
        result, reason = "draw", "ply_limit"
        budgets = {tiny: args.tinyshogi_nodes or args.nodes,
                   other: args.opponent_nodes or args.nodes}
        for ply in range(args.max_plies + 1):
            if state["result"] != "ongoing":
                result, reason = state["result"], state["reason"]
                break
            if ply == args.max_plies:
                break
            side = 0 if state["sfen"].split()[1] == "b" else 1
            current = colors[side]
            limit = f"movetime {args.movetime_ms}" if args.movetime_ms else f"nodes {budgets[current]}"
            move = current.bestmove(opening, limit, moves)
            nodes = current.last_nodes
            if not args.movetime_ms and (
                    (nodes is None and move not in ("resign", "win")) or
                    (nodes is not None and nodes > budgets[current] *
                     (1 + (args.tinyshogi_node_tolerance if current is tiny else
                           args.opponent_node_tolerance)))):
                violation = {"ply": ply, "engine": current.name,
                             "node_limit": budgets[current], "reported_nodes": nodes}
                violations.append(violation)
                if args.strict:
                    raise RuntimeError(f"node budget audit failed: {violation}")
            records.append({
                "version": 1, "type": "position", "game": game, "ply": ply,
                "sfen": state["sfen"], "side": "b" if side == 0 else "w",
                "move": move, "engine": current.name, "opening": args.opening_offset + game // 2,
                "node_limit": None if args.movetime_ms else budgets[current],
                "reported_nodes": nodes, "elapsed_ms": current.last_elapsed_ms,
                "search_info": current.last_info, "model_sha256": model_sha})
            if move == "win":
                if not state["declaration"]:
                    raise RuntimeError(f"{current.name} made an invalid declaration")
                result, reason = ("black" if side == 0 else "white"), "declaration"
                break
            if move == "resign":
                result, reason = ("white" if side == 0 else "black"), "resignation"
                break
            if move not in state["legal_moves"]:
                raise RuntimeError(f"{current.name} returned illegal move {move} at {state['sfen']}")
            moves.append(move)
            state = referee.status(opening, moves)
            if args.verbose:
                print(f"game {game} ply {ply + 1}: {current.name} {move}", flush=True)
        for record in records:
            record["result"] = result
        summary = {
            "version": 2, "game": game, "opening": args.opening_offset + game // 2,
            "initial_sfen": initial_sfen, "final_sfen": state["sfen"],
            "tinyshogi_side": "b" if game % 2 == 0 else "w", "result": result,
            "reason": reason, "plies": len(moves), "decisions": len(records),
            "node_violations": violations, "complete": True,
            "engine_cpu_affinity": [tiny.cpu_affinity, other.cpu_affinity],
            "engine_identity": [tiny.identity, other.identity]}
        return records, summary
    finally:
        for engine in reversed(engines):
            engine.close()


def main(argv=None):
    args = parse_args(argv)
    validate_args(args)
    openings = load_openings(args)
    options = engine_options(args)
    args.output.parent.mkdir(parents=True, exist_ok=True)
    summary_path = Path(str(args.output) + ".games.jsonl")
    manifest_path = Path(str(args.output) + ".manifest.json")
    for path in (args.output, summary_path, manifest_path):
        if path.exists():
            raise ValueError(f"refusing to overwrite existing experiment: {path}")
    model_sha = sha256(args.tinyshogi_nn_bin) if args.tinyshogi_nn_bin else None
    root = Path(__file__).resolve().parents[1]
    revision = subprocess.run(["git", "rev-parse", "HEAD"], cwd=root,
                              capture_output=True, text=True, check=True).stdout.strip()
    diff = subprocess.run(["git", "diff", "--binary"], cwd=root,
                          capture_output=True, check=True).stdout
    manifest = {
        "version": 3, "complete": False, "strict": args.strict,
        "created_unix": time.time(), "revision": revision,
        "tracked_diff_sha256": hashlib.sha256(diff).hexdigest(),
        "runner_sha256": {name: sha256(root / "scripts" / name)
                          for name in ("selfplay_match.py", "usi_engine.py", "match_gate.py")},
        "arguments": {key: str(value) if isinstance(value, Path) else value
                      for key, value in vars(args).items()},
        "engine_sha256": [sha256(args.tinyshogi), sha256(args.yaneuraou)],
        "referee_sha256": sha256(args.referee),
        "plugin_sha256": sha256(args.tinyshogi_eval_plugin) if args.tinyshogi_eval_plugin else None,
        "model_sha256": model_sha,
        "opponent_model_sha256": (sha256(args.yaneuraou_eval_dir / "nn.bin")
                                 if args.tinyshogi_nn_bin and args.yaneuraou_eval_dir else model_sha),
        "openings_sha256": sha256(args.openings) if args.openings else None,
        "engine_options": options, "platform": platform.platform(),
        "cpu_count": os.cpu_count(), "command": sys.argv,
        "node_tolerance": {"tinyshogi": args.tinyshogi_node_tolerance,
                           "YaneuraOu": args.opponent_node_tolerance},
        "tinyshogi_node_overrun": args.tinyshogi_node_overrun}
    manifest_path.write_text(json.dumps(manifest, indent=2, default=str) + "\n")
    results = []
    started = time.monotonic()
    try:
        with args.output.open("x") as positions, summary_path.open("x") as summaries:
            with ThreadPoolExecutor(max_workers=args.jobs) as pool:
                # Bounded batches allow a failed experiment to stop promptly.
                for start in range(0, args.games, args.jobs):
                    futures = [pool.submit(play_game, args, game, openings[game // 2], model_sha, options)
                               for game in range(start, min(start + args.jobs, args.games))]
                    for future in futures:
                        records, summary = future.result()
                        for record in records:
                            positions.write(json.dumps(record) + "\n")
                        summaries.write(json.dumps(summary) + "\n")
                        positions.flush()
                        summaries.flush()
                        results.append(summary)
                        print(f"game {summary['game'] + 1}/{args.games}: "
                              f"{summary['result']} ({summary['plies']} plies, {summary['reason']})",
                              flush=True)
        manifest["complete"] = True
    except BaseException as error:
        manifest["error"] = str(error)
        raise
    finally:
        manifest["completed_games"] = len(results)
        manifest["records_sha256"] = sha256(args.output) if args.output.exists() else None
        manifest["summaries_sha256"] = sha256(summary_path) if summary_path.exists() else None
        manifest["elapsed_seconds"] = time.monotonic() - started
        manifest["node_audit_passed"] = not any(item["node_violations"] for item in results)
        manifest_path.write_text(json.dumps(manifest, indent=2, default=str) + "\n")
    winners = Counter("draw" if item["result"] == "draw" else
                      "tinyshogi" if (item["result"] == "black") ==
                      (item["tinyshogi_side"] == "b") else "YaneuraOu" for item in results)
    print(json.dumps(dict(winners), sort_keys=True))


if __name__ == "__main__":
    main()
