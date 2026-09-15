#!/usr/bin/env python3
# SPDX-License-Identifier: Apache-2.0
"""Separate DL strength protocol: frozen artifacts, 500 color pairs, score CI.

FukauraOu and dr2_exhi are external black-box opponents, never dependencies.
The operator supplies legally obtained artifacts and their build provenance.
"""
import argparse
from contextlib import ExitStack
import json
import math
import os
from pathlib import Path
import random
import re
import subprocess
import sys
import time

from dl_campaign import ROOT, atomic_json, checkpoint_info, sha256
sys.path.insert(0, str(ROOT / "scripts"))
from usi_engine import Engine


def positions(path, count=None):
    lines = [line.strip() for line in Path(path).read_text().splitlines() if line.strip()]
    keys = [" ".join(line.split()[:3]) for line in lines]
    if (not lines or count is not None and len(lines) != count or len(set(keys)) != len(keys)
            or any(len(line.split()) != 4 or line.split()[1] not in ("b", "w") for line in lines)):
        raise ValueError("invalid/duplicate opening set")
    return lines, set(keys)


def score_interval(games, samples=10000, seed=7):
    pairs = {}
    ids = set()
    for game in games:
        if (game["id"] in ids or game["result"] not in ("black", "white", "draw")
                or game["candidate_side"] not in ("b", "w")):
            raise ValueError("invalid or duplicate game")
        ids.add(game["id"])
        pairs.setdefault(game["opening"], []).append(game)
    scores, seen_positions = [], set()
    for pair in pairs.values():
        if (len(pair) != 2 or {g["candidate_side"] for g in pair} != {"b", "w"}
                or pair[0]["initial_sfen"] != pair[1]["initial_sfen"]):
            raise ValueError("incomplete color pair")
        position = " ".join(pair[0]["initial_sfen"].split()[:3])
        if position in seen_positions:
            raise ValueError("duplicate position across opening pairs")
        seen_positions.add(position)
        scores.append(sum(.5 if g["result"] == "draw" else float(
            (g["result"] == "black") == (g["candidate_side"] == "b")) for g in pair)/2)
    if not scores:
        raise ValueError("no complete pairs")
    rng = random.Random(seed)
    boot = sorted(sum(rng.choices(scores, k=len(scores)))/len(scores) for _ in range(samples))
    score = sum(scores)/len(scores)
    ci = [boot[int(.025*samples)], boot[min(samples-1, int(.975*samples))]]
    elo = None if score in (0, 1) else 400*math.log10(score/(1-score))
    return dict(games=len(games), pairs=len(scores), score=score, score_ci95=ci, elo=elo,
                threshold=.36, passed=len(scores) == 500 and ci[0] >= .36)


def artifact(path):
    path = Path(path).resolve()
    return dict(path=str(path), sha256=sha256(path))


def freeze(args):
    if args.lock.exists():
        raise ValueError("refusing to replace a frozen protocol")
    _, acceptance = positions(args.openings, 500)
    _, development = positions(args.development_openings)
    if acceptance & development:
        raise ValueError("acceptance/development openings overlap")
    checkpoint_info(args.model)
    if (not re.fullmatch(r"717da87[0-9a-f]{33}", args.opponent_commit)
            or args.opponent_model.name != "model-dr2_exhi.onnx"):
        raise ValueError("expected FukauraOu v9.40 commit and model-dr2_exhi.onnx")
    if not args.gpu_uuid.startswith("GPU-"):
        raise ValueError("pin a physical CUDA GPU UUID")
    cores = list(map(int, args.cpu_set.split(",")))
    if len(set(cores)) != 8 or any(c < 0 for c in cores):
        raise ValueError("pin exactly eight CPU IDs")
    lock = dict(version=1, created_unix=time.time(), movetime_ms=1000, max_plies=512,
                pairs=500, lower_score=.36, bootstrap_samples=10000, bootstrap_seed=7,
                opponent_release="v9.40", opponent_commit=args.opponent_commit,
                gpu_uuid=args.gpu_uuid, cpu_set=cores, provenance=args.provenance,
                provenance_status="operator supplied; hashes pin artifacts, not upstream authenticity",
                runner=artifact(__file__), transport=artifact(ROOT / "scripts/usi_engine.py"))
    for key in ("engine", "model", "opponent", "opponent_model", "openings", "development_openings"):
        lock[key] = artifact(getattr(args, key))
    lock["candidate_options"] = dict(DLBackend="cuda", DLDevice=0, DLBatchSize=32,
                                      DLModel=lock["model"]["path"], SearchMode="puct", Threads=8, Seed=1)
    # Public v9.00+ USI interface, checked against the actual binary at startup.
    lock["opponent_options"] = dict(EvalDir=str(args.opponent_model.resolve().parent),
        DNN_Model=args.opponent_model.name, DNN_Batch_Size=32, UCT_Threads=8,
        Max_GPU=1, BookFile="no_book", USI_Ponder="false")
    atomic_json(args.lock, lock)


def load_lock(path):
    lock = json.loads(Path(path).read_text())
    if (lock["version"] != 1 or lock["movetime_ms"] != 1000 or lock["max_plies"] != 512
            or lock["pairs"] != 500 or lock["lower_score"] != .36):
        raise ValueError("unexpected DL protocol")
    expected_candidate = dict(DLBackend="cuda", DLDevice=0, DLBatchSize=32,
                              DLModel=lock["model"]["path"], SearchMode="puct", Threads=8, Seed=1)
    model_path = Path(lock["opponent_model"]["path"])
    expected_opponent = dict(EvalDir=str(model_path.parent), DNN_Model="model-dr2_exhi.onnx",
                            DNN_Batch_Size=32, UCT_Threads=8, Max_GPU=1,
                            BookFile="no_book", USI_Ponder="false")
    if (lock["candidate_options"] != expected_candidate or lock["opponent_options"] != expected_opponent
            or model_path.name != "model-dr2_exhi.onnx" or len(set(lock["cpu_set"])) != 8
            or lock["opponent_release"] != "v9.40"
            or not re.fullmatch(r"717da87[0-9a-f]{33}", lock["opponent_commit"])):
        raise ValueError("modified DL match options/provenance")
    for key in ("engine", "model", "opponent", "opponent_model", "openings",
                "development_openings", "runner", "transport"):
        item = lock[key]
        if sha256(item["path"]) != item["sha256"]:
            raise ValueError(f"modified frozen artifact: {key}")
    _, acceptance = positions(lock["openings"]["path"], 500)
    _, development = positions(lock["development_openings"]["path"])
    if acceptance & development:
        raise ValueError("overlapping splits")
    return lock


def play_game(engines, referee, opening, opening_id, candidate_side, game_id, milliseconds=1000):
    for engine in engines:
        engine.new_game()
    moves, decisions = [], []
    while True:
        state = referee.status(opening, moves)  # retain all history, never SFEN-only updates
        result = state["result"]
        if result != "ongoing":
            reason = state["reason"]
            break
        if len(moves) >= 512:
            result, reason = "draw", "ply_limit"
            break
        side = state["sfen"].split()[1]
        index = 0 if side == candidate_side else 1
        engine = engines[index]
        move = engine.bestmove(opening, f"movetime {milliseconds}", moves)
        # A time overrun invalidates the experiment, never becomes training data
        # or an artificial forfeit. 100 ms is transport/dispatch tolerance.
        if engine.last_elapsed_ms > milliseconds+100:
            raise RuntimeError(f"move-time overrun: {engine.name}: {engine.last_elapsed_ms:.3f} ms")
        decisions.append(dict(engine=index, move=move, elapsed_ms=engine.last_elapsed_ms,
                              search_info=engine.last_info.copy()))
        if move == "resign":
            result, reason = ("white" if side == "b" else "black"), "resign"
            break
        if move == "win":
            if not state["declaration"]:
                raise RuntimeError("illegal declaration claim")
            result, reason = ("black" if side == "b" else "white"), "declaration"
            break
        if move not in state["legal_moves"]:
            raise RuntimeError(f"illegal move: {engine.name}: {move}")
        moves.append(move)
    return dict(id=game_id, opening=opening_id, initial_sfen=opening, candidate_side=candidate_side,
                result=result, reason=reason, moves=moves, decisions=decisions)


def run_match(args):
    lock = load_lock(args.lock)
    output = args.output.resolve()
    manifest_path = Path(str(output)+".manifest.json")
    lock_hash = sha256(args.lock)
    previous = []
    if output.exists():
        manifest = json.loads(manifest_path.read_text())
        if manifest["lock_sha256"] != lock_hash or manifest["complete"]:
            raise ValueError("result belongs to another protocol or is already complete")
        previous = [json.loads(line) for line in output.read_text().splitlines()]
        if [g["id"] for g in previous] != list(range(len(previous))):
            raise ValueError("invalid resume transcript")
    else:
        if manifest_path.exists():
            raise ValueError("manifest exists without its transcript")
        manifest = dict(version=1, complete=False, lock_sha256=lock_hash, created_unix=time.time())
    gpu = subprocess.check_output(["nvidia-smi", "-i", lock["gpu_uuid"],
        "--query-gpu=uuid,name,driver_version", "--format=csv,noheader"], text=True).strip()
    if "5060 Ti" not in gpu:
        raise ValueError("formal acceptance requires the pinned RTX 5060 Ti")
    manifest["gpu"] = gpu
    atomic_json(manifest_path, manifest)
    openings, _ = positions(lock["openings"]["path"], 500)
    env = os.environ.copy()
    env["CUDA_VISIBLE_DEVICES"] = lock["gpu_uuid"]
    with ExitStack() as stack:
        engines = []
        for key, options in (("engine", lock["candidate_options"]), ("opponent", lock["opponent_options"])):
            engine = Engine(key, lock[key]["path"], options, 300, env, lock["cpu_set"])
            stack.callback(engine.close)
            engines.append(engine)
        referee = Engine("referee", lock["engine"]["path"], {}, 10)
        stack.callback(referee.close)
        manifest["identities"] = [e.identity for e in engines]
        atomic_json(manifest_path, manifest)
        # Warm-up only on startpos, not on any held-out opening. No go ponder.
        for e in engines:
            e.bestmove([], "nodes 32")
            e.timeout = 10
        with output.open("a") as stream:
            for game_id in range(len(previous), 1000):
                game = play_game(engines, referee, openings[game_id//2], game_id//2,
                                 "b" if game_id%2 == 0 else "w", game_id)
                stream.write(json.dumps(game)+"\n")
                stream.flush()
                os.fsync(stream.fileno())
                previous.append(game)
                print(json.dumps(dict(game=game_id, result=game["result"])), flush=True)
    manifest.update(complete=True, games_sha256=sha256(output), completed_unix=time.time(),
                    summary=score_interval(previous))
    atomic_json(manifest_path, manifest)
    print(json.dumps(manifest["summary"]))


def main():
    p = argparse.ArgumentParser(description=__doc__)
    sub = p.add_subparsers(dest="command", required=True)
    f = sub.add_parser("freeze")
    f.add_argument("--lock", type=Path, required=True)
    for key in ("engine", "model", "opponent", "opponent-model", "openings", "development-openings"):
        f.add_argument("--"+key, type=Path, required=True)
    f.add_argument("--opponent-commit", required=True)
    f.add_argument("--gpu-uuid", required=True)
    f.add_argument("--cpu-set", required=True)
    f.add_argument("--provenance", required=True, help="operator's source/build/weight-terms record")
    r = sub.add_parser("run")
    r.add_argument("--lock", type=Path, required=True)
    r.add_argument("--output", type=Path, required=True)
    args = p.parse_args()
    freeze(args) if args.command == "freeze" else run_match(args)


if __name__ == "__main__":
    main()
