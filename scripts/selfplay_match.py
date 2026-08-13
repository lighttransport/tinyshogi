#!/usr/bin/env python3
"""Run a small USI self-play match between tinyshogi and YaneuraOu."""

import argparse
from collections import Counter
import hashlib
import json
import os
import re
import selectors
import subprocess
import sys
from pathlib import Path


PAIRED_OPENINGS = (
    (),
    ("7g7f", "3c3d"),
    ("2g2f", "8c8d"),
    ("7g7f", "8c8d", "2g2f", "3c3d"),
    ("7g7f", "3c3d", "6g6f", "8c8d"),
    ("7g7f", "3c3d", "2g2f", "8c8d"),
    ("7g7f", "8c8d", "6g6f", "3c3d"),
    ("2g2f", "3c3d", "7g7f", "8c8d"),
    ("7g7f", "3c3d", "9g9f", "9c9d"),
    ("7g7f", "3c3d", "5g5f", "5c5d"),
)


class Engine:
    def __init__(self, name, path, options, timeout, environment=None):
        self.name = name
        self.path = str(path)
        self.timeout = timeout
        self.last_nodes = None
        self.process = subprocess.Popen(
            [self.path], stdin=subprocess.PIPE, stdout=subprocess.PIPE,
            stderr=subprocess.PIPE, bufsize=0, env=environment
        )
        self.selector = selectors.DefaultSelector()
        self.selector.register(self.process.stdout, selectors.EVENT_READ)
        self.send("usi")
        self.read_until("usiok")
        for key, value in options.items():
            self.send(f"setoption name {key} value {value}")
        self.send("isready")
        self.read_until("readyok")

    def send(self, command):
        if self.process.poll() is not None:
            raise RuntimeError(f"{self.name} exited with status {self.process.returncode}")
        self.process.stdin.write((command + "\n").encode())
        self.process.stdin.flush()

    def read_until(self, marker):
        while True:
            events = self.selector.select(self.timeout)
            if not events:
                raise RuntimeError(f"timeout waiting for {marker} from {self.name}")
            line = self.process.stdout.readline()
            if line == b"":
                error = self.process.stderr.read().decode(errors="replace").strip()
                detail = f": {error}" if error else ""
                raise RuntimeError(f"{self.name} closed stdout{detail}")
            line = line.decode(errors="replace").strip()
            match = re.search(r"(?:^| )nodes (\d+)(?: |$)", line)
            if match:
                self.last_nodes = int(match.group(1))
            if "evaluator load failed" in line or "NNUE model load failed" in line:
                raise RuntimeError(f"{self.name}: {line}")
            if line == marker or line.startswith(marker + " "):
                return line

    def read_sfen(self):
        while True:
            events = self.selector.select(self.timeout)
            if not events:
                raise RuntimeError(f"timeout waiting for sfen from {self.name}")
            line = self.process.stdout.readline()
            if line == b"":
                raise RuntimeError(f"{self.name} closed stdout while returning sfen")
            line = line.decode(errors="replace").strip()
            if line.count(" ") >= 3 and "/" in line:
                return line

    def set_position(self, position, moves=None):
        if isinstance(position, str):
            command = "position sfen " + position
        else:
            command = "position startpos"
            if position:
                command += " moves " + " ".join(position)
        if moves:
            command += " moves " + " ".join(moves)
        self.send(command)

    def bestmove(self, position, limit):
        self.last_nodes = None
        self.set_position(position)
        self.send("go " + limit)
        line = self.read_until("bestmove")
        fields = line.split()
        if len(fields) < 2:
            raise RuntimeError(f"malformed bestmove from {self.name}: {line}")
        return fields[1]

    def new_game(self):
        self.send("usinewgame")

    def close(self):
        if self.process.poll() is None:
            try:
                self.send("quit")
                self.process.wait(timeout=2)
            except (BrokenPipeError, subprocess.TimeoutExpired):
                self.process.kill()
        self.selector.close()


def query_sfen(engine, position, moves=None):
    engine.set_position(position, moves)
    engine.send("sfen")
    return engine.read_sfen()


def parse_args():
    root = Path(__file__).resolve().parents[1]
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--tinyshogi", type=Path, default=root / "build/tinyshogi")
    parser.add_argument("--tinyshogi-eval-plugin", type=Path,
                        help="EvalPlugin shared library for TinyShogi")
    parser.add_argument("--tinyshogi-nn-bin", type=Path,
                        help="nn.bin passed to the native TinyShogi evaluator plugin")
    parser.add_argument("--tinyshogi-eval-model", type=Path,
                        help="native EvalModel checkpoint for TinyShogi")
    parser.add_argument("--yaneuraou", type=Path, default=root / "build/yaneuraou/YaneuraOu-material")
    parser.add_argument("--yaneuraou-eval-dir", type=Path,
                        help="EvalDir option for YaneuraOu-compatible engines")
    parser.add_argument("--yaneuraou-eval-model", type=Path,
                        help="EvalModel checkpoint when the opponent is TinyShogi")
    parser.add_argument("--games", type=int, default=2)
    parser.add_argument("--tinyshogi-threads", type=int, default=1)
    parser.add_argument("--tinyshogi-search-mode", choices=("mcts", "alphabeta"),
                        default="mcts",
                        help="Search mode for TinyShogi")
    parser.add_argument("--tinyshogi-mcts-mode", choices=("auto", "neural", "rollout"),
                        default="auto", help="TinyShogi MCTS evaluator policy")
    parser.add_argument("--tinyshogi-uct-exploration", type=int, default=1414)
    parser.add_argument("--tinyshogi-rollout-depth", type=int, default=256)
    parser.add_argument("--tinyshogi-aspiration-window", type=int, default=2000)
    parser.add_argument("--tinyshogi-quiescence-margin", type=int, default=0)
    parser.add_argument("--tinyshogi-quiescence-depth", type=int, default=2,
                        help="TinyShogi tactical quiescence depth")
    parser.add_argument("--opponent-threads", type=int, default=1)
    parser.add_argument("--tinyshogi-leaf-batch", type=int, default=5)
    parser.add_argument("--opponent-leaf-batch", type=int, default=5)
    parser.add_argument("--nodes", type=int, default=256)
    parser.add_argument("--tinyshogi-nodes", type=int,
                        help="Override the node limit for TinyShogi")
    parser.add_argument("--opponent-nodes", type=int,
                        help="Override the node limit for the opponent")
    parser.add_argument("--movetime-ms", type=int)
    parser.add_argument("--max-plies", type=int, default=512)
    parser.add_argument("--output", type=Path, default=root / "selfplay-tiny-yaneuraou.jsonl")
    parser.add_argument("--timeout", type=float, default=30.0)
    parser.add_argument("--seed", type=int, default=1)
    parser.add_argument("--paired-openings", action="store_true",
                        help="Use deterministic two-game opening pairs")
    parser.add_argument("--opening-offset", type=int, default=0,
                        help="Starting paired-opening index")
    parser.add_argument("--reuse-processes", action="store_true",
                        help="Reuse engine processes and transposition state between games")
    parser.add_argument("--verbose", action="store_true",
                        help="Print every move while the match is running")
    return parser.parse_args()


def main():
    args = parse_args()
    if (args.games < 1 or args.max_plies < 1 or args.nodes < 1 or
            args.tinyshogi_threads < 1 or args.opponent_threads < 1 or
            not 0 <= args.tinyshogi_quiescence_depth <= 8 or
            not 1 <= args.tinyshogi_uct_exploration <= 3000 or
            not 1 <= args.tinyshogi_rollout_depth <= 512 or
            not 16 <= args.tinyshogi_aspiration_window <= 2000 or
            not 0 <= args.tinyshogi_quiescence_margin <= 1000 or
            not 0 <= args.opening_offset < len(PAIRED_OPENINGS) or
            not 1 <= args.tinyshogi_leaf_batch <= 12 or
            not 1 <= args.opponent_leaf_batch <= 12):
        raise SystemExit("games, max-plies, nodes, and thread counts must be positive")
    if ((args.tinyshogi_nodes is not None and args.tinyshogi_nodes < 1) or
            (args.opponent_nodes is not None and args.opponent_nodes < 1)):
        raise SystemExit("per-engine node limits must be positive")
    if args.movetime_ms is not None and args.movetime_ms < 1:
        raise SystemExit("movetime-ms must be positive")
    for path in (args.tinyshogi, args.yaneuraou):
        if not path.is_file() or not os.access(path, os.X_OK):
            raise SystemExit(f"executable not found or not executable: {path}")
    if args.tinyshogi_nn_bin is not None and not args.tinyshogi_nn_bin.is_file():
        raise SystemExit(f"nn.bin not found: {args.tinyshogi_nn_bin}")

    if args.movetime_ms:
        tiny_limit = opponent_limit = f"movetime {args.movetime_ms}"
    else:
        tiny_limit = f"nodes {args.tinyshogi_nodes or args.nodes}"
        opponent_limit = f"nodes {args.opponent_nodes or args.nodes}"
    tiny_options = {"Threads": args.tinyshogi_threads, "Seed": args.seed,
                    "SearchMode": args.tinyshogi_search_mode,
                    "MCTSMode": args.tinyshogi_mcts_mode,
                    "UCTExploration": args.tinyshogi_uct_exploration,
                    "RolloutDepth": args.tinyshogi_rollout_depth,
                    "AspirationWindow": args.tinyshogi_aspiration_window,
                    "QuiescenceMargin": args.tinyshogi_quiescence_margin,
                    "MaxTreeNodes": 100000,
                    "QuiescenceDepth": args.tinyshogi_quiescence_depth}
    if args.tinyshogi_eval_plugin is not None:
        tiny_options["EvalPlugin"] = args.tinyshogi_eval_plugin
    if args.tinyshogi_eval_model is not None:
        tiny_options["EvalModel"] = args.tinyshogi_eval_model
        tiny_options["MCTSMode"] = "neural"
        tiny_options["LeafBatch"] = args.tinyshogi_leaf_batch
    yaneura_options = {
        "Threads": args.opponent_threads, "USI_Hash": 64,
        "USI_OwnBook": "false", "BookFile": "no_book"
    }
    if args.yaneuraou_eval_dir is not None:
        yaneura_options["EvalDir"] = args.yaneuraou_eval_dir
    if args.yaneuraou_eval_model is not None:
        yaneura_options["EvalModel"] = args.yaneuraou_eval_model
        yaneura_options["MCTSMode"] = "neural"
        yaneura_options["LeafBatch"] = args.opponent_leaf_batch
    tiny = yaneura = None
    records = []
    results = []
    winners = []
    model_sha256 = None
    if args.tinyshogi_nn_bin is not None:
        digest = hashlib.sha256()
        with args.tinyshogi_nn_bin.open("rb") as model:
            while True:
                block = model.read(1024 * 1024)
                if not block:
                    break
                digest.update(block)
        model_sha256 = digest.hexdigest()
    args.output.parent.mkdir(parents=True, exist_ok=True)
    output_stream = args.output.open("w", encoding="utf-8")
    try:
        tiny_environment = os.environ.copy()
        if args.tinyshogi_nn_bin is not None:
            tiny_environment["YANEURAOU_NN_BIN"] = str(
                args.tinyshogi_nn_bin.resolve())
        tiny = Engine("tinyshogi", args.tinyshogi, tiny_options, args.timeout,
                      tiny_environment)
        yaneura = Engine("YaneuraOu", args.yaneuraou, yaneura_options, args.timeout)
        for game in range(args.games):
            if game != 0 and not args.reuse_processes:
                tiny.close()
                yaneura.close()
                tiny = Engine("tinyshogi", args.tinyshogi, tiny_options,
                              args.timeout, tiny_environment)
                yaneura = Engine("YaneuraOu", args.yaneuraou,
                                  yaneura_options, args.timeout)
            tiny.new_game()
            yaneura.new_game()
            engines = (tiny, yaneura) if game % 2 == 0 else (yaneura, tiny)
            opening_index = ((args.opening_offset + game // 2) % len(PAIRED_OPENINGS)
                             if args.paired_openings else 0)
            moves = list(PAIRED_OPENINGS[opening_index]) if args.paired_openings else []
            current_sfen = query_sfen(tiny, moves)
            game_records = []
            result = "draw"
            for ply in range(args.max_plies):
                side = ply % 2
                current = engines[side]
                sfen = current_sfen
                try:
                    move = current.bestmove(
                        sfen, tiny_limit if current is tiny else opponent_limit)
                except RuntimeError as error:
                    raise RuntimeError(
                        f"game {game} ply {ply} ({current.name}, {len(moves)} moves) "
                        f"at SFEN {sfen}: {error}"
                    ) from error
                if move in ("resign", "win"):
                    if move == "win":
                        result = "black" if side == 0 else "white"
                    else:
                        result = "white" if side == 0 else "black"
                    break
                game_records.append({
                    "version": 1, "game": game, "ply": ply, "sfen": sfen,
                    "side": "b" if side == 0 else "w", "move": move,
                    "engine": current.name, "opening": opening_index,
                    "node_limit": None if args.movetime_ms else
                        (args.tinyshogi_nodes or args.nodes if current is tiny else
                         args.opponent_nodes or args.nodes),
                    "reported_nodes": current.last_nodes,
                    "model_sha256": model_sha256
                })
                next_sfen = query_sfen(tiny, sfen, [move])
                try:
                    before_number = int(sfen.rsplit(" ", 1)[1])
                    after_number = int(next_sfen.rsplit(" ", 1)[1])
                except (IndexError, ValueError) as error:
                    raise RuntimeError(f"invalid SFEN after {move}: {next_sfen}") from error
                if after_number != before_number + 1:
                    raise RuntimeError(
                        f"game {game} ply {ply}: illegal move from {current.name}: {move}")
                moves.append(move)
                current_sfen = next_sfen
                if args.verbose:
                    print(f"game {game + 1} ply {ply + 1}: {current.name} {move}",
                          flush=True)
            for record in game_records:
                record["result"] = result
            records.extend(game_records)
            for record in game_records:
                output_stream.write(json.dumps(record, ensure_ascii=False) + "\n")
            output_stream.flush()
            results.append(result)
            winners.append("draw" if result == "draw" else
                           engines[0 if result == "black" else 1].name)
            print(f"game {game + 1}/{args.games}: {result} ({len(moves)} plies)", flush=True)
    finally:
        output_stream.close()
        if tiny is not None:
            tiny.close()
        if yaneura is not None:
            yaneura.close()

    print(f"wrote {len(records)} records to {args.output}")
    print("results: " + ", ".join(
        f"{name}={count}" for name, count in sorted(Counter(results).items())))
    print("winners: " + ", ".join(
        f"{name}={count}" for name, count in sorted(Counter(winners).items())))


if __name__ == "__main__":
    main()
