#!/usr/bin/env python3
"""Run a small USI self-play match between tinyshogi and YaneuraOu."""

import argparse
import json
import os
import selectors
import subprocess
import sys
from pathlib import Path


class Engine:
    def __init__(self, name, path, options, timeout):
        self.name = name
        self.path = str(path)
        self.timeout = timeout
        self.process = subprocess.Popen(
            [self.path], stdin=subprocess.PIPE, stdout=subprocess.PIPE,
            stderr=subprocess.PIPE, bufsize=0
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

    def bestmove(self, position, limit):
        self.send("position startpos" + (" moves " + " ".join(position) if position else ""))
        self.send("go " + limit)
        line = self.read_until("bestmove")
        fields = line.split()
        if len(fields) < 2:
            raise RuntimeError(f"malformed bestmove from {self.name}: {line}")
        return fields[1]

    def close(self):
        if self.process.poll() is None:
            try:
                self.send("quit")
                self.process.wait(timeout=2)
            except (BrokenPipeError, subprocess.TimeoutExpired):
                self.process.kill()
        self.selector.close()


def query_sfen(engine, moves):
    engine.send("position startpos" + (" moves " + " ".join(moves) if moves else ""))
    engine.send("sfen")
    return engine.read_sfen()


def parse_args():
    root = Path(__file__).resolve().parents[1]
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--tinyshogi", type=Path, default=root / "build/tinyshogi")
    parser.add_argument("--tinyshogi-eval-plugin", type=Path,
                        help="EvalPlugin shared library for TinyShogi")
    parser.add_argument("--yaneuraou", type=Path, default=root / "build/yaneuraou/YaneuraOu-material")
    parser.add_argument("--yaneuraou-eval-dir", type=Path,
                        help="EvalDir option for YaneuraOu-compatible engines")
    parser.add_argument("--games", type=int, default=2)
    parser.add_argument("--nodes", type=int, default=256)
    parser.add_argument("--movetime-ms", type=int)
    parser.add_argument("--max-plies", type=int, default=512)
    parser.add_argument("--output", type=Path, default=root / "selfplay-tiny-yaneuraou.jsonl")
    parser.add_argument("--timeout", type=float, default=30.0)
    parser.add_argument("--seed", type=int, default=1)
    return parser.parse_args()


def main():
    args = parse_args()
    if args.games < 1 or args.max_plies < 1 or args.nodes < 1:
        raise SystemExit("games, max-plies, and nodes must be positive")
    if args.movetime_ms is not None and args.movetime_ms < 1:
        raise SystemExit("movetime-ms must be positive")
    for path in (args.tinyshogi, args.yaneuraou):
        if not path.is_file() or not os.access(path, os.X_OK):
            raise SystemExit(f"executable not found or not executable: {path}")

    limit = f"movetime {args.movetime_ms}" if args.movetime_ms else f"nodes {args.nodes}"
    tiny_options = {"Threads": 1, "Seed": args.seed, "MaxTreeNodes": 100000}
    if args.tinyshogi_eval_plugin is not None:
        tiny_options["EvalPlugin"] = args.tinyshogi_eval_plugin
    yaneura_options = {
        "Threads": 1, "USI_Hash": 64, "USI_OwnBook": "false", "BookFile": "no_book"
    }
    if args.yaneuraou_eval_dir is not None:
        yaneura_options["EvalDir"] = args.yaneuraou_eval_dir
    tiny = yaneura = None
    records = []
    try:
        tiny = Engine("tinyshogi", args.tinyshogi, tiny_options, args.timeout)
        yaneura = Engine("YaneuraOu", args.yaneuraou, yaneura_options, args.timeout)
        for game in range(args.games):
            engines = (tiny, yaneura) if game % 2 == 0 else (yaneura, tiny)
            moves = []
            game_records = []
            result = "draw"
            for ply in range(args.max_plies):
                side = ply % 2
                current = engines[side]
                sfen = query_sfen(tiny, moves)
                try:
                    move = current.bestmove(moves, limit)
                except RuntimeError as error:
                    raise RuntimeError(
                        f"game {game} ply {ply} ({current.name}, {len(moves)} moves): {error}"
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
                    "engine": current.name
                })
                moves.append(move)
            for record in game_records:
                record["result"] = result
            records.extend(game_records)
            print(f"game {game + 1}/{args.games}: {result} ({len(moves)} plies)", flush=True)
    finally:
        if tiny is not None:
            tiny.close()
        if yaneura is not None:
            yaneura.close()

    args.output.parent.mkdir(parents=True, exist_ok=True)
    with args.output.open("w", encoding="utf-8") as output:
        for record in records:
            output.write(json.dumps(record, ensure_ascii=False) + "\n")
    print(f"wrote {len(records)} records to {args.output}")


if __name__ == "__main__":
    main()
