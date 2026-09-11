#!/usr/bin/env python3
"""Test-only differential legality check; requires external python-shogi 1.1.1."""

import argparse
import json
from importlib.metadata import version
from pathlib import Path
import random

from selfplay_match import sha256
from usi_engine import Engine


def main():
    import shogi  # Test-only oracle, never imported by the engine or match runner.
    oracle_version = version("python-shogi")
    if oracle_version != "1.1.1":
        raise RuntimeError("this validation fixture pins python-shogi 1.1.1")

    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--engine", type=Path, default=Path("build/make/tinyshogi"))
    parser.add_argument("--openings", type=Path, default=Path("runs/strength/openings/development.sfens"))
    parser.add_argument("--positions", type=int, default=1000)
    parser.add_argument("--seed", type=int, default=7)
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    if args.positions < 1 or args.output and args.output.exists():
        parser.error("invalid position count or existing report")
    engine = Engine("referee", args.engine.resolve(), {}, 30)
    rng = random.Random(args.seed)
    checked = 0
    try:
        for initial in args.openings.read_text().splitlines():
            board = shogi.Board(initial)
            moves = []
            for _ in range(20):
                state = engine.status(initial, moves)
                actual = set(state["legal_moves"])
                expected = {move.usi() for move in board.legal_moves}
                if actual != expected:
                    raise RuntimeError(f"SFEN={board.sfen()}; extra={sorted(actual - expected)}; "
                                       f"missing={sorted(expected - actual)}")
                if state["sfen"].split()[:3] != board.sfen().split()[:3]:
                    raise RuntimeError(f"SFEN mismatch: {state['sfen']} != {board.sfen()}")
                checked += 1
                if checked == args.positions or not actual:
                    break
                move = rng.choice(sorted(actual))
                moves.append(move)
                board.push_usi(move)
            if checked == args.positions:
                break
    finally:
        engine.close()
    if checked < args.positions:
        raise RuntimeError(f"insufficient positions: {checked}")
    report = json.dumps({"positions": checked, "exact_match": True,
                         "oracle": "python-shogi", "oracle_version": oracle_version,
                         "engine_sha256": sha256(args.engine),
                         "openings_sha256": sha256(args.openings), "seed": args.seed}, indent=2) + "\n"
    if args.output:
        args.output.write_text(report)
    print(report, end="")


if __name__ == "__main__":
    main()
