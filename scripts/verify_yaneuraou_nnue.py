#!/usr/bin/env python3
"""Compare native full/incremental NNUE with the pinned opponent's raw e command."""

import argparse
import json
import os
from pathlib import Path
import random
import subprocess

from selfplay_match import sha256
from usi_engine import Engine


def verify(args):
    env = dict(os.environ, YANEURAOU_NN_BIN=str(args.nn_bin.resolve()),
               YANEURAOU_FV_SCALE=str(args.fv_scale))
    if sha256(args.nn_bin) != sha256(args.eval_dir / "nn.bin"):
        raise ValueError("different model files")
    if args.state_test:
        subprocess.run([str(args.state_test.resolve())], env=env, check=True)
    tiny = Engine("tinyshogi", args.tinyshogi.resolve(),
                  {"Threads": 1, "EvalPlugin": args.plugin.resolve()}, 30, env)
    other = None
    try:
        other = Engine("YaneuraOu", args.yaneuraou.resolve(), {
            "Threads": 1, "USI_Hash": 64, "USI_OwnBook": "false", "BookFile": "no_book",
            "EvalDir": args.eval_dir.resolve(), "FV_SCALE": args.fv_scale}, 30)
        initial_positions = args.openings.read_text().splitlines()
        rng = random.Random(args.seed)
        checked = 0
        examples = []
        for initial in initial_positions:
            moves = []
            for _ in range(20):
                state = tiny.status(initial, moves)
                if state["result"] != "ongoing":
                    break
                tiny.send("eval")
                actual = int(tiny.read_until("info string eval cp").rsplit(" ", 1)[1])
                other.set_position(initial, moves)
                other.send("e")
                expected = int(other.read_until("eval =").rsplit(" ", 1)[1])
                if actual != expected:
                    raise RuntimeError(f"NNUE mismatch: tiny={actual}, YaneuraOu={expected}, "
                                       f"SFEN={state['sfen']}")
                checked += 1
                if len(examples) < 4:
                    examples.append({"sfen": state["sfen"], "score": actual})
                if checked >= args.positions:
                    return {"positions": checked, "exact_match": True,
                            "model_sha256": sha256(args.nn_bin), "fv_scale": args.fv_scale,
                            "engine_sha256": [sha256(args.tinyshogi), sha256(args.yaneuraou)],
                            "plugin_sha256": sha256(args.plugin), "examples": examples}
                moves.append(rng.choice(sorted(state["legal_moves"])))
        raise RuntimeError(f"insufficient positions: {checked}")
    finally:
        tiny.close()
        if other:
            other.close()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--tinyshogi", type=Path, default=Path("build/make/tinyshogi"))
    parser.add_argument("--plugin", type=Path,
                        default=Path("build/make/tinyshogi-yaneuraou-nnue-direct.so"))
    parser.add_argument("--state-test", type=Path)
    parser.add_argument("--yaneuraou", type=Path, default=Path("build/yaneuraou/YaneuraOu"))
    parser.add_argument("--nn-bin", type=Path, default=Path("eval/hao/eval/nn.bin"))
    parser.add_argument("--eval-dir", type=Path, default=Path("eval/hao/eval"))
    parser.add_argument("--openings", type=Path, default=Path("runs/strength/openings/development.sfens"))
    parser.add_argument("--positions", type=int, default=1000)
    parser.add_argument("--fv-scale", type=int, default=20)
    parser.add_argument("--seed", type=int, default=7)
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    if args.positions < 1:
        parser.error("positions must be positive")
    if args.output and args.output.exists():
        parser.error("refusing to overwrite an existing report")
    report = verify(args)
    text = json.dumps(report, indent=2) + "\n"
    if args.output:
        args.output.write_text(text)
    print(text, end="")


if __name__ == "__main__":
    main()
