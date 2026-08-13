#!/usr/bin/env python3
"""Validate a fixed alternating-color TinyShogi match record.

The strength target is expressed as decisive wins; draws are reported but do
not satisfy the requested win-rate gate.
"""

import argparse
import json
from collections import defaultdict


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("record")
    parser.add_argument("--engine", default="tinyshogi")
    parser.add_argument("--games", type=int, default=100)
    parser.add_argument("--minimum-wins", type=int, default=25)
    parser.add_argument("--minimum-score", type=float,
                        help="optional informational score gate")
    args = parser.parse_args()

    games = {}
    with open(args.record, encoding="utf-8") as stream:
        for line in stream:
            record = json.loads(line)
            game = games.setdefault(record["game"], {"result": record.get("result"), "side": {}})
            game["result"] = record.get("result", game["result"])
            game["side"][record["engine"]] = record["side"]

    score = wins = draws = losses = 0
    for game in games.values():
        result = game["result"]
        side = game["side"].get(args.engine)
        if result == "draw" or side is None:
            draws += 1
        elif result == ("black" if side in ("b", "black") else "white"):
            wins += 1
            score += 1
        else:
            losses += 1
            score += 0
    count = wins + draws + losses
    points = score + draws / 2
    fraction = points / count if count else 0.0
    print(f"games={count} wins={wins} draws={draws} losses={losses} score={fraction:.3f}")
    print(f"decisive_win_rate={wins / count if count else 0.0:.3f}")
    if count != args.games or wins < args.minimum_wins:
        raise SystemExit(1)
    if args.minimum_score is not None and fraction < args.minimum_score:
        raise SystemExit(1)


if __name__ == "__main__":
    main()
