#!/usr/bin/env python3
"""Evaluate a selfplay_match JSONL file with a decisive-game Elo SPRT."""

import argparse
import json
import math
from collections import defaultdict
from pathlib import Path


def win_probability(elo):
    return 1.0 / (1.0 + math.pow(10.0, -elo / 400.0))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("records", type=Path)
    parser.add_argument("--candidate", default="tinyshogi")
    parser.add_argument("--elo0", type=float, default=-5.0,
                        help="regression boundary (default: -5 Elo)")
    parser.add_argument("--elo1", type=float, default=0.0,
                        help="acceptance boundary (default: 0 Elo)")
    parser.add_argument("--alpha", type=float, default=0.05)
    parser.add_argument("--beta", type=float, default=0.05)
    args = parser.parse_args()
    if not args.records.is_file() or args.elo1 <= args.elo0:
        parser.error("records must exist and elo1 must exceed elo0")
    if not (0.0 < args.alpha < 1.0 and 0.0 < args.beta < 1.0):
        parser.error("alpha and beta must be between zero and one")

    games = defaultdict(list)
    with args.records.open(encoding="utf-8") as source:
        for line in source:
            if line.strip():
                record = json.loads(line)
                games[int(record["game"])].append(record)
    wins = draws = losses = 0
    for records in games.values():
        records.sort(key=lambda item: int(item["ply"]))
        result = records[0].get("result", "draw")
        candidate_colors = {item["side"] for item in records
                            if item.get("engine") == args.candidate}
        if result == "draw" or len(candidate_colors) != 1:
            draws += 1
        elif ("b" if result == "black" else "w") in candidate_colors:
            wins += 1
        else:
            losses += 1

    p0, p1 = win_probability(args.elo0), win_probability(args.elo1)
    llr = wins * math.log(p1 / p0) + losses * math.log((1.0 - p1) / (1.0 - p0))
    lower = math.log(args.beta / (1.0 - args.alpha))
    upper = math.log((1.0 - args.beta) / args.alpha)
    decision = "accept" if llr >= upper else "reject" if llr <= lower else "continue"
    score = (wins + 0.5 * draws) / max(1, wins + draws + losses)
    output = {
        "games": wins + draws + losses, "wins": wins, "draws": draws,
        "losses": losses, "score": score, "elo0": args.elo0,
        "elo1": args.elo1, "llr": llr, "lower": lower, "upper": upper,
        "decision": decision,
        "method": "draws cancel; logistic likelihood over decisive games",
    }
    print(json.dumps(output, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
