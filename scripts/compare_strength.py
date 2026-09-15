#!/usr/bin/env python3
"""Compare paired development/validation matches; optionally freeze an eligible candidate."""

import argparse
import json
from pathlib import Path
import time

from match_gate import load_match, protocol_errors, bootstrap_interval, summarize
from strength_protocol import load_protocol, position_key, sha256


def pair_values(games, score=False):
    pairs = {}
    for game in games:
        key = position_key(game["initial_sfen"])
        side = game["tinyshogi_side"]
        value = (0.5 if score else 0) if game["result"] == "draw" else float(
            (game["result"] == "black") == (side == "b"))
        if side in pairs.setdefault(key, {}):
            raise ValueError("duplicate opening color")
        pairs[key][side] = value
    if any(set(pair) != {"b", "w"} for pair in pairs.values()):
        raise ValueError("incomplete color pairs")
    return {key: sum(pair.values()) for key, pair in pairs.items()}


def compare(candidate, baseline, direct):
    a, b = pair_values(candidate), pair_values(baseline)
    if a.keys() != b.keys():
        raise ValueError("comparisons must use the same opening pairs")
    deltas = [a[key] - b[key] for key in sorted(a)]
    direct_values = pair_values(direct, score=True)
    if direct_values.keys() != a.keys():
        raise ValueError("direct match must use the same validation pairs")
    delta_interval = bootstrap_interval(deltas)
    direct_interval = bootstrap_interval(list(direct_values.values()))
    return {"candidate": summarize(candidate), "baseline": summarize(baseline),
            "direct": summarize(direct), "paired_win_rate_change": sum(deltas) / (2 * len(deltas)),
            "paired_change_95_interval": delta_interval, "direct_score_95_interval": direct_interval,
            "promotion_supported": delta_interval[0] > 0 and direct_interval[0] > 0.5}


def audit_comparison(candidate_path, baseline_path, direct_path, protocol_path):
    protocol = load_protocol(protocol_path)
    matches = [load_match(path) for path in (candidate_path, baseline_path, direct_path)]
    for manifest, games, violations, *_ in matches:
        errors = protocol_errors(manifest, games, violations, protocol_path, phase="validation")
        if errors or len(games) != 1000:
            raise ValueError(f"invalid full validation match: {errors}")
    candidate, baseline, direct = [m[0] for m in matches]
    if (baseline["engine_sha256"][0] != protocol["baseline_sha256"] or
            direct["engine_sha256"] != [candidate["engine_sha256"][0], protocol["baseline_sha256"]] or
            candidate["engine_sha256"][1] != protocol["opponent"]["sha256"] or
            baseline["engine_sha256"][1] != protocol["opponent"]["sha256"] or
            candidate["engine_options"][0] != direct["engine_options"][0] or
            candidate["plugin_sha256"] != direct["plugin_sha256"]):
        raise ValueError("comparison binaries/options do not match")
    report = compare(*[m[1] for m in matches])
    report["acceptance_eligible"] = report["promotion_supported"] and report["candidate"]["wins"] >= 850
    report["target_accepted"] = False
    return report, candidate


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--candidate", type=Path, required=True)
    parser.add_argument("--baseline", type=Path, required=True)
    parser.add_argument("--direct", type=Path, required=True)
    parser.add_argument("--protocol", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--freeze", type=Path, help="Create an acceptance lock only if validation qualifies")
    args = parser.parse_args()
    if args.output.exists() or args.freeze and args.freeze.exists():
        parser.error("refusing to overwrite an experiment")
    report, candidate = audit_comparison(args.candidate, args.baseline, args.direct, args.protocol)
    with args.output.open("x") as stream:
        json.dump(report, stream, indent=2)
        stream.write("\n")
    if args.freeze:
        if not report["acceptance_eligible"]:
            raise ValueError("validation has not qualified for acceptance; holdout remains reserved")
        artifacts = [Path(str(path) + suffix) for path in (args.candidate, args.baseline, args.direct)
                     for suffix in ("", ".manifest.json", ".games.jsonl")]
        artifacts.append(args.output)
        lock = {"version": 1, "created_unix": time.time(), "protocol_sha256": sha256(args.protocol),
                "candidate_sha256": candidate["engine_sha256"][0], "plugin_sha256": candidate["plugin_sha256"],
                "options": candidate["engine_options"][0],
                "protocol_file": str(args.protocol.resolve()),
                "records": {name: str(path.resolve()) for name, path in
                            (("candidate", args.candidate), ("baseline", args.baseline), ("direct", args.direct))},
                "report": str(args.output.resolve()),
                "validation": {str(path.resolve()): sha256(path) for path in artifacts}}
        with args.freeze.open("x") as stream:
            json.dump(lock, stream, indent=2)
            stream.write("\n")
    print(json.dumps(report, indent=2))


if __name__ == "__main__":
    main()
