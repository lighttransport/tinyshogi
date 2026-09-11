#!/usr/bin/env python3
"""Audit a completed match and gate the fixed 85%-wins benchmark."""

import argparse
from collections import defaultdict
import json
import math
from pathlib import Path
import random
import statistics

from selfplay_match import sha256

PINNED_OPPONENT = "39d8fe33c7fad313ecc2544b4705e82a77398ddd66f58982cf8a6e36976e1505"
PINNED_MODEL = "1141d275bceec911156801f27303dc9ff5beb24f4f59144cc069306c59e80782"
HELDOUT_OPENINGS = "c4864ddfb5c1672c19aabfa6891deea99407679e5bf32e9f81ed67ca8762be6a"


def read_jsonl(path):
    with Path(path).open(encoding="utf-8") as stream:
        return [json.loads(line) for line in stream if line.strip()]


def load_match(path):
    path = Path(path)
    manifest = json.loads(Path(str(path) + ".manifest.json").read_text())
    summaries = read_jsonl(str(path) + ".games.jsonl")
    if not manifest.get("complete"):
        raise ValueError("incomplete experiment")
    if manifest.get("version", 0) >= 3:
        if (sha256(path) != manifest.get("records_sha256") or
                sha256(str(path) + ".games.jsonl") != manifest.get("summaries_sha256")):
            raise ValueError("match artifact checksum mismatch")
    expected = manifest["arguments"]["games"]
    if len(summaries) != expected or manifest.get("completed_games") != expected:
        raise ValueError("missing game summaries")
    games = {}
    for game in summaries:
        game_id = game["game"]
        if type(game_id) is not int or game_id in games or not 0 <= game_id < expected:
            raise ValueError("duplicate or invalid game identifier")
        if (not game.get("complete") or game["result"] not in ("black", "white", "draw") or
                game["tinyshogi_side"] not in ("b", "w")):
            raise ValueError("invalid game result or color")
        games[game_id] = game
    positions = defaultdict(list)
    for record in read_jsonl(path):
        if record["game"] not in games:
            raise ValueError("position refers to unknown game")
        positions[record["game"]].append(record)
    violations = []
    nodes = defaultdict(list)
    elapsed = defaultdict(list)
    for game_id, game in games.items():
        records = positions[game_id]
        if len(records) != game["decisions"]:
            raise ValueError("missing move records")
        first_side = game["initial_sfen"].split()[1]
        if first_side not in ("b", "w"):
            raise ValueError("invalid starting side")
        game_violations = []
        move_count = 0
        for ply, record in enumerate(records):
            expected_side = first_side if ply % 2 == 0 else ("w" if first_side == "b" else "b")
            expected_engine = "tinyshogi" if expected_side == game["tinyshogi_side"] else "YaneuraOu"
            if (record["ply"] != ply or record["side"] != expected_side or
                    record["engine"] != expected_engine or record["result"] != game["result"] or
                    record["opening"] != game["opening"]):
                raise ValueError("inconsistent move record")
            if record.get("model_sha256") != manifest.get("model_sha256"):
                raise ValueError("inconsistent model hash in move record")
            if record["sfen"].split()[1] != expected_side:
                raise ValueError("inconsistent position side")
            if record["move"] in ("resign", "win"):
                if ply != len(records) - 1:
                    raise ValueError("moves after terminal decision")
            else:
                move_count += 1
            count, limit = record["reported_nodes"], record["node_limit"]
            settings = manifest["arguments"]
            expected_limit = None if settings.get("movetime_ms") else (
                settings.get("tinyshogi_nodes" if expected_engine == "tinyshogi" else "opponent_nodes")
                or settings["nodes"])
            if limit != expected_limit:
                raise ValueError("move budget does not match the experiment")
            if count is not None and (type(count) is not int or count < 0):
                raise ValueError("invalid reported node count")
            if count is not None:
                nodes[expected_engine].append(count)
            duration = record["elapsed_ms"]
            if not isinstance(duration, (int, float)) or not math.isfinite(duration) or duration < 0:
                raise ValueError("invalid elapsed time")
            elapsed[expected_engine].append(duration)
            if limit is not None:
                if (type(limit) is not int or limit < 1 or
                        (count is None and record["move"] not in ("resign", "win")) or
                        (count is not None and count > limit * (1 + float(
                            manifest.get("node_tolerance", {}).get(expected_engine, 0.05)
                            if isinstance(manifest.get("node_tolerance"), dict)
                            else manifest.get("node_tolerance", 0.05))))):
                    violations.append({"game": game_id, "ply": ply, "engine": expected_engine,
                                       "nodes": count, "limit": limit})
                    game_violations.append({"ply": ply, "engine": expected_engine,
                                            "reported_nodes": count, "node_limit": limit})
        if game_violations != game.get("node_violations", []):
            raise ValueError("inconsistent node audit")
        if move_count != game["plies"]:
            raise ValueError("inconsistent played-move count")
    if manifest.get("node_audit_passed") != (not violations):
        raise ValueError("inconsistent manifest node audit")
    return manifest, summaries, violations, nodes, elapsed


def paired_counts(games):
    pairs = defaultdict(list)
    for game in games:
        pairs[game["opening"]].append(game)
    counts = []
    seen = set()
    for pair in pairs.values():
        if len(pair) != 2 or {game["tinyshogi_side"] for game in pair} != {"b", "w"}:
            raise ValueError("missing or unmatched opening pair")
        if pair[0]["initial_sfen"] != pair[1]["initial_sfen"]:
            raise ValueError("color pair used different positions")
        key = " ".join(pair[0]["initial_sfen"].split()[:3])
        if key in seen:
            raise ValueError("repeated opening masquerading as independent pairs")
        seen.add(key)
        counts.append(sum(game["result"] != "draw" and
                          ((game["result"] == "black") == (game["tinyshogi_side"] == "b"))
                          for game in pair))
    return counts


def bootstrap_interval(counts, samples=10000, seed=7):
    if not counts:
        raise ValueError("empty match")
    rng = random.Random(seed)
    size = len(counts)
    estimates = sorted(sum(rng.choices(counts, k=size)) / (2 * size) for _ in range(samples))
    return [estimates[int(samples * 0.025)], estimates[int(samples * 0.975)]]


def summarize(games):
    wins = sum(game["result"] != "draw" and
               ((game["result"] == "black") == (game["tinyshogi_side"] == "b")) for game in games)
    draws = sum(game["result"] == "draw" for game in games)
    count = len(games)
    return {"games": count, "wins": wins, "draws": draws, "losses": count - wins - draws,
            "win_rate": wins / count if count else 0,
            "score": (wins + draws / 2) / count if count else 0}


def protocol_errors(manifest, games, violations):
    errors = []
    args = manifest["arguments"]
    if manifest.get("version", 0) < 3:
        errors.append("target acceptance requires checksummed version-3 artifacts")
    if not manifest.get("strict"):
        errors.append("experiment was not run in strict mode")
    if manifest["engine_sha256"][1] != PINNED_OPPONENT:
        errors.append("opponent does not match the pinned binary")
    if manifest.get("model_sha256") != PINNED_MODEL or manifest.get("opponent_model_sha256") != PINNED_MODEL:
        errors.append("models do not match the pinned shared weights")
    if manifest.get("openings_sha256") != HELDOUT_OPENINGS or args["opening_offset"] != 0:
        errors.append("experiment did not use the frozen held-out split")
    if ((args.get("tinyshogi_nodes") or args["nodes"]) != 1000 or
            (args.get("opponent_nodes") or args["nodes"]) != 1000 or
            args.get("movetime_ms") is not None or args["max_plies"] != 512):
        errors.append("incorrect search or game limits")
    options = manifest["engine_options"]
    for settings in options:
        if int(settings["Threads"]) != 1 or int(settings["USI_Hash"]) != 64 or int(settings["MultiPV"]) != 1:
            errors.append("incorrect thread, hash, or MultiPV setting")
    if (options[0].get("SearchMode") != "alphabeta" or
            options[0].get("PerpetualCheck") != "on" or
            options[1].get("USI_OwnBook") != "false" or
            options[1].get("BookFile") != "no_book" or
            options[1].get("USI_Ponder") != "false" or
            options[1].get("EnteringKingRule") != "CSARule27" or
            int(options[1].get("FV_SCALE", 0)) != 20 or args["fv_scale"] != 20):
        errors.append("incorrect search, book, pondering, rules, or evaluation settings")
    if violations or not manifest.get("node_audit_passed"):
        errors.append(f"node audit failed ({len(violations)} violations)")
    paired_counts(games)
    return errors


def validation_errors(manifest, parity_path, rules_path):
    errors = []
    for kind, path in (("NNUE parity", parity_path), ("rules parity", rules_path)):
        if path is None:
            errors.append(f"missing {kind} report")
            continue
        report = json.loads(Path(path).read_text())
        if not report.get("exact_match") or report.get("positions", 0) < 1000:
            errors.append(f"insufficient {kind} validation")
        if kind == "NNUE parity":
            if (report.get("engine_sha256") != manifest["engine_sha256"] or
                    report.get("plugin_sha256") != manifest["plugin_sha256"] or
                    report.get("model_sha256") != PINNED_MODEL or report.get("fv_scale") != 20):
                errors.append("NNUE report does not match the experiment artifacts")
        elif (report.get("engine_sha256") != manifest["referee_sha256"] or
              report.get("oracle") != "python-shogi" or report.get("oracle_version") != "1.1.1"):
            errors.append("rules report does not match the referee and pinned oracle")
    return errors


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("record", type=Path)
    parser.add_argument("--games", type=int, default=1000)
    parser.add_argument("--minimum-wins", type=int, default=850)
    parser.add_argument("--minimum-score", type=float)
    parser.add_argument("--report-only", action="store_true",
                        help="Describe a diagnostic/development match without accepting the target")
    parser.add_argument("--parity-report", type=Path, help="Exact NNUE comparison for these binaries")
    parser.add_argument("--rules-report", type=Path, help="Independent legal-move comparison for this referee")
    parser.add_argument("--output", type=Path, help="Write the audit report without replacing an existing file")
    args = parser.parse_args(argv)
    if args.output and args.output.exists():
        parser.error("refusing to overwrite an existing audit report")
    manifest, games, violations, nodes, elapsed = load_match(args.record)
    report = summarize(games)
    try:
        counts = paired_counts(games)
        report["win_rate_95_interval"] = bootstrap_interval(counts)
        report["interval_method"] = "opening-pair bootstrap, 10000 samples, seed 7"
    except ValueError:
        if not args.report_only:
            raise
        report["win_rate_95_interval"] = None
    report["node_violations"] = len(violations)
    report["nodes"] = {name: {"median": statistics.median(values), "maximum": max(values)}
                       for name, values in nodes.items() if values}
    report["elapsed_ms"] = {name: {"median": statistics.median(values), "maximum": max(values)}
                            for name, values in elapsed.items() if values}
    if args.report_only:
        report["target_accepted"] = False
        report["diagnostic_only"] = True
    else:
        errors = protocol_errors(manifest, games, violations)
        errors.extend(validation_errors(manifest, args.parity_report, args.rules_report))
        if args.games != 1000 or args.minimum_wins < 850:
            errors.append("the fixed target cannot be relaxed below 850 wins in 1000 games")
        if report["games"] != 1000 or report["wins"] < max(850, args.minimum_wins):
            errors.append(f"requires {max(850, args.minimum_wins)} wins in 1000 games")
        if args.minimum_score is not None and report["score"] < args.minimum_score:
            errors.append("score threshold not reached")
        report["errors"] = errors
        report["target_accepted"] = not errors
    text = json.dumps(report, indent=2) + "\n"
    if args.output:
        with args.output.open("x") as stream:
            stream.write(text)
    print(text, end="")
    return 0 if args.report_only or report["target_accepted"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
