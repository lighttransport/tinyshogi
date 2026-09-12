#!/usr/bin/env python3
"""Freeze disjoint, stratified development and held-out SFEN opening sets."""

import argparse
import hashlib
import json
from pathlib import Path
import subprocess

from strength_protocol import sha256, position_key, MODEL, OPPONENT_COMMIT, PHASES, load_protocol


def split_openings(sources, pairs=500, seed=20260910):
    if pairs < 2 or pairs % 2:
        raise ValueError("pair count must be positive and even for two strata")
    seen = set()
    groups = []
    for source in sources:
        positions = []
        for line in source.read_text(encoding="utf-8-sig").splitlines():
            fields = line.strip().removeprefix("sfen ").split()
            if len(fields) != 4 or fields[1] not in ("b", "w"):
                raise ValueError(f"invalid opening in {source}: {line}")
            key = " ".join(fields[:3])
            if key in seen:
                continue
            seen.add(key)
            # Ignore the move number when deduplicating. Never filter by a
            # candidate's evaluation or results when constructing this split.
            positions.append(" ".join(fields))
        positions.sort(key=lambda sfen: hashlib.sha256(
            f"{seed}:".encode() + " ".join(sfen.split()[:3]).encode()).digest())
        if len(positions) < pairs:
            raise ValueError(f"insufficient unique positions in {source}")
        groups.append(positions)
    if len(groups) != 2:
        raise ValueError("exactly two strata are required")
    development, heldout = [], []
    for index in range(pairs // 2):
        for group in groups:
            development.append(group[index])
            heldout.append(group[index + pairs // 2])
    return development, heldout


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--fixtures", type=Path, default=Path("runs/strength/fixtures"))
    parser.add_argument("--output-dir", type=Path, default=Path("runs/strength/openings"))
    parser.add_argument("--pairs", type=int, default=500)
    parser.add_argument("--seed", type=int, help="Defaults to 20260910 for legacy splits or 20260912 for campaigns")
    parser.add_argument("--campaign", action="store_true", help="Freeze a three-way protocol; seed 20260912")
    parser.add_argument("--budget", choices=("equal-request-1000", "tiny-2000-yane-1000"),
                        default="equal-request-1000", help="Candidate/YaneuraOu requests; direct matches use equal budgets")
    parser.add_argument("--yaneuraou", type=Path, default=Path("build/yaneuraou/YaneuraOu"))
    parser.add_argument("--opponent-source", type=Path, default=Path("third_party/YaneuraOu"))
    parser.add_argument("--baseline", type=Path, default=Path("build/strength-v2-baseline/tinyshogi"))
    parser.add_argument("--exclude-protocol", type=Path, action="append", default=[],
                        help="Exclude all positions registered by a prior campaign")
    args = parser.parse_args()
    if args.seed is None:
        args.seed = 20260912 if args.campaign else 20260910
    sources = [args.fixtures / f"start_sfens_ply{ply}.txt" for ply in (24, 32)]
    if args.campaign:
        prepare_campaign(args, sources)
        return
    if args.exclude_protocol or args.budget != "equal-request-1000":
        raise ValueError("--exclude-protocol and asymmetric budgets require --campaign")
    development, heldout = split_openings(sources, args.pairs, args.seed)
    args.output_dir.mkdir(parents=True, exist_ok=True)
    paths = [args.output_dir / name for name in ("development.sfens", "heldout.sfens", "split.json")]
    if any(path.exists() for path in paths):
        raise ValueError("opening split already exists; refusing to replace it")
    for path, positions in zip(paths, (development, heldout)):
        path.write_text("\n".join(positions) + "\n", encoding="utf-8")
    manifest = {
        "source": "https://github.com/yaneurao/YaneuraOu/releases/tag/BalancedPositions2025",
        "license": "MIT", "seed": args.seed, "pairs_per_split": args.pairs,
        "source_sha256": {path.name: sha256(path) for path in sources},
        "split_sha256": {path.name: sha256(path) for path in paths[:2]},
        "selection": f"SHA-256(seed:board side hands), globally deduplicated, {args.pairs // 2} per stratum",
    }
    paths[2].write_text(json.dumps(manifest, indent=2) + "\n")
    print(json.dumps(manifest, indent=2))


def campaign_splits(sources, pairs=500, seed=20260912, excluded_positions=()):
    old = split_openings(sources)
    excluded = {position_key(sfen) for group in old for sfen in group}
    excluded.update(position_key(sfen) for sfen in excluded_positions)
    seen = set(excluded)
    groups = []
    for source in sources:
        group = []
        for line in source.read_text(encoding="utf-8-sig").splitlines():
            sfen = " ".join(line.removeprefix("sfen ").split())
            key = position_key(sfen)
            if key not in seen:
                seen.add(key)
                group.append(sfen)
        group.sort(key=lambda sfen: hashlib.sha256(f"{seed}:{position_key(sfen)}".encode()).digest())
        if len(group) < 3 * pairs // 2:
            raise ValueError("insufficient fresh openings")
        groups.append(group)
    return {phase: [groups[stratum][phase_index * pairs // 2 + i]
                    for i in range(pairs // 2) for stratum in range(2)]
            for phase_index, phase in enumerate(PHASES)}


def prepare_campaign(args, sources):
    if args.pairs != 500:
        raise ValueError("campaign requires 500 pairs per split")
    revision = subprocess.check_output(["git", "-C", str(args.opponent_source), "rev-parse", "HEAD"], text=True).strip()
    dirty = subprocess.check_output(["git", "-C", str(args.opponent_source), "diff", "HEAD", "--"], text=True)
    if revision != OPPONENT_COMMIT or dirty:
        raise ValueError("opponent must be the unchanged pinned source revision")
    excluded = []
    for path in args.exclude_protocol:
        prior = load_protocol(path)
        for split in prior["splits"].values():
            excluded.extend((path.parent / split["file"]).read_text().splitlines())
    splits = campaign_splits(sources, seed=args.seed, excluded_positions=excluded)
    paths = [args.output_dir / (phase + ".sfens") for phase in PHASES]
    output = args.output_dir / "protocol.json"
    if any(path.exists() for path in paths + [output]):
        raise ValueError("refusing to replace registered campaign")
    protocol = {"version": 2 if args.budget == "equal-request-1000" else 3,
                "budget": args.budget, "seed": args.seed,
                "model_sha256": MODEL, "baseline_sha256": sha256(args.baseline),
                "opponent": {"commit": revision, "sha256": sha256(args.yaneuraou),
                             "compiler": subprocess.check_output(["clang++", "--version"], text=True).splitlines()[0],
                             "build": "normal YANEURAOU_EDITION=YANEURAOU_ENGINE_NNUE TARGET_CPU=AVX2 COMPILER=clang++"},
                "source_sha256": {path.name: sha256(path) for path in sources},
                "excluded": "both historical 500-pair splits, seed 20260910",
                "excluded_protocol_sha256": [sha256(path) for path in args.exclude_protocol],
                "splits": {}}
    args.output_dir.mkdir(parents=True, exist_ok=True)
    for phase, path in zip(PHASES, paths):
        with path.open("x") as stream:
            stream.write("\n".join(splits[phase]) + "\n")
        protocol["splits"][phase] = {"file": path.name, "sha256": sha256(path)}
    with output.open("x") as stream:
        json.dump(protocol, stream, indent=2)
        stream.write("\n")
    print(json.dumps(protocol, indent=2))


if __name__ == "__main__":
    main()
