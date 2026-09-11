#!/usr/bin/env python3
"""Freeze disjoint, stratified development and held-out SFEN opening sets."""

import argparse
import hashlib
import json
from pathlib import Path

from selfplay_match import sha256


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
    parser.add_argument("--seed", type=int, default=20260910)
    args = parser.parse_args()
    sources = [args.fixtures / f"start_sfens_ply{ply}.txt" for ply in (24, 32)]
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


if __name__ == "__main__":
    main()
