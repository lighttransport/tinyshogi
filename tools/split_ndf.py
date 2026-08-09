#!/usr/bin/env python3
"""Deterministically split NDF1 into held-out records and rank shards."""

import argparse
from pathlib import Path
import struct

HEADER = struct.Struct("<4sIII")
MAGIC, VERSION, RECORD_SIZE = b"NDF1", 1, 100


def read_records(path):
    raw = path.read_bytes()
    magic, version, count, record_size = HEADER.unpack(raw[:HEADER.size])
    if (magic, version, record_size) != (MAGIC, VERSION, RECORD_SIZE):
        raise ValueError(f"unsupported NDF1: {path}")
    records = [raw[HEADER.size + i * RECORD_SIZE:HEADER.size + (i + 1) * RECORD_SIZE]
               for i in range(count)]
    if len(raw) != HEADER.size + count * RECORD_SIZE:
        raise ValueError(f"truncated NDF1: {path}")
    return records


def write_ndf(path, records):
    path.parent.mkdir(parents=True, exist_ok=True)
    partial = path.with_name(path.name + ".partial")
    with partial.open("wb") as stream:
        stream.write(HEADER.pack(MAGIC, VERSION, len(records), RECORD_SIZE))
        stream.writelines(records)
    partial.replace(path)


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("input", type=Path)
    parser.add_argument("--train-dir", required=True, type=Path)
    parser.add_argument("--heldout", required=True, type=Path)
    parser.add_argument("--ranks", type=int, default=12)
    args = parser.parse_args()
    if args.ranks < 1:
        parser.error("--ranks must be positive")
    records = read_records(args.input)
    heldout = [record for index, record in enumerate(records) if index % 5 == 0]
    train = [record for index, record in enumerate(records) if index % 5 != 0]
    write_ndf(args.heldout, heldout)
    for rank in range(args.ranks):
        write_ndf(args.train_dir / f"rank-{rank}.ndf1", train[rank::args.ranks])
    print(f"train={len(train)} heldout={len(heldout)} ranks={args.ranks}")


if __name__ == "__main__":
    main()
