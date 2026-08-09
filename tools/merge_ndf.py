#!/usr/bin/env python3
"""Merge NDF1 shards without decoding their fixed-size records."""

import argparse
from pathlib import Path
import struct


HEADER = struct.Struct("<4sIII")
MAGIC, VERSION, RECORD_SIZE = b"NDF1", 1, 100
COPY_BYTES = 16 * 1024 * 1024


def inspect(path):
    size = path.stat().st_size
    with path.open("rb") as stream:
        raw = stream.read(HEADER.size)
    if len(raw) != HEADER.size:
        raise ValueError(f"short header: {path}")
    magic, version, count, record_size = HEADER.unpack(raw)
    if (magic, version, record_size) != (MAGIC, VERSION, RECORD_SIZE):
        raise ValueError(f"unsupported NDF header: {path}")
    expected = HEADER.size + count * RECORD_SIZE
    if size != expected:
        raise ValueError(f"size mismatch: {path}: expected {expected}, got {size}")
    return count


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--output", required=True, type=Path)
    parser.add_argument("inputs", nargs="+", type=Path)
    args = parser.parse_args()
    counts = [inspect(path) for path in args.inputs]
    total = sum(counts)
    if total > 0xFFFFFFFF:
        parser.error("NDF1 supports at most 4,294,967,295 records per file")
    partial = args.output.with_name(args.output.name + ".partial")
    args.output.parent.mkdir(parents=True, exist_ok=True)
    with partial.open("wb") as target:
        target.write(HEADER.pack(MAGIC, VERSION, total, RECORD_SIZE))
        for path in args.inputs:
            with path.open("rb") as source:
                source.seek(HEADER.size)
                while True:
                    chunk = source.read(COPY_BYTES)
                    if not chunk:
                        break
                    target.write(chunk)
        target.flush()
    partial.replace(args.output)
    print(f"merged {len(args.inputs)} shards, {total} records -> {args.output}")


if __name__ == "__main__":
    main()
