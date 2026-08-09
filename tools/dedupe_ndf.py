#!/usr/bin/env python3
"""Deduplicate fixed-size NDF1 records while preserving first-seen order."""

import argparse
from pathlib import Path
import struct

HEADER = struct.Struct("<4sIII")
MAGIC, VERSION, RECORD_SIZE = b"NDF1", 1, 100


def records(path):
    with path.open("rb") as stream:
        header = stream.read(HEADER.size)
        if len(header) != HEADER.size:
            raise ValueError(f"short NDF1 header: {path}")
        magic, version, count, record_size = HEADER.unpack(header)
        if (magic, version, record_size) != (MAGIC, VERSION, RECORD_SIZE):
            raise ValueError(f"unsupported NDF1 header: {path}")
        for _ in range(count):
            record = stream.read(RECORD_SIZE)
            if len(record) != RECORD_SIZE:
                raise ValueError(f"truncated NDF1 record: {path}")
            yield record


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--output", required=True, type=Path)
    parser.add_argument("inputs", nargs="+", type=Path)
    args = parser.parse_args()
    seen = set()
    unique = []
    for path in args.inputs:
        for record in records(path):
            if record not in seen:
                seen.add(record)
                unique.append(record)
    if len(unique) > 0xFFFFFFFF:
        parser.error("NDF1 supports at most 4,294,967,295 records")
    partial = args.output.with_name(args.output.name + ".partial")
    args.output.parent.mkdir(parents=True, exist_ok=True)
    with partial.open("wb") as stream:
        stream.write(HEADER.pack(MAGIC, VERSION, len(unique), RECORD_SIZE))
        for record in unique:
            stream.write(record)
        stream.flush()
    partial.replace(args.output)
    print(f"deduplicated {len(unique)} records -> {args.output}")


if __name__ == "__main__":
    main()
