#!/usr/bin/env python3
"""Convert TinyShogi self-play/teacher JSONL into compact NDF1 records."""

import argparse
import json
import random
import struct
import sys

RECORD = struct.Struct("<81B14B x h B B")


def encode_sfen(sfen):
    fields = sfen.split()
    if len(fields) != 4 or fields[1] not in ("b", "w"):
        raise ValueError("invalid SFEN")
    types = {"p": 1, "l": 2, "n": 3, "s": 4, "g": 5,
             "b": 6, "r": 7, "k": 8}
    board = []
    for row in fields[0].split("/"):
        expanded = []
        promoted = False
        for token in row:
            if token.isdigit():
                expanded.extend([0] * int(token))
            elif token == "+":
                if promoted:
                    raise ValueError("duplicate promotion marker")
                promoted = True
            else:
                if token.lower() not in types or (promoted and types[token.lower()] >= 9):
                    if token.lower() not in types:
                        raise ValueError("invalid board piece")
                piece = types[token.lower()]
                if promoted:
                    if piece > 7:
                        raise ValueError("invalid promoted piece")
                    piece += 8
                    promoted = False
                expanded.append(piece if token.isupper() else piece + 16)
        if promoted or len(expanded) != 9:
            raise ValueError("invalid board row")
        board.extend(expanded)
    if len(board) != 81:
        raise ValueError("invalid board")
    hand = [0] * 14
    hand_types = {"r": 0, "b": 1, "g": 2, "s": 3,
                  "n": 4, "l": 5, "p": 6}
    if fields[2] != "-":
        amount = 0
        for token in fields[2]:
            if token.isdigit():
                amount = amount * 10 + int(token)
                continue
            if token.lower() not in hand_types:
                raise ValueError("invalid hand piece")
            index = (0 if token.isupper() else 7) + hand_types[token.lower()]
            hand[index] = amount or 1
            amount = 0
        if amount:
            raise ValueError("dangling hand count")
    return board, hand, 0 if fields[1] == "b" else 1


def result_value(record):
    teacher = "teacher_value" in record
    value = record.get("teacher_value", record.get("value"))
    if value is None and record.get("result") in ("black", "white", "draw"):
        result = record["result"]
        side = record.get("side")
        if result == "draw":
            value = 0
        elif side in ("b", "w"):
            value = 1000 if (result == "black") == (side == "b") else -1000
        else:
            raise ValueError("side is required when using result labels")
    if teacher:
        if not isinstance(value, (int, float)):
            raise ValueError("teacher_value must be numeric")
        value = round(value * 1000.0)
    elif value in (-1, 0, 1):
        value *= 1000
    if not isinstance(value, int) or value < -1000 or value > 1000:
        raise ValueError("value must be an integer in [-1000, 1000] or teacher_value in [-1, 1]")
    return value, 1 if teacher else 0


def read_records(paths):
    for path in paths:
        with open(path, encoding="utf-8") as source:
            for line_number, line in enumerate(source, 1):
                if not line.strip():
                    continue
                try:
                    record = json.loads(line)
                    if record.get("version") != 1 or not isinstance(record.get("sfen"), str):
                        raise ValueError("version 1 SFEN record required")
                    board, hand, side = encode_sfen(record["sfen"])
                    value, source_id = result_value(record)
                    yield bytes(board), bytes(hand), side, value, source_id
                except (ValueError, TypeError, json.JSONDecodeError) as error:
                    raise ValueError(f"{path}:{line_number}: {error}") from error


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("inputs", nargs="+", help="self-play or teacher JSONL files")
    parser.add_argument("-o", "--output", required=True)
    parser.add_argument("--limit", type=int, default=0)
    parser.add_argument("--shuffle", action="store_true")
    parser.add_argument("--seed", type=int, default=1)
    args = parser.parse_args()
    if args.limit < 0:
        parser.error("--limit must be non-negative")
    try:
        records = list(read_records(args.inputs))
    except (OSError, ValueError) as error:
        print(error, file=sys.stderr)
        return 1
    if args.shuffle:
        random.Random(args.seed).shuffle(records)
    if args.limit:
        records = records[:args.limit]
    with open(args.output, "wb") as output:
        output.write(b"NDF1")
        output.write(struct.pack("<III", 1, len(records), RECORD.size))
        for board, hand, side, value, source_id in records:
            output.write(RECORD.pack(*board, *hand, value, side, source_id))
    print(f"wrote {len(records)} NDF1 records to {args.output}", file=sys.stderr)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
