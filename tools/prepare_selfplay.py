#!/usr/bin/env python3
"""Validate and normalize tinyshogi self-play JSONL for GPU training jobs."""

import argparse
import json
import struct
import sys


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("input")
    parser.add_argument("output")
    parser.add_argument("--binary", help="also write compact feature records")
    args = parser.parse_args()

    records = 0
    binary = open(args.binary, "wb") if args.binary else None
    if binary:
        binary.write(b"TSF1")
        binary.write(struct.pack("<I", 1))
    with open(args.input, "r", encoding="utf-8") as source, open(
        args.output, "w", encoding="utf-8"
    ) as destination:
        for line_number, line in enumerate(source, 1):
            if not line.strip():
                continue
            try:
                record = json.loads(line)
                if record.get("version") != 1:
                    raise ValueError("unsupported version")
                if not isinstance(record.get("sfen"), str):
                    raise ValueError("missing sfen")
                if not isinstance(record.get("move"), str):
                    raise ValueError("missing selected move")
                policy = record.get("policy")
                if not isinstance(policy, list) or not policy:
                    raise ValueError("missing policy")
                moves = set()
                visits = 0
                for entry in policy:
                    if not isinstance(entry, list) or len(entry) != 2:
                        raise ValueError("invalid policy entry")
                    move, count = entry
                    if not isinstance(move, str) or not isinstance(count, int) or count < 0:
                        raise ValueError("invalid policy value")
                    if move in moves:
                        raise ValueError("duplicate policy move")
                    moves.add(move)
                    visits += count
                if record["move"] not in moves:
                    raise ValueError("selected move absent from policy")
                if record.get("value") not in (-1, 0, 1):
                    raise ValueError("invalid outcome")
                record["policy_visits"] = visits
                destination.write(json.dumps(record, separators=(",", ":")) + "\n")
                if binary:
                    board, hands, side = encode_sfen(record["sfen"])
                    binary.write(struct.pack("<81B14BbBH", *board, *hands, side,
                                             record["value"], len(policy)))
                    for move, count in policy:
                        encoded = move.encode("ascii")
                        if len(encoded) > 8:
                            raise ValueError("move encoding too long")
                        binary.write(struct.pack("<8sI", encoded, count))
                records += 1
            except (ValueError, TypeError, json.JSONDecodeError) as error:
                print(f"{args.input}:{line_number}: {error}", file=sys.stderr)
                return 1
    if binary:
        binary.close()
    print(f"validated {records} records", file=sys.stderr)
    return 0


def encode_sfen(sfen):
    fields = sfen.split()
    if len(fields) != 4 or fields[1] not in ("b", "w"):
        raise ValueError("invalid sfen")
    board = []
    piece_types = {"p": 1, "l": 2, "n": 3, "s": 4, "g": 5,
                   "b": 6, "r": 7, "k": 8}
    for row in fields[0].split("/"):
        expanded = []
        promoted = False
        for token in row:
            if token.isdigit():
                expanded.extend([0] * int(token))
            elif token == "+":
                promoted = True
            else:
                base = piece_types[token.lower()]
                if promoted:
                    base += 8
                    promoted = False
                expanded.append(base if token.isupper() else base + 14)
        if len(expanded) != 9:
            raise ValueError("invalid sfen board row")
        board.extend(expanded)
    if len(board) != 81:
        raise ValueError("invalid sfen board")
    hands = [0] * 14
    if fields[2] != "-":
        hand_types = {"r": 0, "b": 1, "g": 2, "s": 3, "n": 4, "l": 5, "p": 6}
        amount = 0
        color = 0
        for token in fields[2]:
            if token.isdigit():
                amount = amount * 10 + int(token)
                continue
            if token.lower() not in hand_types:
                raise ValueError("invalid sfen hand")
            if amount == 0:
                amount = 1
            color = 0 if token.isupper() else 1
            hands[color * 7 + hand_types[token.lower()]] = amount
            amount = 0
    return board, hands, 0 if fields[1] == "b" else 1


if __name__ == "__main__":
    raise SystemExit(main())
