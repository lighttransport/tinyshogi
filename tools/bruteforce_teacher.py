#!/usr/bin/env python3
"""Label SFEN positions with a bounded TinyShogi USI search."""

import argparse
import json
import selectors
import subprocess
import sys


class Engine:
    def __init__(self, path, timeout):
        self.process = subprocess.Popen([path], stdin=subprocess.PIPE,
                                        stdout=subprocess.PIPE, bufsize=0)
        self.selector = selectors.DefaultSelector()
        self.selector.register(self.process.stdout, selectors.EVENT_READ)
        self.timeout = timeout
        self.send("usi")
        self.read_until("usiok")
        self.send("setoption name Threads value 1")
        self.send("isready")
        self.read_until("readyok")

    def send(self, command):
        self.process.stdin.write((command + "\n").encode())
        self.process.stdin.flush()

    def read_until(self, marker):
        while True:
            if not self.selector.select(self.timeout):
                raise RuntimeError("timeout waiting for " + marker)
            line = self.process.stdout.readline().decode(errors="replace").strip()
            if line == marker or line.startswith(marker + " "):
                return line

    def label(self, sfen, nodes):
        self.send("position sfen " + sfen)
        self.send("go nodes " + str(nodes))
        score = 0
        move = "resign"
        while True:
            if not self.selector.select(self.timeout):
                raise RuntimeError("timeout during teacher search")
            line = self.process.stdout.readline().decode(errors="replace").strip()
            fields = line.split()
            if len(fields) >= 3 and fields[0] == "info":
                for index, field in enumerate(fields[:-1]):
                    if field == "score" and fields[index + 1] == "cp":
                        try:
                            score = int(fields[index + 2])
                        except (ValueError, IndexError):
                            pass
            if fields and fields[0] == "bestmove":
                if len(fields) > 1:
                    move = fields[1]
                return move, max(-1000, min(1000, score))

    def close(self):
        if self.process.poll() is None:
            self.send("quit")
            self.process.wait(timeout=2)
        self.selector.close()


class BruteServer:
    def __init__(self, path, timeout):
        self.process = subprocess.Popen([path], stdin=subprocess.PIPE,
                                        stdout=subprocess.PIPE, bufsize=0)
        self.selector = selectors.DefaultSelector()
        self.selector.register(self.process.stdout, selectors.EVENT_READ)
        self.timeout = timeout

    def label(self, sfen, depth):
        self.process.stdin.write((sfen + "\t" + str(depth) + "\n").encode())
        self.process.stdin.flush()
        if not self.selector.select(self.timeout):
            raise RuntimeError("timeout during brute-force search")
        fields = self.process.stdout.readline().decode(errors="replace").split()
        if len(fields) != 3 or fields[0] == "error":
            raise RuntimeError("invalid brute-force teacher response")
        return fields[0], max(-1000, min(1000, int(fields[1])))

    def close(self):
        if self.process.poll() is None:
            self.process.terminate()
            self.process.wait(timeout=2)
        self.selector.close()


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("input", help="JSONL containing SFEN records")
    parser.add_argument("output")
    parser.add_argument("--engine", default="build/tinyshogi")
    parser.add_argument("--brute-server", help="native brute-force teacher server")
    parser.add_argument("--nodes", type=int, default=256)
    parser.add_argument("--depth", type=int, default=2)
    parser.add_argument("--timeout", type=float, default=30.0)
    parser.add_argument("--limit", type=int, default=0)
    args = parser.parse_args()
    if args.nodes < 1 or args.depth < 1 or args.limit < 0:
        parser.error("nodes/depth must be positive and limit must be non-negative")
    engine = BruteServer(args.brute_server, args.timeout) if args.brute_server else Engine(args.engine, args.timeout)
    count = 0
    try:
        with open(args.input, encoding="utf-8") as source, open(args.output, "w", encoding="utf-8") as destination:
            for line in source:
                if not line.strip():
                    continue
                record = json.loads(line)
                record["teacher_move"], score = engine.label(
                    record["sfen"], args.depth if args.brute_server else args.nodes)
                record["teacher_value"] = score / 1000.0
                destination.write(json.dumps(record, separators=(",", ":")) + "\n")
                count += 1
                if count % 100 == 0:
                    print(f"labeled {count}", file=sys.stderr)
                if args.limit and count >= args.limit:
                    break
    finally:
        engine.close()
    print(f"wrote {count} teacher records", file=sys.stderr)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
