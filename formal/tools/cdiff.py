#!/usr/bin/env python3
"""Differential test: compiled src/shogi.c (ASan/UBSan) vs the Lean spec.

Current coverage (T1): SFEN parse + print on the fuzz corpus, the
tests/test_rules.c fixtures, and random byte-level mutations of them.
Both sides read hex-encoded lines and print the re-serialised SFEN or
REJECT; any difference is a failure.

Usage: python3 tools/cdiff.py [--n 2000] [--seed 1]
"""
import argparse, os, random, re, subprocess, sys, tempfile

HERE = os.path.dirname(os.path.abspath(__file__))
FORMAL = os.path.dirname(HERE)
ROOT = os.path.dirname(FORMAL)
CC = os.environ.get("CC", "clang")

ALPHABET = b"plnsgbrkPLNSGBRK+/-0123456789bw \t\r\n*xZ\xc3\xa9"


def seeds():
    out = []
    corpus = os.path.join(ROOT, "fuzz", "corpus")
    for name in sorted(os.listdir(corpus)):
        with open(os.path.join(corpus, name), "rb") as f:
            out.append(f.read().split(b"\0")[0].rstrip(b"\n"))
    with open(os.path.join(ROOT, "tests", "test_rules.c"), "rb") as f:
        out += [m.group(1) for m in re.finditer(rb'"([^"\n]*/[^"\n]* [bw] [^"\n]*)"', f.read())]
    return [s for s in out if b"\0" not in s]


def mutate(rng, s):
    s = bytearray(s)
    for _ in range(rng.randint(1, 3)):
        op = rng.randrange(4)
        i = rng.randrange(len(s) + 1)
        c = rng.choice(ALPHABET)
        if op == 0 and s:
            s[min(i, len(s) - 1)] = c
        elif op == 1:
            s.insert(i, c)
        elif op == 2 and s:
            del s[min(i, len(s) - 1)]
        else:
            s[i:i] = str(rng.choice([0, 1, 18, 19, 4294967295, 4294967296, 2**64])).encode()
    return bytes(s)


FAMILY = "plnsgbr"
MAXF = [18, 4, 4, 4, 4, 2, 2]


def random_position(rng):
    """A random SFEN within material limits (dead pieces allowed, as in C)."""
    board = [None] * 81
    sq = rng.sample(range(81), 2)
    board[sq[0]], board[sq[1]] = "K", "k"
    hand = {}
    for f, m in zip(FAMILY, MAXF):
        for _ in range(rng.randint(0, m)):
            where = rng.random()
            letter = f.upper() if rng.random() < 0.5 else f
            if where < 0.6:
                free = [i for i in range(81) if board[i] is None]
                promo = "+" if f not in "g" and rng.random() < 0.3 else ""
                board[rng.choice(free)] = promo + letter
            else:
                hand[letter] = hand.get(letter, 0) + 1
    rows = []
    for r in range(9):
        out, e = "", 0
        for c in range(9):
            x = board[r * 9 + c]
            if x is None:
                e += 1
            else:
                out += (str(e) if e else "") + x
                e = 0
        rows.append(out + (str(e) if e else ""))
    keys = list(hand)
    rng.shuffle(keys)   # unnormalised order and counts on purpose
    h = "".join((str(hand[k]) if hand[k] > 1 or rng.random() < 0.2 else "") + k for k in keys) or "-"
    return f"{'/'.join(rows)} {rng.choice('bw')} {h} {rng.randint(1, 500)}".encode()


def run(cmd, inputs):
    data = "".join(x.hex() + "\n" for x in inputs)
    return subprocess.run(cmd, input=data, capture_output=True, text=True,
                          check=True).stdout.splitlines()


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--n", type=int, default=2000)
    ap.add_argument("--seed", type=int, default=1)
    args = ap.parse_args()
    rng = random.Random(args.seed)
    base = seeds()
    gen = [random_position(rng) for _ in range(args.n)]
    inputs = base + gen + [mutate(rng, rng.choice(base + gen)) for _ in range(args.n)]
    inputs.append(b"4k4/9/9/9/9/9/9/9/4K4 b - 1" + b" " * 490)   # >= 512 bytes
    with tempfile.TemporaryDirectory() as d:
        exe = os.path.join(d, "cdiff_c")
        subprocess.check_call([CC, "-std=c11", "-O1", "-g", "-fsanitize=address,undefined",
                               "-fno-sanitize-recover=all", "-o", exe,
                               os.path.join(HERE, "cdiff_c.c"), os.path.join(ROOT, "src", "shogi.c")])
        c_out = run([exe], inputs)
    subprocess.check_call(["lake", "build", "cdiff"], cwd=FORMAL, stdout=subprocess.DEVNULL)
    lean_out = run([os.path.join(FORMAL, ".lake", "build", "bin", "cdiff")], inputs)
    bad = [(i, c, l) for i, c, l in zip(inputs, c_out, lean_out) if c != l]
    if len(c_out) != len(inputs) or len(lean_out) != len(inputs):
        print("cdiff: output length mismatch", file=sys.stderr)
        return 1
    accepted = sum(1 for c in c_out if c != "REJECT")
    for i, c, l in bad[:20]:
        print(f"MISMATCH input={i!r}\n  C:    {c}\n  Lean: {l}")
    print(f"cdiff: {len(inputs)} inputs, {accepted} accepted, {len(bad)} mismatches")
    return 1 if bad else 0


if __name__ == "__main__":
    sys.exit(main())
