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


class Proc:
    """A request/response pipe to one side (C or Lean)."""

    def __init__(self, cmd):
        self.p = subprocess.Popen(cmd, stdin=subprocess.PIPE, stdout=subprocess.PIPE, text=True)

    def ask(self, cmd, payload):
        self.p.stdin.write(f"{cmd} {payload.hex()}\n")
        self.p.stdin.flush()
        return self.p.stdout.readline().rstrip("\n")

    def batch(self, cmd, payloads):
        out = subprocess.run(self.p.args, input="".join(f"{cmd} {x.hex()}\n" for x in payloads),
                             capture_output=True, text=True, check=True).stdout.splitlines()
        if len(out) != len(payloads):
            raise RuntimeError("output length mismatch")
        return out

    def close(self):
        self.p.stdin.close()
        self.p.wait()


EDGE = [
    # tests/test_rules.c: uchifuzume, pins, nifu, dead drops, repetition gates
    b"4k4/9/2NG1GN2/9/9/9/9/9/4K4 b P 1",
    b"4k4/9/9/9/4P4/9/9/9/4K4 b P 1",
    b"4k4/9/9/9/9/9/9/9/4K4 b N 1",
    b"4r3k/9/9/9/9/9/9/4R4/4K4 b - 1",
    b"4k4/9/9/9/9/5+b3/4R4/3K5/9 b - 1",
    # pawn-drop check that is not mate (king can escape / capture)
    b"4k4/9/3G5/9/9/9/9/9/4K4 b P 1",
    b"8k/9/7G1/9/9/9/9/9/K8 b P 1",
    # nested uchifuzume: replies themselves include pawn-drop checks
    b"k8/2G6/1P7/9/9/9/7p1/6g2/8K b Pp 1",
    # forced promotion of knight/lance/pawn, and dead drops for white
    b"4k4/2N6/1L1P5/9/9/9/9/9/4K4 b NLP 1",
    b"4k4/9/9/9/9/9/5p1l1/6n2/4K4 w nlp 1",
    # uchifuzume where the only capture is by a pinned gold (python-shogi
    # 1.1.1 wrongly allows P*9h here)
    b"9/9/gN7/P3+s4/4+p4/3g1L+s1p/k1p5p/3+PPP3/KG2r4 w 3pSs2P 45",
    # many drops
    b"4k4/9/9/9/9/9/9/9/4K4 b RBGSNLP 1",
    b"4k4/9/9/9/9/9/9/9/4K4 w rbgsnlp 1",
]


def oracle_legal(sfen):
    """python-shogi 1.1.1 legal moves (sorted USI), or None if it cannot load
    the position (python-shogi rejects some analysis positions the C accepts)."""
    import shogi
    try:
        board = shogi.Board(sfen.decode())
        moves = list(board.legal_moves)
        # The side not to move is in check: not reachable by play. python-shogi
        # then generates king captures, which C and the spec never generate.
        if any((pc := board.piece_at(m.to_square)) and pc.piece_type == shogi.KING
               for m in moves):
            return None
        return " ".join(sorted(m.usi() for m in moves))
    except Exception:
        return None


ORACLE = {"checked": 0, "skipped": 0, "uchifuzume_bug": 0}


def python_shogi_uchifuzume_bug(sfen, move):
    """python-shogi 1.1.1 allows a pawn-drop mate when the only capture of
    the pawn is by a pinned piece. Recognise it by python-shogi's own verdict:
    after the drop it reports checkmate."""
    import shogi
    if not move.startswith("P*"):
        return False
    board = shogi.Board(sfen.decode())
    board.push_usi(move)
    return board.is_checkmate()


def check_oracle(label, sfen, c_legal):
    o = oracle_legal(sfen)
    if o is None:
        ORACLE["skipped"] += 1
        return 0
    ORACLE["checked"] += 1
    if o != c_legal:
        cs, os_ = set(c_legal.split()), set(o.split())
        if not (cs - os_) and all(python_shogi_uchifuzume_bug(sfen, m) for m in os_ - cs):
            ORACLE["uchifuzume_bug"] += 1
            return 0
        print(f"MISMATCH [{label} python-shogi] sfen={sfen!r}\n"
              f"  only C/Lean: {sorted(cs - os_)}\n  only python-shogi: {sorted(os_ - cs)}")
        return 1
    return 0


def compare(label, inputs, c_out, l_out, limit=20):
    bad = [(i, c, l) for i, c, l in zip(inputs, c_out, l_out) if c != l]
    for i, c, l in bad[:limit]:
        print(f"MISMATCH [{label}] input={i!r}\n  C:    {c}\n  Lean: {l}")
    return len(bad)


def walk(rng, c, lean, start, plies, oracle=False):
    """Play random legal moves, comparing legal sets and resulting SFENs."""
    sfen, bad = start, 0
    for _ in range(plies):
        lc, ll = c.ask("L", sfen), lean.ask("L", sfen)
        if lc != ll:
            print(f"MISMATCH [walk L] sfen={sfen!r}")
            cs, ls = set(lc.split()), set(ll.split())
            print(f"  only C: {sorted(cs - ls)}\n  only Lean: {sorted(ls - cs)}")
            return 1
        if oracle and lc != "REJECT" and check_oracle("walk", sfen, lc):
            return 1
        moves = lc.split()
        if not moves or lc == "REJECT":
            return bad
        mv = rng.choice(moves).encode()
        nc, nl = c.ask("M", sfen + b"|" + mv), lean.ask("M", sfen + b"|" + mv)
        if nc != nl:
            print(f"MISMATCH [walk M] sfen={sfen!r} move={mv!r}\n  C:    {nc}\n  Lean: {nl}")
            return 1
        sfen = nc.encode()
    return bad


GAME_FIXTURES = [
    # tests/test_rules.c: fourfold repetition draw; perpetual check (White wins)
    (b"4k4/9/9/9/9/9/9/9/4K4 b - 1", b"5i5h 5a5b 5h5i 5b5a " * 3),
    (b"4R3k/9/9/9/9/9/9/9/K8 w - 1", b"1a1b 5a5b 1b1a 5b5a " * 3),
    # three repetitions only: still ongoing
    (b"4k4/9/9/9/9/9/9/9/4K4 b - 1", b"5i5h 5a5b 5h5i 5b5a " * 2 + b"5i5h 5a5b 5h5i"),
    # move counter at UINT_MAX - 1: the second move is refused
    (b"4k4/9/9/9/9/9/9/9/4K4 b - 4294967294", b"5i5h 5a5b"),
    # mate: no legal move for the side to move
    (b"4k4/4G4/4P4/9/9/9/9/9/4K4 w - 1", b""),
]

SMALL = [b"4k4/9/9/9/9/9/9/9/4K4 b - 1", b"4k4/9/9/9/9/9/9/4R4/4K4 b - 1",
         b"k8/9/9/9/9/9/9/9/7RK b - 1", b"4k4/9/9/9/9/9/9/9/4K4 b G 1",
         b"3gkg3/9/9/9/9/9/9/9/3GKG3 b - 1", b"8k/9/9/9/9/9/9/9/K3R4 w - 1"]


def camp_position(rng):
    """Random position with many black pieces in black's camp (declaration)."""
    board = [None] * 81
    board[rng.randrange(0, 27)] = "K"
    board[rng.randrange(54, 81)] = "k"
    left = {"P": 9, "G": 3, "S": 4, "B": 1, "R": 1, "N": 4, "L": 4}
    for _ in range(rng.randint(6, 18)):
        free = [i for i in range(27) if board[i] is None]
        f = rng.choice([k for k, v in left.items() if v > 0])
        left[f] -= 1
        promo = "+" if f in "PSBRNL" and rng.random() < 0.3 else ""
        board[rng.choice(free)] = promo + (f if rng.random() < 0.85 else f.lower())
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
    hand = rng.choice(["-", "P", "2P", "B", "R", "RB", "4P", "G", "rb", "2p"])
    return f"{'/'.join(rows)} {rng.choice('bw')} {hand} 1".encode()


def cycle_game(rng, c):
    """Random prefix, then a reversible 4-ply cycle played 3-4 times."""
    start = rng.choice(SMALL + [b"lnsgkgsnl/1r5b1/ppppppppp/9/9/9/PPPPPPPPP/1B5R1/LNSGKGSNL b - 1"])
    sfen, moves = start, []

    def play(mv):
        nonlocal sfen
        nxt = c.ask("M", sfen + b"|" + mv.encode())
        if nxt == "ILLEGAL":
            return False
        sfen = nxt.encode()
        moves.append(mv)
        return True

    for _ in range(rng.randint(0, 12)):
        legal = c.ask("L", sfen).split()
        if not legal:
            return None
        play(rng.choice(legal))
    quiet = lambda ms: [m for m in ms if "*" not in m and "+" not in m]
    a_opts = quiet(c.ask("L", sfen).split())
    if not a_opts:
        return None
    a = rng.choice(a_opts)
    play(a)
    b_opts = quiet(c.ask("L", sfen).split())
    if not b_opts:
        return None
    b = rng.choice(b_opts)
    play(b)
    cycle = [a, b, a[2:4] + a[0:2], b[2:4] + b[0:2]]
    for mv in cycle[2:]:
        if not play(mv):
            return None
    for _ in range(rng.choice([2, 3])):
        for mv in cycle:
            if not play(mv):
                return (start, " ".join(moves).encode())
    return (start, " ".join(moves).encode())


def game_tests(rng, c, lean, n):
    bad, results = 0, {}
    cases = list(GAME_FIXTURES)
    for _ in range(n):
        start = rng.choice(SMALL)
        sfen, moves = start, []
        for _ in range(rng.randint(10, 300)):
            if moves and c.ask("G", start + b"|" + " ".join(moves).encode()).split()[0] != "ONGOING":
                break
            legal = c.ask("L", sfen).split()
            if not legal:
                break
            mv = rng.choice(legal)
            moves.append(mv)
            sfen = c.ask("M", sfen + b"|" + mv.encode()).encode()
        cases.append((start, " ".join(moves).encode()))
    cases += [(camp_position(rng), b"") for _ in range(n)]
    cases += [x for x in (cycle_game(rng, c) for _ in range(n)) if x]
    for start, moves in cases:
        payload = start + b"|" + moves
        rc, rl = c.ask("G", payload), lean.ask("G", payload)
        results[rc.split()[0]] = results.get(rc.split()[0], 0) + 1
        if rc != rl:
            print(f"MISMATCH [G] start={start!r} moves={moves!r}\n  C:    {rc}\n  Lean: {rl}")
            bad += 1
    return bad, results


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--n", type=int, default=2000, help="SFEN / random-position inputs")
    ap.add_argument("--walks", type=int, default=50)
    ap.add_argument("--plies", type=int, default=120)
    ap.add_argument("--seed", type=int, default=1)
    ap.add_argument("--games", type=int, default=200)
    ap.add_argument("--mini", type=int, default=40,
                    help="positions for the MiniC-model attack checks (four-way)")
    ap.add_argument("--oracle", action="store_true", help="also compare with python-shogi 1.1.1")
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
                               os.path.join(HERE, "cdiff_c.c")])
        subprocess.check_call(["lake", "build", "cdiff"], cwd=FORMAL, stdout=subprocess.DEVNULL)
        lean_exe = os.path.join(FORMAL, ".lake", "build", "bin", "cdiff")
        c, lean = Proc([exe]), Proc([lean_exe])
        bad = 0
        out_c, out_l = c.batch("S", inputs), lean.batch("S", inputs)
        bad += compare("S", inputs, out_c, out_l)
        accepted = sum(1 for x in out_c if x != "REJECT")
        legal_inputs = EDGE + gen
        legal_c = c.batch("L", legal_inputs)
        bad += compare("L", legal_inputs, legal_c, lean.batch("L", legal_inputs))
        if args.oracle:
            for sfen, lc in zip(legal_inputs, legal_c):
                if lc != "REJECT":
                    bad += check_oracle("L", sfen, lc)
        start = b"lnsgkgsnl/1r5b1/ppppppppp/9/9/9/PPPPPPPPP/1B5R1/LNSGKGSNL b - 1"
        openings = os.path.join(ROOT, "runs", "strength", "openings", "development.sfens")
        starts = [start] + EDGE
        if os.path.exists(openings):
            with open(openings, "rb") as f:
                starts += [l.strip() for l in f if l.strip()]
        for k in range(args.walks):
            bad += walk(rng, c, lean, rng.choice(starts) if k else start, args.plies, args.oracle)
        # Four-way on the attack layer: compiled C == MiniC model of the same
        # C (Shogi.C.Gen) == spec, for every target square / colour, and for
        # every (from, to) pair of shogi_piece_attacks_square.
        mini = (EDGE + gen)[:args.mini]
        for cmd_spec, cmd_mini in (("A", "a"), ("X", "x")):
            cs = c.batch(cmd_spec, mini)
            bad += compare(cmd_spec + " spec", mini, cs, lean.batch(cmd_spec, mini))
            bad += compare(cmd_mini + " MiniC", mini, cs, lean.batch(cmd_mini, mini))
        gbad, results = game_tests(rng, c, lean, args.games)
        bad += gbad
        c.close()
        lean.close()
    print(f"cdiff: {len(inputs)} SFEN inputs ({accepted} accepted), "
          f"{len(legal_inputs)} legal-move positions, {args.walks} walks x {args.plies} plies, "
          f"games {results}, MiniC attack checks on {len((EDGE + gen)[:args.mini])} positions, "
          f"{bad} mismatches")
    if args.oracle:
        print(f"python-shogi: {ORACLE['checked']} positions compared, "
              f"{ORACLE['skipped']} skipped (side not to move in check), "
              f"{ORACLE['uchifuzume_bug']} known python-shogi pawn-drop-mate defects")
    return 1 if bad else 0


if __name__ == "__main__":
    sys.exit(main())
