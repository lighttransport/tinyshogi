#!/usr/bin/env python3
"""M1: measure the maximum pseudo-move count over reachable positions.

Sources:
  1. selfplay corpora + greedy/random selfplay walks (reachable positions),
  2. construction search over invariant-valid positions: exact conserved
     multiset (2 kings + {18,4,4,4,4,2,2}), template scan over onboard counts,
     hill-climbing with type-consistent mutations.

Usage: python3 maxpseudo.py [--walks] [--climb] [--all]
"""
import argparse
import json
import os
import random
import subprocess
import sys
import tempfile

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(os.path.dirname(HERE))
SCRATCH = os.environ.get("COMMANDCODE_SCRATCHPAD", tempfile.gettempdir())
PROBE = os.path.join(SCRATCH, "maxpseudo")
CORPORA = [
    os.path.join(ROOT, "selfplay-tiny-yaneuraou.jsonl"),
    os.path.join(ROOT, "selfplay-tiny-aobannue.jsonl"),
    os.path.join(ROOT, "selfplay-tiny-aobannue-plugin.jsonl"),
]
QUOTA = {"P": 18, "L": 4, "N": 4, "S": 4, "G": 4, "B": 2, "R": 2}
HAND_ORDER = "PLNSGBR"
# rough mobility maxima for template ranking (mover pieces)
MOBILITY = {"P": 2, "L": 9, "N": 2, "S": 6, "G": 6, "B": 17, "R": 17,
            "+P": 6, "+L": 6, "+N": 6, "+S": 6, "+G": 6, "+B": 24, "+R": 24}


def build_probe():
    subprocess.run(
        ["clang", "-std=c11", "-O2", "-Wall", "-Wextra", "-o", PROBE,
         os.path.join(HERE, "maxpseudo.c")],
        check=True, cwd=ROOT)


def evaluate(svens):
    out = []
    for i in range(0, len(svens), 400):
        batch = svens[i:i + 400]
        proc = subprocess.run([PROBE], input="\n".join(batch) + "\n",
                              capture_output=True, text=True, check=True)
        for line in proc.stdout.splitlines():
            count, _, sfen = line.partition(" ")
            out.append((None if count == "REJECT" else int(count), sfen))
    return out


def corpus_svens():
    Svens = []
    for path in CORPORA:
        if not os.path.exists(path):
            continue
        with open(path) as f:
            for line in f:
                try:
                    Svens.append(json.loads(line)["sfen"])
                except (json.JSONDecodeError, KeyError):
                    pass
    return Svens


def walks(seeds, games, plies):
    Svens = []
    for greedy in (1, 0):
        for seed in seeds:
            proc = subprocess.run(
                [PROBE, "walk", str(seed), str(games), str(plies), str(greedy)],
                capture_output=True, text=True, check=True)
            for line in proc.stdout.splitlines():
                Svens.append(line.split(" ", 2)[2])
    return Svens


# ---------------------------------------------------------------- constructions

class Pos:
    """cells[(side, where)] with where 0 = board (dict square->piece char),
    1 = hand (dict type->count). Conservation enforced by construction."""

    def __init__(self):
        self.board = {0: {}, 1: {}}
        self.hand = {0: {}, 1: {}}
        self.side = 0

    def clone(self):
        p = Pos.__new__(Pos)
        p.board = {0: dict(self.board[0]), 1: dict(self.board[1])}
        p.hand = {0: dict(self.hand[0]), 1: dict(self.hand[1])}
        p.side = self.side
        return p

    def sfen(self):
        rows = []
        for r in range(9):
            row, run = "", 0
            for c in range(9):
                pc = self.board[0].get((r, c)) or self.board[1].get((r, c))
                if pc is None:
                    run += 1
                else:
                    if run:
                        row += str(run)
                        run = 0
                    row += pc if pc[0] == "+" and pc[-1].isupper() else (
                        pc.upper() if pc.isupper() else pc)
                    # piece chars are already case-coded; just append
                    row = row[:-len(pc)] + pc
            if run:
                row += str(run)
            rows.append(row)

        def hs(h, upper):
            s = ""
            for t in HAND_ORDER:
                n = h.get(t, 0)
                if n:
                    s += (str(n) if n > 1 else "") + (t if upper else t.lower())
            return s
        hand = hs(self.hand[0], True) + hs(self.hand[1], False) or "-"
        return "%s %s %s 1" % ("/".join(rows), "bw"[self.side], hand)

    def squares(self):
        return list(self.board[0]) + list(self.board[1])

    def empties(self):
        occ = set(self.board[0]) | set(self.board[1])
        return [(r, c) for r in range(9) for c in range(9) if (r, c) not in occ]


def from_template(rng, onboard_mover, onboard_other):
    """Mover gets the `onboard_mover` most mobile pieces; other side gets
    `onboard_other` (king always); the rest goes to the mover's hand."""
    p = Pos()
    pool = []
    for t, cap in QUOTA.items():
        pool += [t] * cap
    # rank by mobility, prefer promoted forms for the mover's onboard pieces
    pool.sort(key=lambda t: -MOBILITY["+" + t])
    mover_on = ["+" + t for t in pool[:onboard_mover]]
    rest = pool[onboard_mover:]
    other_on = rest[:onboard_other]
    hand_types = rest[onboard_other:]
    empties = [(r, c) for r in range(9) for c in range(9) if not (r == 4 and c == 4)]
    p.board[0][(4, 4)] = "K"
    # other king
    for sq in rng.sample(empties, 1):
        p.board[1][sq] = "k"
        empties.remove(sq)
    # avoid dead placements for mover pieces: keep off the last two ranks for
    # unpromoted pawn/lance/knight (promoted forms are fine anywhere)
    def place(piece, sq):
        p.board[0][sq] = piece
        empties.remove(sq)
    for piece in mover_on:
        for _ in range(60):
            sq = rng.choice(empties)
            r = sq[0]
            base = piece.lstrip("+")
            if not piece.startswith("+") and base in "PLN" and r >= 9 - (1 if base in "PL" else 2):
                continue
            if base == "P" and not piece.startswith("+"):
                pass  # nifu checked by C anyway; pseudo unaffected
            place(piece, sq)
            break
        else:
            hand_types.append(piece.lstrip("+"))
    for piece in other_on:
        for _ in range(60):
            sq = rng.choice(empties)
            base = piece.lstrip("+")
            if not piece.startswith("+") and base in "PLN" and sq[0] <= (1 if base in "PL" else 2):
                continue
            p.board[1][sq] = piece.lower() if not piece.startswith("+") else "+" + piece[-1].lower()
            empties.remove(sq)
            break
        else:
            hand_types.append(piece.lstrip("+"))
    for t in hand_types:
        p.hand[0][t] = p.hand[0].get(t, 0) + 1
    p.side = 0
    return p


def mutate(p, rng):
    q = p.clone()
    acts = range(8)
    act = rng.choice(acts)
    mover, other = 0, 1
    if q.side == 1:
        mover, other = 1, 0
    empties = q.empties()
    occ_m = list(q.board[mover])
    occ_o = list(q.board[other])
    if act == 0 and occ_m and empties:                    # relocate mover piece
        sq = rng.choice(occ_m)
        q.board[mover][rng.choice(empties)] = q.board[mover].pop(sq)
    elif act == 1 and len(occ_m) >= 2:                    # swap two mover pieces
        a, b = rng.sample(occ_m, 2)
        q.board[mover][a], q.board[mover][b] = q.board[mover][b], q.board[mover][a]
    elif act == 2 and occ_m:                              # promote/demote
        sq = rng.choice(occ_m)
        pc = q.board[mover][sq]
        if pc.startswith("+"):
            base = pc[1:]
            r, _ = sq
            if base in "PLN" and r >= 9 - (1 if base in "PL" else 2):
                return None                               # would be dead
            q.board[mover][sq] = base
        else:
            q.board[mover][sq] = "+" + pc
    elif act == 3 and occ_m:                              # mover board -> mover hand
        sq = rng.choice(occ_m)
        pc = q.board[mover].pop(sq)
        t = pc.lstrip("+")
        q.hand[mover][t] = q.hand[mover].get(t, 0) + 1
    elif act == 4:                                        # mover hand -> board
        cand = [t for t in q.hand[mover] if q.hand[mover][t] > 0]
        if not cand or not empties:
            return None
        t = rng.choice(cand)
        piece = ("+" if rng.random() < 0.7 else "") + t
        for _ in range(20):
            sq = rng.choice(empties)
            r = sq[0]
            if not piece.startswith("+") and t in "PLN" and r >= 9 - (1 if t in "PL" else 2):
                continue
            q.board[mover][sq] = piece
            empties.remove(sq)
            break
        else:
            return None
        q.hand[mover][t] -= 1
        if not q.hand[mover][t]:
            del q.hand[mover][t]
    elif act == 5:                                        # flip side
        q.side = 1 - q.side
    elif act == 6 and occ_o:                              # demote other-side piece / shift it
        sq = rng.choice(occ_o)
        pc = q.board[other][sq]
        if pc.startswith("+") and rng.random() < 0.5:
            base = pc[1:]
            r = sq[0]
            if base in "PLN" and r <= (1 if base in "PL" else 2):
                return None
            q.board[other][sq] = base
        else:
            e = q.empties()
            if not e:
                return None
            q.board[other][rng.choice(e)] = q.board[other].pop(sq)
    else:                                                 # rebalance a hand count (conserved)
        t = rng.choice(list(QUOTA))
        src = mover if q.hand[mover].get(t, 0) > 0 else other
        if q.hand[src].get(t, 0) == 0:
            return None
        q.hand[src][t] -= 1
        if not q.hand[src][t]:
            del q.hand[src][t]
        q.hand[1 - src][t] = q.hand[1 - src].get(t, 0) + 1
    return q


def local_search(p0, eval_batch, rng, max_sweeps=40, cache=None):
    """Sweep local moves (relocate/promote/demote/board-hand/side), evaluating
    each sweep's candidates in batch; accept the best candidate if it does not
    decrease the count. Returns (pos, count)."""
    cur, cur_c = p0, None

    def count_of(pos):
        nonlocal cur_c
        if cur_c is None:
            (cnt, ) = [c for c, _ in eval_batch([pos.sfen()])]
            cur_c = cnt
        return cur_c

    count_of(cur)
    if cur_c is None:
        return None, None
    for _ in range(max_sweeps):
        cands = []
        mover = cur.side
        other = 1 - mover
        occ = list(cur.board[mover])
        empties = cur.empties()
        # relocate each piece to every empty square
        for sq in occ:
            if cur.board[mover][sq] in ("K", "k"):
                continue
            for e in empties:
                q = cur.clone()
                q.board[mover][e] = q.board[mover].pop(sq)
                cands.append(q)
        # promote / demote each piece
        for sq in occ:
            pc = cur.board[mover][sq]
            if pc.startswith("+"):
                base = pc[1:]
                r = sq[0]
                if base in "PLN" and r >= 9 - (1 if base in "PL" else 2):
                    continue
                q = cur.clone()
                q.board[mover][sq] = base
                cands.append(q)
            elif pc in ("P", "L", "N", "S", "B", "R"):
                q = cur.clone()
                q.board[mover][sq] = "+" + pc
                cands.append(q)
        # board <-> hand for each family
        for sq in occ:
            pc = cur.board[mover][sq]
            if pc in ("K", "k"):
                continue
            q = cur.clone()
            t = pc.lstrip("+")
            del q.board[mover][sq]
            q.hand[mover][t] = q.hand[mover].get(t, 0) + 1
            cands.append(q)
        for t, n in cur.hand[mover].items():
            if n <= 0 or not empties:
                continue
            for e in empties:
                for prom in (False, True):
                    piece = ("+" if prom else "") + t
                    r = e[0]
                    if not prom and t in "PLN" and r >= 9 - (1 if t in "PL" else 2):
                        continue
                    q = cur.clone()
                    q.board[mover][e] = piece
                    q.hand[mover][t] -= 1
                    if not q.hand[mover][t]:
                        del q.hand[mover][t]
                    cands.append(q)
        # rebalance: move one piece of a family between hands
        for t in QUOTA:
            for src in (0, 1):
                if cur.hand[src].get(t, 0) <= 0:
                    continue
                q = cur.clone()
                q.hand[src][t] -= 1
                if not q.hand[src][t]:
                    del q.hand[src][t]
                q.hand[1 - src][t] = q.hand[1 - src].get(t, 0) + 1
                cands.append(q)
        # side flip
        q = cur.clone()
        q.side = 1 - q.side
        cands.append(q)
        # shift an opponent piece
        for sq in list(cur.board[other]):
            if cur.board[other][sq] == "k":
                continue
            for e in empties:
                q = cur.clone()
                q.board[other][e] = q.board[other].pop(sq)
                cands.append(q)
            pc = cur.board[other][sq]
            if pc.startswith("+"):
                base = pc[1:]
                r = sq[0]
                if base in "PLN" and r <= (1 if base in "PL" else 2):
                    continue
                q = cur.clone()
                q.board[other][sq] = base
                cands.append(q)
        if not cands:
            break
        Svens = [q.sfen() for q in cands]
        scored = eval_batch(Svens)
        best_q, best_c, best_sf = None, cur_c, None
        for q, sf, (cnt, _) in zip(cands, Svens, scored):
            if cnt is None:
                continue
            if cache is not None:
                cache[sf] = cnt
            if cnt > best_c or (cnt == best_c and rng.random() < 0.3):
                best_q, best_c, best_sf = q, cnt, sf
        if best_q is None:
            break
        cur, cur_c = best_q, best_c
    return cur, cur_c


def climb(starts, rng, steps, eval_batch):
    best = {}
    todo = list(starts)
    for cnt, sf in eval_batch(todo):
        if cnt is not None:
            best[sf] = cnt
    pool = [(c, s) for s, c in best.items()]
    if not pool:
        return best
    results = []
    for c0, s0 in sorted(pool, reverse=True)[:24]:
        cur = sfen_to_pos(s0)
        cur_c = c0
        results.append((c0, s0))
        for _ in range(steps):
            m = mutate(cur, rng)
            if m is None:
                continue
            sf = m.sfen()
            if sf in best:
                cnt = best[sf]
            else:
                (cnt, ) = [c for c, _ in eval_batch([sf])]
                if cnt is None:
                    continue
                best[sf] = cnt
            if cnt >= cur_c:
                cur, cur_c = m, cnt
                results.append((cnt, sf))
    return best, results


def sfen_to_pos(sfen):
    b, side, hand, _ = sfen.split(" ")
    p = Pos()
    r = c = 0
    prom = False
    for ch in b:
        if ch == "+":
            prom = True
            continue
        if ch == "/":
            r, c, prom = r + 1, 0, False
            continue
        if ch.isdigit():
            c += int(ch)
            continue
        pc = ("+" if prom else "") + ch
        p.board[0 if ch.isupper() else 1][(r, c)] = pc
        c += 1
        prom = False
    idx = 0
    num = ""
    for ch in hand:
        if ch.isdigit():
            num += ch
            continue
        if ch == "-":
            break
        n = int(num) if num else 1
        num = ""
        t = ch.upper()
        if t in QUOTA:
            p.hand[0 if ch.isupper() else 1][t] = p.hand[0 if ch.isupper() else 1].get(t, 0) + n
    p.side = 0 if side == "b" else 1
    return p


def curated_templates():
    """Configs from the marginal-value analysis: an onboard piece of family i
    is worth mobility(i) - (drop-square value of its square); only dragons,
    horses, and lances are net-positive, and hand[i] must stay >= 1 for every
    family to keep that family's drops. Opponent = bare king on the back rank;
    kings and lances on the back rank keep drop rows intact."""
    def row_str(pieces):
        s, run = "", 0
        for c in range(9):
            pc = pieces.get(c)
            if pc is None:
                run += 1
            else:
                s += (str(run) if run else "") + pc
                run = 0
        return s + (str(run) if run else "")

    out = []
    spots = [(4, 3), (2, 5), (4, 5), (2, 3), (0, 0), (0, 8), (1, 4), (2, 4)]
    for d, h, l in ((1, 1, 0), (1, 1, 1), (1, 1, 2), (1, 1, 3), (1, 1, 4),
                    (0, 1, 3), (1, 0, 3), (2, 2, 0), (2, 2, 3), (0, 0, 4),
                    (2, 1, 3), (1, 2, 3), (2, 2, 1)):
        rows = ["9"] * 9
        back = {c: "L" for c in range(l)}
        back[8] = "K"
        back[6] = "k"
        rows[8] = row_str(back)
        majors = ["+R"] * d + ["+B"] * h
        for pc, (r, c) in zip(majors, spots):
            row = {} if rows[r] == "9" else row_str_inv(rows[r])
            row[c] = pc
            rows[r] = row_str(row)
        hand = {"P": 18, "N": 4, "S": 4, "G": 4, "L": 4 - l, "B": 2 - h, "R": 2 - d}
        hs = "".join((str(n) if n > 1 else "") + t for t, n in hand.items() if n)
        out.append("/".join(rows) + " b " + (hs or "-") + " 1")
    return out


def row_str_inv(s):
    pieces, c, prom = {}, 0, False
    for ch in s:
        if ch == "+":
            prom = True
            continue
        if ch.isdigit():
            c += int(ch)
            continue
        pieces[c] = ("+" if prom else "") + ch
        c += 1
        prom = False
    return pieces


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--walks", action="store_true")
    ap.add_argument("--climb", action="store_true")
    ap.add_argument("--all", action="store_true")
    args = ap.parse_args()
    if not (args.walks or args.climb or args.all):
        args.all = True
    build_probe()
    rng = random.Random(0x5EC0)

    def eval_batch(xs):
        return evaluate(xs)

    svens, reachable = [], set()
    if args.all or args.walks:
        svens += corpus_svens()
        walk_svens = walks(seeds=range(1, 26), games=8, plies=150)
        svens += walk_svens
        reachable.update(walk_svens)
    best = {}
    counted = [(c, s) for c, s in eval_batch(svens) if c is not None]
    for c, s in counted:
        best[s] = c
    if args.all or args.climb:
        templates = [from_template(rng, k, o).sfen()
                     for k in range(0, 39, 2) for o in (0, 1, 3)]
        starts = [s for _, s in sorted(counted, key=lambda kv: -kv[0])[:12]]
        seeds = list(dict.fromkeys(curated_templates() + templates + starts))
        counted_seeds = [(c, s) for c, s in eval_batch(seeds) if c is not None]
        for c, s in counted_seeds:
            best[s] = c
        pool = [(c, s) for s, c in best.items()]
        for c0, s0 in sorted(pool, reverse=True)[:20]:
            p = sfen_to_pos(s0)
            for kick in range(3):
                for _ in range(kick * 3):
                    m = mutate(p, rng)
                    if m is not None:
                        p = m
                p2, c2 = local_search(p, eval_batch, rng)
                if p2 is not None and c2 is not None:
                    best[p2.sfen()] = c2
                    if c2 >= c0:
                        p = p2
                        c0 = c2
                    else:
                        p = sfen_to_pos(s0)
    # verification pass: re-evaluate every recorded candidate; keep only
    # entries the probe confirms (guards against any bookkeeping drift).
    verified = {}
    items = sorted(best.items(), key=lambda kv: -kv[1])
    for sf, c in items[:200]:
        cnt, _ = evaluate([sf])[0]
        if cnt == c:
            verified[sf] = c
    top = sorted(verified.items(), key=lambda kv: -kv[1])[:10]
    for sfen, count in top:
        print("%4d  %s" % (count, sfen))
    walk_max = max((c for s, c in verified.items() if s in reachable), default=0)
    print("CONSTRUCTION_MAX %d" % max(verified.values(), default=0))
    print("WALK_MAX %d" % walk_max)


if __name__ == "__main__":
    main()
