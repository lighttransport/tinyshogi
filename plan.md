# Plan prompt: Lean 4 formalization and verification of shogi rules in tinyshogi

You are working in the `lighttransport/tinyshogi` repository (clean-room 9x9 shogi engine in C11, Apache-2.0). Your task in this session is **to produce an implementation plan, not to implement it**. Write the plan to `formal/PLAN.md` and stop for review.

## Goal

Add a `formal/` Lean 4 project to tinyshogi that:

1. **Specifies** standard shogi rules in Lean 4 as an executable, readable reference (the "spec").
2. **Proves** properties of that spec (rule invariants, generator soundness/completeness).
3. **C → Lean**: imports the tinyshogi rules core (C) into Lean and proves it refines the spec.
4. **Lean → C**: generates C for at least one rules component from Lean, with a machine-checked guarantee that the generated C refines its Lean source.
5. **Differentially tests** compiled C, the C model in Lean, the Lean spec, and `python-shogi` against each other.

## Prior art to reuse: tinygltf `formal/`

Read `https://github.com/syoyo/tinygltf/blob/release/formal/README.md` and the code under `formal/` on the `release` branch first. It already has the C → Lean pipeline we want to copy:

- `tools/c2lean.py`: reads `clang -Xclang -ast-dump=json`, takes types and implicit conversions from clang, measures record layouts with a probe compiled by the same compiler, emits `C/Gen.lean` (generated, never hand-edited), hoists loops into named `Stmt` defs (`…_loopN`), **rejects anything outside the subset instead of guessing**, and has `--check` to confirm `Gen.lean` matches the C source.
- `C/Semantics.lean`: MiniC, a ~500-line operational semantics; C11 UB maps to `ub`; pointers are (block, offset) pairs; LP64 little-endian.
- `C/Logic.lean`, `Hoare.lean`, `Lemmas.lean`, `Splice.lean`: proof rules.
- Refinement theorems of the form "for every input: no UB, terminates, returns the spec's result, writes only what the spec allows".
- `tools/cdiff.py`: compiled C (ASan/UBSan) == MiniC interpreter == Lean spec on random and adversarial inputs.
- Policy: `lake build` with no `sorry`, no Mathlib, no `native_decide`/`bv_decide`; only Lean's three standard axioms.

Decide in the plan whether to **vendor** these files into tinyshogi (with attribution; tinygltf is MIT, compatible with Apache-2.0), **share** them as a common package, or **fork and extend**. Expect MiniC to need extensions for tinyshogi (e.g. 64/128-bit bitboard ops, shifts, popcount/ctz builtins, fixed-size arrays of structs, `static const` tables). List each extension and how its semantics will be validated.

## Known references (from a survey; for orientation, not to copy)

- `Arthur742Ramos/chess-lean`: Lean 4 executable FIDE chess kernel; proves a reachable-position invariant by induction over legal moves; perft as regression tests. Closest model for the spec layer.
- `dwrensha/Chess.lean`, `elanroth/PuzzleProof`: forced-mate proofs as Lean theorems (future: tsume proofs).
- Wesselink et al., "Formal Verification of Minimax Algorithms" (Dafny, arXiv 2509.20138): useful later if search is verified; out of scope now.
- No prior Lean/Coq/Isabelle formalization of shogi was found. This would be the first.

## Phase 0: investigate before planning (report findings in PLAN.md)

1. Find the rules core in tinyshogi: board representation (bitboard or mailbox), move encoding, legal-move generation (including the "mutable make/unmake" path and target-centered attack detection), check detection, SFEN/USI parsing, repetition handling. List files and functions with line counts.
2. Run `c2lean.py` (from a tinygltf checkout) on those files unmodified and record every rejection. That gives the gap list for the C subset.
3. Look at `scripts/verify_rules.py` and the existing rules tests; reuse their positions as fixtures.
4. Find anything in the rules core that MiniC cannot model (threads, `volatile`, SIMD intrinsics, unions, function pointers, global mutable state) and propose either a refactor of the C or an exclusion boundary.

## Spec scope (Lean)

Model standard 9x9 shogi:

- Pieces, promotion, hands, side to move; SFEN parse/print with a round-trip theorem.
- Pseudo-legal moves for every piece, drops, promotion zone rules (optional/forced promotion).
- Illegal moves: leaving own king in check, **nifu** (two unpromoted pawns on a file), **dead pieces** (pawn/lance on last rank, knight on last two ranks, by move or drop), **uchifuzume** (pawn-drop mate).
- Terminal states: checkmate, plus **sennichite** (four-fold repetition, perpetual-check loss) modelled over a position history. Put entering-king (jishogi / 27-point declaration) in a separate optional module.

Spec theorems to plan for, roughly in order of difficulty:

- Piece conservation: 40 pieces on board plus hands in every reachable position; at most one king per side; no dead pieces on the board.
- `legalMoves` soundness and completeness against a declarative `isLegal`.
- `make`/`unmake` round-trip; SFEN round-trip.
- Uchifuzume is decided correctly (it needs the opponent's full legal-move set, so watch termination and proof cost).
- Perft regression values from the start position, depth 1–3 (30, 900, 25470) checked by `decide` or kernel evaluation. If the kernel is too slow without `native_decide`, keep deeper perft (719731 at depth 4) in `cdiff`/tests and say so.

## C → Lean (refinement)

- Choose the **verified core**: the smallest set of C functions that defines legality (attack detection, move generation, make/unmake, check, SFEN). Exclude search, eval, NNUE, SIMD, A64FX assembly, threading, WASM glue.
- Plan the refinement proofs bottom-up (bit helpers → attacks → per-piece generators → legality filters → full generator), with a theorem statement sketch for each layer, linking the C state to the spec state through an abstraction function.
- Flag the C changes needed to make proofs tractable (e.g. split functions, remove aliasing), keeping performance-critical paths intact. Measure perft and benchmark before and after any change.

## Lean → C (verified generation)

The tinygltf pipeline only goes C → Lean. Design the reverse direction, and prefer **translation validation over a verified compiler**:

1. Write the component in a small, first-order Lean subset (or a deep-embedded IR) that maps one-to-one onto the MiniC subset.
2. Emit C from it with an untrusted generator.
3. Re-import the emitted C with `c2lean.py` and prove, per generated function, that the MiniC model refines the Lean source. Then the generator is outside the trust base.

Pick one candidate component for the first iteration (e.g. attack tables, a piece move generator, or SFEN parsing) and justify the choice. Compare briefly with Lean's own compiler output (not verified) and any existing Lean → C verified-codegen projects you find. Note what each would add to the trust base.

## Differential testing

Extend a `cdiff`-style harness: compiled C under ASan/UBSan, MiniC interpreter on `Gen.lean`, Lean spec, and `python-shogi` (via `verify_rules.py`). Inputs: random legal games, SFEN fuzzing (reuse the `fuzz/` corpus), and hand-picked edge cases (uchifuzume, nifu, forced promotion, perpetual check).

## Trust base

State it explicitly, as tinygltf does: Lean kernel, MiniC semantics (plus its extensions), `c2lean.py` and the clang front end, target ABI, the C compiler (proofs do not reach machine code), and what is not modelled.

## Deliverable: `formal/PLAN.md`

It must contain:

1. Phase 0 findings (files, functions, c2lean rejection list, MiniC gaps).
2. Directory layout for `formal/`, and build/CI commands (`lake build`, `c2lean.py --check`, `cdiff`). Add a GitHub Actions job.
3. Milestones T1…Tn in tinygltf style, each with scope, theorem statements (Lean signatures), exit criteria, and a rough effort estimate.
4. The Lean → C design and first target.
5. Risks and open questions: proof cost of uchifuzume and sennichite, kernel evaluation speed without `native_decide`, MiniC extensions, C refactors.
6. What stays out of scope.

Do not write proofs or change C code in this session beyond throwaway experiments for Phase 0. Commit `formal/PLAN.md` on a new branch and open a draft PR for review.


## Status and remaining items (updated 2026-11-16, session 2)

Done on branch `formal-plan` (ahead of PR #2, not pushed):
`generate_legal_refines` (`formal/Shogi/C/Proofs/LegalMain.lean`) proves that
`generate_legal_mut_internal(…, 1)`, with an output array of ≥ 600 moves, writes
a reordering of the spec's `legalAux (fuel+1) p` and returns its length.
`lake build` passes with no `sorry`; the axiom check shows only propext,
Classical.choice and Quot.sound; `cdiff` has 0 mismatches.

Landed this session:

- `de86640` **`RecSpec` restated** (`LegalProbe.lean`): explicit spec-fuel
  parameter (contract is now "returned count nonzero iff `legalAux fuel q`
  nonempty"), a `ReplyBuf` side condition (3000 bytes at offset 0, disjoint
  from the allocator/position/table blocks), and a named allocation budget
  (`recBudget`). The hypothesis is now demanded **only for checking pawn
  drops** — the C recurses exactly there — threaded through
  `probe_path_drop`, `iter_slow`, `iter_one`, `legal_loop`,
  `generate_legal_main`, `generate_legal_refines`.
- `04133d8` **Geometric core of "at most one checking pawn drop"**
  (`OneCheckDrop.lean`, new): if the side not to move is not in check, a
  checking pawn drop attacks the opponent's king itself (a pawn attacks
  exactly one square; adding a piece never lengthens another piece's slide),
  which pins the drop square — so two checking pawn drops are the same move.
  Plus board-after-drop, `kingSquare`-invariance, slide monotonicity, pawn
  geometry and offset arithmetic lemmas.
- `4203c6a` **Buffer margin measured** (`tools/maxpseudo.{c,py}`): verified
  maximum `generate_pseudo` count over invariant-valid positions is **591**
  (`SHOGI_MAX_MOVES` = 600 leaves 9 slots); best game-reachable in play: 520.
- `c37d829` **`checkingPawnDrops_le_one` proved** (`OneCheckDrop.lean`): at
  most one pawn drop in `pseudoMoves` gives check. Via a named per-square
  `dropCell` (injective within a square), `dropMoves` is Nodup (distinct
  squares have disjoint move sets — a drop's destination is its square),
  board moves never survive the pawn-drop/check filter, and a Nodup list of
  equal elements has length ≤ 1. Registered in the axiom check
  (propext, Quot.sound). This is the bound M4's allocation accounting needs.

Remaining work, in dependency order:

1. **Discharge `RecSpec`** (M4) by strong induction on `q.pawnsInHands`
   (`legalFuel = pawnsInHands + 2`), using `generate_legal_main` for the inner
   call. Progress: `legal_loop` (`LegalLoop.lean`) and `generate_legal_main`
   (`LegalMain.lean`) now both export `Frame m s'.mem mb cb` (commits
   `1a371f9`, `cc8368a`), and `legal_loop` additionally exports
   `∃ f, Fresh s'.mem f ∧ f ≤ n + (d+1) * RB`. Still to do:
   - export the Fresh bound from `generate_legal_main` too (compose the
     prologue `n+2`, pseudo `n+40000`, count-init `+1`, safety `+2`, and the
     loop's `f`; the true per-call cost is ≈ `n + 40000 + 5 + (Ms.length+1)*RB`
     ≤ `n + 5*RB + 40010`, so `allocBound` can be a constant ≈ `5000000010`).
   - replace `recBudget` (`LegalProbe.lean:207`) and the fixed `k + recBudget`
     in `RecSpec` by `allocBound`; a single level's nested-call cost is one
     `allocBound`, but `iter_one`'s bound currently charges `+1000000030`
     regardless, so `allocBound` must exceed `1000000030` per level *and*
     recursively cover one nested level: use a per-level constant
     `Lvl := 5000000000` and set `allocBound pawns := (pawns + 2) * Lvl`
     (reachable `pawnsInHands ≤ 18` ⇒ ≈ 10¹¹ ≪ 2^64). Prove
     `k' ≤ k + allocBound (pawnsInHands q)` from the loop's `f` bound plus
     `checkingPawnDrops_le_one` (at most one nested level consumes `Lvl`).
   - play-preservation lemmas for a checking pawn drop: **done** (commit
     `e326838`) — `play_drop_kingsUnique` and `play_drop_hand_le` (hands < 256
     for both colours) in `OneCheckDrop.lean`; `play_shaped` already exists in
     `Shogi/Theorems.lean`. Then strong induction on `pawnsInHands`
     (`pawnsInHands_play_drop` decreases it; `legalAux_stable` supplies the
     fuel past `pawnsInHands+2`).
2. **600-move bound** (M5), informed by the measured 591: prove
   `pseudoMoves.length ≤ 600` for reachable positions (per-family mobility
   maxima + drop count, case analysis on onboard count), or prove a bound
   `B > 600` and bump `SHOGI_MAX_MOVES` (measure perft/NPS, regenerate
   `Gen.lean`), or keep it as one named hypothesis in the trust base. False
   for arbitrary positions.
4. **Public entry points** (M6): `shogi_generate_legal_mut` (already
   translated, `Gen.lean` fid 36) wrapper proof, then add
   `shogi_position_copy_active` + `shogi_generate_legal` to `c2lean.py` ROOTS,
   regenerate, and prove the copy-active bridge → final "C legal moves ~ spec
   `legalMoves`" for reachable positions.
5. **Full make/unmake with Zobrist hash and history, and repetition**
   (M7): `ZobristIn` κ-parametric abstraction, `position_hash_spec`,
   `shogi_make_move_internal_spec` (watch mutation-during-validation at
   `src/shogi.c:846`), full `shogi_unmake_move` round-trip, the fast-path
   variant parameterized over the `fast_check_bookkeeping` flag, and
   `shogi_repetition_result_spec` under `NoCollision`.
6. **Before any push** (M8): refresh `formal/PLAN.md` stale header and
   `formal/README.md` status/trust base; run the full check loop; AGENTS.md
   pre-push audit on `@{upstream}..HEAD` (secrets, personal paths, artifacts,
   gitleaks/trufflehog); fresh user authorization; update PR #2.

### Resuming prompt

```text
Continue the tinyshogi Lean formalization on branch `formal-plan` (HEAD
c37d829). Read plan.md's "Status and remaining items (session 2)" first.

Verification loop (run after every change):
  cd formal && lake build && ./tools/axiomcheck.sh && \
    python3 tools/c2lean.py --check && python3 tools/cdiff.py --n 500

Start with item 1 (M4, discharge RecSpec). Three changes, in order:
(a) add `Frame s.mem s'.mem mb cb` to `legal_loop`'s conclusion in
    formal/Shogi/C/Proofs/LegalLoop.lean (the per-iteration `Frame` from
    `iter_one` is already in scope — just thread it through the induction);
(b) export a memory frame from `generate_legal_main` (LegalMain.lean) by
    composing the prologue / pseudo / count-init / king-safety / loop frames;
(c) replace `recBudget` (LegalProbe.lean) with `allocBound pawns`, use the
    new `checkingPawnDrops_le_one` (OneCheckDrop.lean) to show a level has
    at most one nested call, then strong induction on `pawnsInHands` closes
    `RecSpec`. Add play-preservation lemmas for a checking pawn drop
    (`Shaped`, `KingsUnique`, hands < 256) if not already present.
Then items 2–6 (600 bound, entry points, make/unmake+repetition, docs/audit).

Policy: no `sorry`, no Mathlib, no `native_decide`; only propext,
Classical.choice, Quot.sound. Commit each milestone separately with the
Co-authored-by trailer. Do not push without fresh authorization.
```

