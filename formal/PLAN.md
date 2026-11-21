# tinyshogi `formal/` — plan for a Lean 4 formalization of the shogi rules

Status (2026-11-20): R0, R1 and the MiniC half of R2 are done.
`MiniC/Extend.lean` now proves the full mutual induction `ext_step` over
all MiniC constructors plus `ExS_ext`/`ExS_mem_ext`, all axiom-clean.
`encodeW` is defined in `Shogi/C/Model.lean`. The remaining R2 step is
migrating the position-block proofs from `encode p` to `encodeW p w` with
a block tail, then composing with the extension lemma to discharge
`CopyGenSpec`. R4a (spec Zobrist hash) is done. Note: making the 12 bytes an
implicit parameter of `encode` itself was tried and reverted — the proofs
use `simp [encode]` extensively, so the parametrisation must be threaded
through theorem statements instead (a wide refactor). The spec (T1–T4), the Lean → C tables (T6), the
attack/king layer (T7) and the whole legal-move generator (T8–T9: pseudo
moves, king safety, probe make/unmake, legality loop, uchifuzume recursion
via `RecSpec_discharge`, 7200-move bound) are proven against the MiniC model,
axiom-clean. `Shogi.C.Main.shogi_generate_legal_mut_correct` now states the
fid 36 result without `hrec`/`RecSpec`. **The main structural gap remains:
all position-block theorems still assume the 114-byte `encode p` block**
(finding F2), so they do not yet cover the 41088-byte `ShogiPosition` the
engine builds. Make/unmake, hashing, repetition, declaration and the game
result (old T9/T10, "M7") have spec-level scaffolding only. The remaining
work is R2–R9 below. The original design (§1–§8) is kept at the end for
reference; where it conflicts with the sections above it, the sections above
win.

---

## 0. Snapshot (2026-11-19)

Health check run during the review (working tree = detached `5750e18` plus
uncommitted work, see F1):

| Check | Result |
|---|---|
| `lake build` | green, 79 jobs (incremental) |
| `./tools/axiomcheck.sh` | `axiomcheck: ok` (three standard axioms) |
| `python3 tools/c2lean.py --check` | exit 0 (`Gen.lean` matches `src/shogi.c`) |
| `python3 tools/cdiff.py --n 200 --walks 5 --games 20 --mini 5` | 0 mismatches |
| `c2lean_report.py` | 60/72 functions translate; `FUNCTIONS` imports 52 (fid 0–51) |

Not re-measured: clean `lake build` wall time, `make test`, full-size cdiff.

### Proven C refinements, per translated function (fid in `Gen.lean`)

| fid | Function | State |
|---|---|---|
| 0–14 | piece/square helpers, `hand_index`, `piece_letter` | proven, every input |
| 15 | `step_piece_attacks` | translated; no theorem (only used by fid 18) |
| 16, 17, 19, 21 | `step_square_attacked`, `square_attacked`, `find_king`, `shogi_is_in_check` | proven, every position |
| 18 | `shogi_piece_attacks_square` | **tested only** |
| 20, 31 | `same_king_ray`, `king_safety_prepare` | proven |
| 22–28 | `add_*`, `generate_pseudo_for_color`, `generate_pseudo` | proven (permutation of `pseudoMoves`) |
| 29, 30 | `shogi_generate_pseudo{,_for_color}` (public) | **no theorem** |
| 32 | `same_move` | **no theorem** (used by `shogi_parse_and_make_move`) |
| 33, 34 | `make_legal_probe`, `unmake_legal_probe` | proven, round trip |
| 35 | `generate_legal_mut_internal` | proven (`generate_legal_refines`), **114-byte block only** (F2) |
| 36 | `shogi_generate_legal_mut` | proven **conditionally**: `hrec` hypothesis, 114-byte block, output pinned to block 2 (F2, F4, F6) |
| 37 | `shogi_position_copy_active` | proven, full 41088-byte blocks |
| 38 | `shogi_generate_legal` | proven **under `CopyGenSpec`** (F2, F3) |
| 39–47 | `position_hash`, `reset_history`, make/undo/unmake (+ `_fast`), `shogi_search_null_move` | **tested only** (four-way cdiff) |
| 48–51 | `validate_material`, `declaration_points`, `shogi_is_declaration_win`, `shogi_repetition_result` | **tested only** |
| — | `shogi_game_result{,_with_moves,_with_moves_mut}`, `square_from_text/_chars`, `shogi_parse_and_make_move` | translate, but **not in `FUNCTIONS`** |
| — | SFEN/USI parse/print, `shogi_init`, `splitmix64`, printing | rejected by c2lean (libc, atomics); spec + cdiff only |

Spec-level results: `legalMoves_iff`, `legalAux_stable`, `reachable_inv`,
`reachable_kings`, `reachable_material(Ok)`, `Sfen.parse_print(_reachable)`,
`Usi.parse_print`, `pseudoMoves_le_7200`, `unplay_pseudo` (spec make/unmake
round trip), `Game.init_wf`/`play_wf`/`occurrences_spec`/
`repetition_none_of_lt_four`, perft 1 in the kernel.

---

## 1. Review findings (2026-11-19)

**F1 — The current proofs are not committed.** HEAD is detached at
`5750e18`. 56 tracked files are modified (the `posBlock` generalisation, the
`rem` budget threading) and four theorem files are untracked:
`Shogi/C/Proofs/EntryPoints.lean`, `Shogi/C/Proofs/RecDischarge.lean`,
`Shogi/GameTheorems.lean`, `Shogi/PlayInverse.lean`. `formal-plan`
(`32fc17c`) has two commits on top of `5750e18` (`67b9294`, `32fc17c`). They
hold the abandoned "flat RB constant" scheme that the working tree replaced.
There are 10 stashes from those experiments. The untracked root `resume.md`
is out of date (it says `RecSpec` is open) and contains an absolute
home-machine path, so it must never be committed.

**F2 — Every position-block theorem assumes a 114-byte block whose
`move_number` and `hash` are zero.** `encode p` (`Shogi/C/Model.lean`) is the
114-byte `ShogiPosition` prefix, with zeros at offsets 100–111 (`move_number`
at 100, `hash` at 104). Every C-side theorem takes `m posBlock = some
(encode p)`. A real `ShogiPosition` has 41088 bytes and, in general, a
non-zero hash and move number. As a result, the fid 35/36 theorems **do not
yet apply to any position the engine builds**. `CopyGenSpec` (fid 38) is the
visible symptom of this gap, and the README's "verified end to end" claim
for fid 36 overstates the result. This gap is the main open item: R2.

**F3 — The `CopyGenSpec` budget is inconsistent with the generator's
contract.** It assumes `n + 10^9 < 2^64`, but `generate_legal_refines` needs
`n + 401·rem < 2^64` with `rem ≥ recDelta = 10^13`. The hypothesis has to be
restated when it is discharged, not just proved as written.

**F4 — No unconditional capstone theorem exists.** `RecSpec_discharge` is
proven but is not yet composed with `shogi_generate_legal_mut_spec`, so fid 36
still takes `hrec`. Results are stated for `legalAux (fuel+1) p`, not
`legalMoves p`. The side conditions (`Shaped`, `KingsUnique`,
`hand < 256`, `inCheck side.opp = false`, the budget) are not derived from
`Reachable p` anywhere. There is no lemma
`Reachable p → p.inCheck p.side.opp = false`.

**F5 — Frame conditions are dropped.** `generate_legal_main` exports "every
other pre-existing block is unchanged", but `generate_legal_refines` and fid 36
discard it (`_` in the `obtain`). Every caller (fid 38, the game result)
needs it.

**F6 — The fid 36 output buffer is pinned** to block `movesBlock = 2`,
offset 0, a harness constant. `generate_legal_refines` already allows any
`mb`/`mo`.

**F7 — The docs are out of date.** The README "Findings" section still says
`SHOGI_MAX_MOVES = 600` and that `h600` is open, and its T8 row says the 600-move cut "is not
yet shown never to trigger". Both are fixed by M5. The line numbers in Appendix A §1.1
refer to a 1539-line `shogi.c`; it now has 1480 lines.
`fast_check_bookkeeping` is now `_Thread_local`. The T3 row lists make/unmake
as "todo".

**F8 — M7 has no C-side foundation yet.** There is no Lean Zobrist
function, no abstraction for the history arrays, and no relation between a
full 41088-byte block and `Game`. `encodeFull`/`decodeFull` are test-harness
helpers only.

**F9 — `tools/AxiomCheck.lean` is a hand-maintained list.** A new theorem
that is left out of it is not checked, and the list already has duplicates.

**F10 — Clean-build cost is unmeasured.** `Geom.lean` alone takes about
5 minutes, and CI has a 60-minute budget. R2/R4/R5 add proofs over
41088-byte blocks, so those proofs must never evaluate a full block (see the
risks).

---

## 2. Remaining work (re-designed 2026-11-19)

Order and dependencies:

```
R0 ─► R1 ─► R2 ─┬─► R4 ─► R5 ─► R6 ─► R7
                └─► R3 (parallel with R4–R6)
R8: decided (tested only); R9: optional, independent
```

Estimates are focused engineer-days (d) or weeks (w), ±50 % for proofs.

### R0 — Commit the work in progress (0.5 d) — prerequisite

1. Create a branch from the current HEAD and commit the working tree in
   logical commits, each of which builds on its own:
   (a) `posBlock`/`rem` generalisation across `Shogi/C/Proofs`,
   (b) `RecDischarge.lean` (M4), (c) `EntryPoints.lean` (fid 36/37/38),
   (d) `PlayInverse.lean`, (e) `GameTheorems.lean`, (f) `AxiomCheck`, README
   and PLAN.
2. Tag `formal-plan`'s `67b9294`/`32fc17c` as `formal-plan-rb-attempt`,
   then point `formal-plan` at the new commits. Because they descend from
   `5750e18`, the branch stays a fast-forward of `origin/formal-plan`.
   Export the 10 stashes as patches to the ignored
   `formal/scratch/stashes/`.
3. Do not commit `resume.md`. Refresh it outside the tree or delete it.
4. Exit: `git status` is clean under `formal/`; the R7 verification baseline
   is green on the tip. Nothing is pushed without the `AGENTS.md` audit and
   fresh authorization.

### R1 — Unconditional legal-move theorem on the current model — DONE (2026-11-19)

`Shogi.C.Main` proves `shogi_generate_legal_mut_correct` with no `hrec` or
`RecSpec` hypothesis; all five new theorems are axiom-clean. R1 removed
`hrec` from the headline statement and fixed its shape before R2 changes the
block model. Implemented as follows.

* Spec: `reachable_opp_not_in_check : Reachable p → p.inCheck p.side.opp =
  false` (start position by `decide`, step by `legalMoves_safe`).
* Spec: bundle `RulesInv p := Shaped ∧ (∀ c, kingCount c ≤ 1) ∧ materialOk ∧
  inCheck side.opp = false`, with `reachable_rulesInv`
  (`reachable_inv`, `reachable_kings`, `reachable_materialOk`, the lemma
  above). `KingsUnique` is derived by `kingsUnique_of_count`, and
  `hand < 256` by `hand_lt_256_of_materialOk`. (Deviation from the original
  wording: the count bound is stored instead of `KingsUnique`, which is
  equivalent and avoids a second invariant proof.)
* Re-export the frame from `generate_legal_refines` (F5). Generalise fid 36
  to any output block/offset (F6).
* `shogi_generate_legal_mut_correct`: `RulesInv p`, the block hypotheses and
  a simple budget (`n < 2^63`) imply that the output is a permutation of
  `(legalMoves p).map (moveBytes p)`, the return value is its length, the
  position block is unchanged, every other block is framed, and the
  allocator stays bounded. Choose `fuel := p.pawnsInHands + 1` (so
  `legalAux (fuel+1) = legalMoves` by definition of `legalFuel`) and
  `rem := recBigEnough + pawnsInHands·recDelta` (≤ 1.36·10^15 ≤ 200·recDelta
  since the two hands hold at most 18 pawns each). Discharge `hrec` with `RecSpec_discharge` on
  `p.play mv` (`pawnsInHands_play_drop`, `play_materialOk`,
  `play_kingCount_le`).
* Optional (T2 promised it): `legalMoves_nodup`, so the permutation is also
  a set equality.
* Exit: the theorem has no `hrec`/`RecSpec`/`CopyGenSpec` hypothesis and is
  listed in the axiom check.

### R2 — Real `ShogiPosition` blocks (1–2 w) — the core of the remaining M6

**Progress (2026-11-20):** the MiniC half is complete. `MiniC/Extend.lean`
proves `MemExt`, all byte-level extension lemmas, the mutual fuel-induction
`ext_step` covering every MiniC constructor (including `alloc`, `memcpy`,
`memset`), and `ExS_ext`/`ExS_mem_ext` using fuel monotonicity. All are
axiom-clean and imported by `Shogi.lean`. `Shogi.C.encodeW p w` replaces the
12 implementation-only bytes with a symbolic word. **Remaining:** migrate
the position-block proofs from `encode p` to `encodeW p w` (and a block
tail), then lift each `ExS` proof with `ExS_mem_ext` and discharge
`CopyGenSpec`.

Goal: fid 35/36/38 theorems for any 41088-byte block whose live fields
encode `p`, with any `move_number`/`hash`/history bytes. `CopyGenSpec` is
deleted.

Design (two independent pieces):

1. **Block-extension simulation (MiniC, proved, not trusted).** Add
   `MiniC/Extend.lean`. Relation `MemExt m m' := ∀ x, (m x = none ∧ m' x =
   none) ∨ ∃ B T, m x = some B ∧ m' x = some (B ++ T)`. Theorem by fuel
   induction, following the pattern of `MiniC/Fuel.lean`: a successful
   `evalExpr`/`evalArgs`/`execStmt`/`callFunc` on `m` runs the same way on
   `m'` (same outcome and locals), and the resulting memories are again
   `MemExt`. Each primitive is monotone under extension: bounds checks in
   `readBytes`/`writeBytes`/`ptrAdd`/`ptrAddN`/`memcpy`/`memset`/`memcmpAt`
   only get easier; `strlenFrom` finds the same NUL; `alloc` reads the
   counter from the prefix of block 0 and creates identical fresh blocks. A
   success on the short block therefore lifts to the long block, and the
   tail `T` is never inspected. Corollary `ExS_ext`.
2. **The 12 bytes the generator ignores (`move_number`, `hash`).** These
   are inside the 114-byte prefix, so extension does not cover them.
   Decision: **parametrise the encoding** as `encodeW p w := (encode p).take
   100 ++ w ++ (encode p).drop 112` with `w.length = 12`, so `encode p =
   encodeW p zeros`. Only four proof files unfold `encode` directly
   (`AddSlide`, `AddStep`, `FindKing`, `PlaySpec`); the others use about 150
   `encode p` mentions through lemmas. Migration:
   (i) add accessor lemmas (`encodeW_board`, `_hand`, `_side`, `_king`,
   `_length`) and make the four files use only these;
   (ii) generalise statements bottom-up (Helpers → FindKing/StepAttack/
   SquareAttack/InCheck → Add*/Pseudo* → PlaySpec/Probe*/Unmake → KS* →
   Legal* → RecDischarge → EntryPoints) with `{w} (hw : w.length = 12)`;
   the probe results become `encodeW (p.play m) w` with the same `w`;
   (iii) restate `RecSpec` with `w`.
   Rejected alternatives: a simulation over arbitrary "don't-care" bytes
   (not provable without a separate non-access proof); putting
   `p.moveNumber` into `encode` (the probe does not bump the move number, so
   `encode (p.play m)` would be wrong).
3. **Predicate** `IsPos m b p := ∃ w T, w.length = 12 ∧ m b = some (encodeW p
   w ++ T)`. The restated fid 35/36 theorems take `IsPos` (with
   `(encodeW p w ++ T).length = 41088` where needed) and restore the block
   exactly.
4. **fid 38.** Drop the `100..111` conjuncts from `FieldsOK`, derive `IsPos
   work p` from `shogi_position_copy_active_spec`, apply R2.3 and the R1
   capstone, and restate the budget (F3). Result:
   `shogi_generate_legal_correct` (source block untouched, frame kept).
* Exit: R1's capstone restated on `IsPos` for fid 36 and fid 38;
  `CopyGenSpec` and the 114-byte-only statements are removed or demoted to
  internal lemmas; README no longer overclaims.

### R3 — Remaining small refinements (3–5 d, parallel after R2)

**Progress (2026-11-20):**
- fid 32 `same_move` is proven (`Shogi/C/Proofs/SameMove.lean`): the C copies
  both move blobs into fresh blocks and compares fields 0/1/3/4; the frame
  lemma shows unrelated blocks are unchanged.
- fid 29/30 (`shogi_generate_pseudo{,_for_color}`) are proven
  (`Shogi/C/Proofs/PseudoWrap.lean`): each allocates an 8-byte count, calls
  fid 28 / fid 27, and returns the number of pseudo moves written (capped at
  capacity). All axiom-clean.
- fid 48 (`validate_material`) is **complete**
  (`Shogi/C/Proofs/ValidateMaterial.lean`, `validate_material_spec`): the full
  C body is proved to allocate the maximum/total arrays, initialise the maximum
  to `handMax`, count each board family, add both hands, reject on overflow,
  and return `u8 1` for a shaped position with `materialOk = true`. The two
  loops (`loop0_runs`, `loop1_runs`) use `ExS.loop_next`/`ExS.loop_brk` and
  the structured `BodyResult`/`Loop1Inv` invariants. Axiom-clean.
- fid 15 (`step_piece_attacks`) is **complete** (`Shogi/C/Proofs/StepPieceAttacksSpec.lean`, `step_piece_attacks_spec`): the seven-step condition evaluation refines `stepOffsets` membership for |dr|,|dc| ≤ 8. Axiom-clean.
Remaining: fid 18 (geometric attacks).

Write these directly against `IsPos`.

* fid 29/30 `shogi_generate_pseudo{,_for_color}`: the output is a
  permutation of the spec pseudo moves for the requested colour (add a spec
  `pseudoMovesFor c` if needed). `pseudoMoves_le_7200` gives "no truncation"
  for `cap ≥ 7200`; otherwise the count is `min`.
* fid 15 + 18 `step_piece_attacks`, `shogi_piece_attacks_square`: equal to
  the spec's from-centred geometric attack.
* fid 32 `same_move`: byte equality of the 5 fields.
* fid 48 `validate_material`: equal to `materialOk` plus whatever else the C
  checks (pin down the exact C predicate first).

### R4 — Hash and full-state abstraction (M7a, 1 w)

**Progress (2026-11-20):** `Shogi/Zobrist.lean` defines `Keys`, `Position.zobrist`
and the `XorList` lemmas; all axiom-clean. **Remaining:** the incremental
hash lemma for a move (`zobrist (p.play m) = zobrist p ^^^ delta`), the
C-global bridge, and `FullRel`.

* `Shogi/Zobrist.lean` (spec): `Keys` (board 81×32, hand 2×7×19, side), and
  `zobrist K p` mirroring `position_hash` (hand count clamped at 18, side key
  only for white). Incremental lemma: for `m ∈ p.pseudoMoves` with
  `materialOk`, `zobrist K (p.play m) = zobrist K p ^^^ delta K p m`
  (the clamp never triggers, because hands are ≤ 18).
* `ZobristIn M K`: the after-init global blocks hold the bytes of `K`.
  The proofs are **parametric in `K`**; the key values are never proved.
* `FullRel M b K g`: block `b` is `IsPos` for `g.pos` with `w = le32
  moveNumber ++ le64 (zobrist K g.pos)`; `history_length =
  g.history.length ≤ 4096`; `history[i] = zobrist K eᵢ.key`; mover byte
  (`none` ↦ `HISTORY_MOVER_NONE`) and check byte per entry; king squares
  coherent. State it through `readBytes` facts at field offsets, never as a
  41088-element list.
* fid 39 `position_hash_refines`, fid 40 `reset_history_refines` (from a
  block with the live fields of `p`, the result satisfies `FullRel` for
  `Game.init p`).

### R5 — make / unmake (M7b, 2 w)

* fid 41 `shogi_make_move_internal`: for `m ∈ g.pos.legalMoves`, `FullRel g →
  FullRel g'` where `Game.play g m = some g'`, and the function returns
  true. Reuse the `PlaySpec` byte-edit lemmas, R4's incremental hash, and
  `shogi_is_in_check_refines` on the new block (needs R2). Also prove that
  the post-update `!shogi_can_promote` exit is unreachable. Optionally,
  characterise C acceptance for pseudo-legal moves (the C does not check
  king safety).
* fid 42 wrapper; fid 43/44 `make_move_undo{,_internal}` and fid 46
  `shogi_unmake_move`: the undo round trip restores the live state (the
  `activeState` relation cdiff already uses), linked to the spec `unplay`.
* fid 45 `_fast`, covered with the flag both on and off (decision): the
  thread-local flag is modelled as a read-only global. With the flag `true`,
  the result is the same `FullRel` as fid 41. With `false`, the check bytes
  are 0; this refines a spec variant `Game.playNoCheck` in which the
  perpetual-check rule collapses to a draw. That variant is documented as a
  throughput mode, not a rules claim. The game-level capstone in R6 is
  stated for both flag values.
* fid 47 `shogi_search_null_move`: side/hash/history effect.

### R6 — Repetition, declaration, game result (M7c, 1–1.5 w)

* `NoCollision K g := ∀ e ∈ g.history, zobrist K e.key = zobrist K
  g.pos.key → e.key = g.pos.key` (the other direction is automatic).
* fid 51 `shogi_repetition_result`: under `FullRel` and `NoCollision`,
  the return value and `*result` are exactly `Game.repetition g`.
* fid 49/50: `declaration_points`/`shogi_is_declaration_win` =
  `Declaration.declarationPoints`/`declarationWin`.
* Append `shogi_game_result_with_moves`, `_with_moves_mut` and
  `shogi_game_result` to the **end** of `c2lean.py` `FUNCTIONS` (existing fid
  numbers stay stable), regenerate, and `--check`.
* Game result = `Game.result g` (capacity ≥ 7200; `shogi_game_result` uses
  `SHOGI_MAX_MOVES` = 7200 through fid 38 from R2).
* Capstone: for any legal move sequence from `reset_history` on a position
  `p`, the C block after the `shogi_make_move` chain is `FullRel` of the spec
  game, and `shogi_game_result` = `Game.result`, under `NoCollision`. The
  same holds for the `_fast` chain (with the undo records discarded) with
  bookkeeping on; with bookkeeping off, it holds against
  `Game.playNoCheck`/`Game.result`.

### R7 — Statement audit, axiom check, docs (M8; 2 d at the end, plus per milestone)

* `Shogi/C/Main.lean`: the headline end-to-end theorems with minimal,
  readable hypotheses (`Reachable`/`RulesInv`, `IsPos`/`FullRel`, budget,
  `NoCollision`), imported last.
* Generate the axiom check instead of listing names: a meta script that
  walks every theorem in `Shogi.*`/`MiniC.*` and fails on any other axiom
  (F9). It is run by `lake env lean` and does not enter the trust base.
* README/PLAN: a per-fid status table (proven / conditional / tested only /
  excluded), fix the F7 items, trust-base notes (E5 never frees blocks; the
  `_Thread_local` flag is modelled as a read-only global; `NoCollision` and
  the key values are assumptions).
* Measure the clean `lake build` time and record it in the README (F10).
* Pre-push audit per `AGENTS.md` (credentials/personal paths, build
  artefacts, binaries, then explicit authorization).

### R8 — Text I/O: tested only (decided)

SFEN/USI C functions are rejected by c2lean (`__ctype_b_loc`, `strtok_r`,
`strcmp`, `snprintf`, pointer arithmetic). Decision: they stay covered by the
spec theorems (`Sfen.parse_print`, `Usi.parse_print`) and the cdiff SFEN/USI
runs only. They are listed as "tested only" in the trust base. Not pursued:
MiniC E9 (grows the trusted semantics) and a libc-free C rewrite.

### R9 — Infrastructure (optional)

MiniC memory as arrays (faster cdiff); T12 shared `minic` package with
tinygltf; CI cache keyed without `scratch/`; a toolchain bump together with
tinygltf; a scratch-cleanup policy (`formal/scratch/` has about 450 ignored
files).

---

## 3. Verification baseline

After every proof change, in `formal/`:

```sh
lake build
./tools/axiomcheck.sh
python3 tools/c2lean.py --check          # note: running c2lean.py without --check rewrites Gen.lean
lake exe gentables | diff -u ../src/shogi_tables.h -
python3 tools/cdiff.py --n 500
git diff --check
```

If `src/shogi.[ch]` or `src/shogi_tables.h` change, also run `make test`
and the `web/` checks (`npm test`, `npm run test:wasm`, `npm run build`),
because the web build compiles the same C. Before any push: the
`AGENTS.md` pre-push audit and fresh authorization.

---

## 4. Risks and open questions (updated)

1. **R2 churn.** About 25 proof files take `encode p`. Mitigation: switch to
   accessor lemmas first (no statement change), then generalise bottom-up;
   keep each step building.
2. **Proof-time blow-up on 41088-byte blocks.** Never `rfl`/`decide` on a
   full block. Keep tails symbolic (`B ++ T`), use `readBytes` facts at field
   offsets, and track per-file elaboration time against the 60-minute CI
   budget.
3. **Allocation budget.** The `rem`/`recDelta` scheme must be threaded
   through R5/R6 (`shogi_is_in_check` allocates). Fix a single budget
   convention in `Main.lean`.
4. **`NoCollision` cannot be discharged** for the dumped key values in
   general. It stays a hypothesis; optionally it can be checked for a
   concrete history window.
5. **fid stability.** Append new `FUNCTIONS` entries at the end only.
6. Open (from the original plan, still open): the exact reading of the
   perpetual-check cycle (Appendix A §7.2) and the declaration variant (Appendix A §7.7).

Decisions (user, 2026-11-19):
* R0: commit the work in progress on `formal-plan`, keep the two
  experimental commits under the tag `formal-plan-rb-attempt`, and export
  the stashes as patches to `formal/scratch/stashes/`. The stashes
  themselves are kept until the user asks to drop them.
* R2: the `encodeW` parametrisation is accepted.
* R8: text I/O stays spec + cdiff only (option a).
* R5: the game-level theorem also covers `_fast`, with check bookkeeping
  both on and off.

---

## 5. History of milestones M4–M6 (condensed)

* **M4 (done, 2026-11-19)** — `RecSpec_discharge` (`RecDischarge.lean`):
  strong induction on `pawnsInHands` with a decreasing allocation budget
  (`RecSpec fuel rem q`, recursive call at `rem - recDelta`, `recDelta =
  10^13`, ceiling `200·recDelta`, global bounds `401·rem`). The ceiling was
  raised from `100·recDelta` because `recBigEnough = 100·recDelta` had made
  the discharge vacuous for `pawnsInHands > 0`.
* **M5 (done)** — `SHOGI_MAX_MOVES = 7200`, `pseudoMoves_le_7200`; `h600`
  is gone.
* **M6 (partial)** — fid 37 proven; fid 36 conditional; fid 38 under
  `CopyGenSpec`. Completed by R1 + R2.

---

## Appendix A — original design (2026-11-15)

*Historical. Superseded by §0–§4 where they conflict. Known stale facts:
line numbers in §1.1 refer to a 1539-line `shogi.c` (now 1480);
`SHOGI_MAX_MOVES` is 7200, not 600; `fast_check_bookkeeping` is
`_Thread_local`; T8–T10 in §5 are re-planned as R1–R6.*

The goal is a Lean 4 project under `formal/` that

1. specifies standard 9x9 shogi as an executable, readable Lean reference (the *spec*),
2. proves properties of the spec (invariants, generator soundness and completeness),
3. **C → Lean**: imports the tinyshogi rules core into Lean and proves it refines the spec,
4. **Lean → C**: generates C for at least one rules component from Lean, with a
   machine-checked proof that the generated C refines its Lean source,
5. differentially tests compiled C, the MiniC model, the Lean spec and `python-shogi`.

The policy is the same as tinygltf `formal/`: `lake build` with no `sorry`, no Mathlib,
no `native_decide`, no `bv_decide`, and only the three standard axioms
(`propext`, `Classical.choice`, `Quot.sound`), checked by `#print axioms` in CI.

---

### 1. Phase 0 findings

Prior art: local tinygltf checkout, branch `release` @ `97789b3`, `formal/`
(Lean `v4.35.0`, MiniC `GlTF/C/Semantics.lean` 620 lines, `tools/c2lean.py` 737 lines).

#### 1.1 The rules core

All of it is in **`src/shogi.c` (1539 lines) + `src/shogi.h` (157 lines)**. Nothing
else is needed to define legality. `search.c`, `eval.c`, `nnue.c`, `simd.c`, the
`a64fx_*` files, `thread_posix.c`, GPU and web code only call into `shogi.h`.

**Representation.** The board is a **mailbox**, not a bitboard:
`uint8_t board[81]` with square `= row*9 + col` (row 0 = rank a, col 0 = file 9).
A piece byte is `type | color<<4` (`type` 1..14, see `ShogiPieceType`; `0` is empty).
Other fields: `hand[2][7]` (P L N S G B R counts), `side`, `move_number`, a Zobrist
`hash`, a cached `king_square[2]`, and repetition history `history[4096]`,
`history_mover[]`, `history_check[]`, `history_length`.
Because there are no bitboards, the expected 64/128-bit bitboard MiniC extensions
are **not needed**. The 64-bit work is limited to Zobrist hashing (`^`, `>>`, `*` on `u64`).

**Move encoding.** `ShogiMove {from, to, piece, promote, drop}` (5 × `uint8_t`).
`from == 255` (`SHOGI_SQ_NONE`) marks a drop with `drop = type`. Moves are passed **by value**.

**Global state.** `zobrist_board[81][32]`, `zobrist_hand[2][7][19]`, `zobrist_side`,
`step_attack_probes[2][81][10]` (struct `{u8 square; u16 piece_mask}`),
`step_attack_probe_count[2][81]`, `attack_rays[81][8][8]`, `attack_ray_length[81][8]`,
`attack_ray_masks[2][81][8]`. All are filled once by `shogi_init()`, which is guarded
by an `atomic_uint`. There is also one mutable flag, `fast_check_bookkeeping`
(`shogi_set_fast_check_bookkeeping`).

**Functions** (line ranges in `src/shogi.c`, approximate size):

| Area | Functions (line) | Notes |
|---|---|---|
| Tables / init | `step_piece_attacks` (30, 19), `init_attack_tables` (49, 55), `splitmix64` (105, 6), `shogi_init` (112, 29) | builds the target-centred attack tables; atomics |
| Piece helpers | `shogi_piece` 142, `shogi_piece_color`, `shogi_piece_type`, `shogi_is_promoted` 154, `shogi_unpromoted_type`, `shogi_can_promote` 170, `promoted_type` 175, `row_of`/`col_of`/`on_board`/`square_at` 187–201, `in_promotion_zone` 203, `forced_promotion` 207, `hand_index` 216 | small, pure |
| Hash / history | `position_hash` 229, `reset_history` 250 | Zobrist |
| SFEN | `shogi_position_start` 266, `parse_sfen_board` 311 (49), `parse_sfen_hands` 360 (35), `validate_material` 395, `shogi_position_from_sfen` 410 (41), `piece_letter` 451, `write_sfen` 465 (73), `shogi_position_to_sfen{,_full}` 538/542 | `strcmp`, `strtoul`-style parsing |
| Attacks (target-centred) | `step_square_attacked` 546, `square_attacked` 559, `shogi_piece_attacks_square` 578 (geometric, from-centred) | reads global tables |
| King safety | `find_king` 668, `same_king_ray` 618, `king_safety_prepare` 635 (31, returns `KingSafety` **by value**, `memset`), `shogi_is_in_check` 684 | pin detection: shortcut for non-probed moves |
| Pseudo moves | `add_move` 691, `add_normal_move` 706, `add_step` 724, `add_slide` 737, `add_pseudo_drops` 755 (34, `__builtin_ctz`, nifu + dead-drop masks), `generate_pseudo_for_color` 789 (91, `switch`), `generate_pseudo` 880 | `add_move` drops moves silently once `capacity` is reached |
| Make / unmake | `shogi_make_move_internal` 885 (73), `shogi_make_move_undo{,_internal}` 962/1002, `shogi_make_move_undo_fast` 1017 (109), `shogi_unmake_move` 1126 (37) | updates hash and history; the check flag is recorded for perpetual check |
| Legal moves (mutable path) | `same_move` 1163, `make_legal_probe` 1181, `unmake_legal_probe` 1218, `generate_legal_mut_internal` 1234 (39), `shogi_generate_legal{,_mut}` 1294/1301, `shogi_position_copy_active` 1273 | probe make/unmake updates only board, hand, king square and side. **Uchifuzume is checked by a recursive call** on the opponent's replies |
| Repetition | `shogi_repetition_result` 1323 (33) | four-fold repetition by **hash equality**; a side that gave check on every one of its moves in the cycle loses |
| Declaration | `declaration_points` 1357, `shogi_is_declaration_win` 1380 | 28 points for black / 27 for white, at least 10 pieces in camp, king in camp, not in check |
| Result | `shogi_game_result{,_with_moves,_with_moves_mut}` | order: repetition → declaration → no legal move |
| USI | `square_from_text` 1437, `square_from_chars` 1445, `shogi_parse_usi_move` 1451, `shogi_move_to_usi` 1483, `shogi_parse_and_make_move` 1509 | |
| Display | `display_piece`, `shogi_print_position` | out of scope (`printf`) |

Things in the C that the proofs must take into account (none of them is a known bug):

* `unmake_legal_probe` restores `board[from] = move.piece`. This is correct only
  because every pseudo move has `piece == board[from]`. It becomes a lemma of the
  pseudo-move generator.
* The `if (!shogi_can_promote(type)) return false;` after the board update in
  `shogi_make_move_internal` would leave a half-applied move, but an earlier check
  makes it unreachable. We will prove that it is unreachable.
* The uchifuzume recursion ends because each nested level needs the side to move to
  be in check after a pawn drop that gave check. The measure is the number of pawns
  in both hands, which drops by one per level. The same measure is used in the spec.
* `SHOGI_MAX_MOVES = 600`. The known maximum number of legal moves in a shogi
  position is 593. Pseudo moves are bounded by a lemma
  (`pseudo_count_le : (pseudo p).length ≤ 600`), so the C buffer never truncates.
* Repetition compares 64-bit Zobrist keys, not positions. The refinement theorem
  therefore carries a **no-collision hypothesis** over the history window (§3, T9).

#### 1.2 `c2lean.py` on unmodified `src/shogi.c`

`c2lean.py` hard-codes `tiny_gltf_v3.c` and stops at the first error. A throwaway
driver (not committed) pointed it at `shogi.c` and translated **each of the 67
function definitions separately**, catching every rejection.

**Translator crash before any function is reached.** `collect_enums` assumes that
every `EnumConstantDecl` has an initializer (`KeyError: 'inner'`). Enumerators with
implicit values, such as `ShogiResult` and the system headers, crash it. This is a
translator fix.

**Accepted unchanged (6/67):** `shogi_piece`, `row_of`, `col_of`, `square_at`,
`shogi_position_to_sfen`, `shogi_position_to_sfen_full`.

**Rejected (61/67).** Only the first rejection per function is shown. The causes,
grouped:

| # | Cause (c2lean message) | First hit in | Count | Fix |
|---|---|---|---|---|
| G1 | `pointer comparison` (`p == NULL`) | all public API entry points, `parse_*`, make/unmake | 22 | MiniC: `ptr`/`null` equality (defined C11 semantics; ordered comparison stays rejected) |
| G2 | `unsupported cast IntegralToBoolean` (`return x == y` into `bool`, `if (int)`) | `step_piece_attacks`, `on_board`, `in_promotion_zone`, `same_move`, … | 13 | translator: emit `x != 0` cast to `u8` (the `_Bool` conversion) |
| G3 | `unsupported integer type 'ShogiColor'/'ShogiPieceType'/'ShogiMove'` | `shogi_piece_color`, `find_king`, `add_step`, `shogi_make_move` | 10 | enums: map to `u32` (clang's underlying type, which the probe checks). `ShogiMove` is G9 |
| G4 | `reference to unknown local` (declaration in a `for` initializer or a nested block) | `add_slide`, `generate_pseudo_for_color`, `position_hash`, `declaration_points` | 8 | translator: scope handling for `for (int r = …, c = …)` and block-local declarations |
| G5 | `cannot evaluate case label` (enumerator `case SHOGI_PAWN:`) | `promoted_type`, `hand_index`, `piece_letter`, `shogi_unpromoted_type` | 4 | translator: resolve `DeclRefExpr` to an `EnumConstantDecl` through the enum table |
| G6 | `static local` (`static const int ray_row[8]`, material limits) | `init_attack_tables`, `validate_material` | 2 | lift to file-scope `static const` (G10) |
| G7 | `decay of non-memory array` (local `ShogiMove pseudo[600]`, `replies[600]`, `moves[600]`) | `generate_legal_mut_internal`, `shogi_game_result` | 2 | MiniC: address-taken locals get their own memory block (`alloca`-style, freed on return) |
| G8 | calls to `memset`, `strcmp`, `toupper` | `king_safety_prepare`, `parse_sfen_hands`, `display_piece` | 3 | `memset`/`memcpy` as `Stmt` builtins. `strcmp` → rewrite on top of the existing `memcmp`/`strlen`, or add it as a builtin. `toupper` is display-only (excluded) |
| G9 | struct by value: `ShogiMove` parameters, compound literals `(ShogiMove){…}`, `return safety;` | `add_normal_move`, `make_legal_probe`, `king_safety_prepare` | (hidden behind G2/G3) | see §1.3, R1 |
| G10 | file-scope globals (10 arrays/scalars above) | every attack/hash function | (hidden) | MiniC: a global block table (read-only for `const`) |
| G11 | `CompoundAssignOperator` in an expression (`*state += k`), `++` inside an expression (`moves[(*count)++]`, `probe_count++`) | `splitmix64`, `add_move` | 2 | translator: split into a statement and a read. Pure syntax; it must preserve C11 sequencing, so reject when the same lvalue appears twice |
| G12 | `AtomicExpr` | `shogi_init` | 1 | **exclusion boundary**: `shogi_init` is not translated (§1.3, R2) |
| G13 | `__builtin_ctz` | `add_pseudo_drops` | (hidden) | `Expr.ctz`/`Expr.popcount`; `ctz 0` is `ub` |

The hidden rows were found by reading the code; they will surface once G1–G5 are fixed.
The rejection list is regenerated as part of T5 (`c2lean.py --report`).

#### 1.3 What MiniC cannot model, and what to do about it

| Construct | Where | Decision |
|---|---|---|
| `atomic_uint`, `atomic_*` | `shogi_init` | **Exclude.** Verified functions take tables as already initialized: the global blocks hold `Tables.init` (§T6). `shogi_init` correctness = "after it returns, the globals equal `Tables.init`". We test this in `cdiff` and do not prove it (concurrency is not modelled) |
| Global mutable tables | attacks, hash | **R2 (refactor, recommended):** move the generated tables to a `static const` header `src/shogi_tables.h`. It is produced by the Lean → C pipeline (§4), so the tables become the first Lean → C target. `init_attack_tables` disappears from the runtime, and `shogi_init` keeps only the Zobrist fill. Startup gets slightly faster and the hot path is unchanged (same arrays, now `const`) |
| Zobrist keys (`splitmix64` at init) | hash, repetition | Keep them as runtime globals. Make/unmake is proven **parametrically** in the key arrays: `hash' = hash ^ keys…`, with the keys as an opaque read-only block. Repetition is proven under a no-collision hypothesis |
| `fast_check_bookkeeping` (mutable global flag) | `shogi_make_move_undo_fast` | Model it as a read-only global. Prove both values; `true` is the spec-conforming one |
| Struct by value (`ShogiMove`, `KingSafety`, compound literals) | everywhere | **R1 (MiniC extension, recommended over a C refactor):** in MiniC, by-value structs are a byte-blob `Val.agg (bytes : List UInt8)` with the size taken from the probe. Copy and field access are byte splices (reuses `Splice.lean`). Refactoring `ShogiMove` to `uint32_t` would touch search and every caller and costs NPS; we do not do it |
| Recursion (uchifuzume) | `generate_legal_mut_internal` | Already representable: MiniC `call` is fuel-bounded. The termination proof uses the pawn measure |
| `printf`, `toupper`, `shogi_print_position` | display | excluded |
| Unions, function pointers, `volatile`, SIMD | — | **none in `shogi.c`** |

#### 1.4 Existing fixtures to reuse

* `tests/test_rules.c` (324 lines): perft 30 / 900 / 25470 from the start position.
  Per-rule SFENs for SFEN round-trip with `1R1r` hand normalisation, promotion,
  drop, nifu (`4k4/9/9/9/4P4/9/9/9/4K4 b P 1`), dead knight drop, material limits
  (`3RRR3/…` rejected, `1+R2+R4/…` accepted, too many rooks in hand), dead gold
  `+G` rejected, pin (`4r3k/…/4R4/4K4 b`), discovered-check pin, **uchifuzume**
  (`4k4/9/2NG1GN2/9/9/9/9/9/4K4 b P 1`), repetition and perpetual check
  (`4R3k/…/K8 w`), declaration gate.
* `fuzz/corpus/*.sfen` (7 files) and `fuzz/shogi_fuzz.c`: SFEN parser fuzz seeds.
* `scripts/verify_rules.py`: talks to the built engine over USI `status` and compares
  legal-move sets and SFEN against **python-shogi 1.1.1 (pinned)**, on random 20-ply
  walks from `runs/strength/openings/development.sfens`.

All of these become Lean fixtures in `Shogi/Tests.lean` (kernel-checked where cheap)
and `cdiff` corpora.

---

### 2. Vendor, share, or fork the tinygltf pipeline?

**Decision: vendor a fork into `formal/MiniC/` and `formal/tools/`, with attribution,
and plan to extract a shared package later.**

* MIT → Apache-2.0 is compatible. Each vendored file keeps its MIT header plus a
  `Vendored from syoyo/tinygltf formal/ @ 97789b3, modified` line, and the MIT text is
  stored in `formal/MiniC/LICENSE-MIT`.
* The extensions in §1.2 are large: aggregates, globals, address-taken locals,
  pointer equality, ctz. Developing them against two consumers at once would block
  both projects. With a fork, tinyshogi can move fast while tinygltf's proofs are not
  touched.
* The namespace changes from `GlTF.C` to `MiniC`, and the translator becomes
  configuration-driven (`c2lean.toml`: source, function list, output) instead of
  hard-coded.
* **Exit path (T12):** once both projects use the same MiniC, it is extracted into a
  `minic` Lake package that both projects `require` at a pinned commit. tinygltf's
  `Gen.lean` must still match. Any change to an extension that is generic (G1, G2,
  G4, G5, G11, the enum crash) is upstreamed to tinygltf as a separate PR.

#### MiniC extensions and how each is validated

Each extension gets (a) **negative controls** in `Tests.lean`: kernel-checked
`decide` examples showing that the UB cases evaluate to `.ub`, following tinygltf's
OOB controls; (b) **`cdiff` coverage**: compiled C under ASan/UBSan, the MiniC
interpreter and the spec must agree on random inputs that exercise it; and
(c) a **semantic lemma** used by the proofs.

| Ext | Semantics | Validation, in addition to (a) and (b) |
|---|---|---|
| E1 enum types | `u32`; the probe asserts `sizeof(enum)==4` and signedness | probe check in `c2lean --check` |
| E2 `_Bool` conversion | `x ≠ 0 → 1 : u8` | lemma `toBool_cast` |
| E3 pointer `==`/`!=` incl. `NULL` | equal iff same `(block, offset)`. Comparing pointers into different live blocks is defined (unequal). Ordered comparison is still rejected | control: `p == NULL` for a live `p` is `0` |
| E4 file-scope globals | a fixed global block per variable, initialised from the C initializer (for `static const`) or by an explicit `Init` state. Stores to a `const` block are `ub` | c2lean emits the initializer bytes; `--check` compares them with the probe's `memcmp` of the real arrays |
| E5 address-taken local arrays and structs | fresh block per activation, uninitialised bytes are poison (reading them is `ub`), freed on return. A dangling use is `ub` | control: returning `&local` then loading it is `ub` |
| E6 aggregates by value | `Val.agg bytes`. Struct assignment copies bytes; field reads/writes are splices; compound literals zero the gaps | probe-measured offsets; lemma `agg_field_splice` |
| E7 `memset`/`memcpy` | stmt builtins; `memcpy` overlap is `ub`; bounds as `load`/`store` | controls for overlap and OOB |
| E8 `ctz`/`popcount` builtins | `ctz 0` is `ub` (GCC/Clang doc), otherwise the index of the lowest set bit | exhaustive check for `u32` values `< 2^9` by `decide` (all hand masks) plus random `cdiff` |
| E9 `strcmp` | C-standard, via `unsigned char`, UB without a NUL | as `memcmp` today |
| E10 sequenced `++`/compound assignment | translator lowering only; rejected if the lvalue is aliased in the same full expression | `c2lean` unit tests in `tools/test_c2lean.py` |

`Semantics.lean` is expected to grow from about 620 to about 900 lines. All of it
stays in the trusted base (§6).

---

### 3. Directory layout, build, and CI

```
formal/
  PLAN.md                     this file
  README.md                   status table, trust base, spec↔C map (tinygltf style)
  lakefile.lean, lean-toolchain (leanprover/lean4:v4.35.0, same as tinygltf), lake-manifest.json
  Shogi.lean                  root import
  Shogi/
    Basic.lean                Color, PieceType, Piece, Square (Fin 81), Hand, Move
    Position.lean             Position, start, abstraction of the piece byte
    Sfen.lean                 parse / print, round-trip
    Usi.lean                  move text parse / print, round-trip
    Attacks.lean              geometric attacks, `attacked`, `inCheck`
    Pseudo.lean               pseudo-legal moves for every piece, drops, promotion
    Legal.lean                declarative `IsLegal`, executable `legalMoves`, uchifuzume
    Make.lean                 `apply`, `undo`
    Invariants.lean           Reachable, conservation, at most one king per side, no dead pieces
    Game.lean                 history, sennichite, perpetual check, result
    Declaration.lean          optional: entering-king 27/28 points
    Perft.lean                perft, depth-1/2 kernel checks
    Tables.lean               Lean source of the attack tables (Lean → C target)
    Tests.lean                fixtures from tests/test_rules.c, MiniC negative controls
  MiniC/                      vendored and extended from tinygltf (MIT)
    Semantics.lean, Logic.lean, Hoare.lean, Lemmas.lean, Splice.lean, LICENSE-MIT
  Shogi/C/
    Gen.lean                  GENERATED from src/shogi.c — do not edit
    GenTables.lean            GENERATED from src/shogi_tables.h (re-import of Lean → C output)
    Abs.lean                  abstraction: C memory ↦ Shogi.Position
    Proofs/*.lean             per-layer refinement proofs (T6–T10)
  CDiff.lean                  Lean side of the differential tests (exe)
  tools/
    c2lean.py, c2lean.toml    translator (forked) and config
    lean2c.py                 untrusted emitter (§4)
    cdiff.py, cdiff_c.c       four-way differential driver
    test_c2lean.py            translator unit tests
```

Commands (also listed in `formal/README.md`):

```sh
cd formal
lake build                                # spec, MiniC, all proofs
python3 tools/c2lean.py --check           # Gen.lean / GenTables.lean match the C
python3 tools/lean2c.py --check           # src/shogi_tables.h matches Shogi/Tables.lean
python3 tools/cdiff.py --n 2000           # C(ASan/UBSan) == MiniC == spec (== python-shogi with --oracle)
lake env lean --run tools/AxiomCheck.lean # every theorem uses only the three standard axioms
```

**GitHub Actions**: new job `formal` in `.github/workflows/formal.yml`, triggered on
changes to `formal/**`, `src/shogi.[ch]` or `src/shogi_tables.h`:

```yaml
jobs:
  formal:
    runs-on: ubuntu-24.04
    timeout-minutes: 60
    steps:
      - uses: actions/checkout@v4
      - uses: leanprover/lean-action@v1          # installs elan from formal/lean-toolchain
        with: { lake-package-directory: formal, build: false }
      - run: sudo apt-get install -y clang
      - run: cd formal && lake build
      - run: cd formal && python3 tools/c2lean.py --check && python3 tools/lean2c.py --check
      - run: cd formal && lake env lean --run tools/AxiomCheck.lean
      - run: grep -rn --include=*.lean -E '\bsorry\b|native_decide|bv_decide' formal/ && exit 1 || true
      - run: pip install python-shogi==1.1.1 && cd formal && python3 tools/cdiff.py --n 500 --oracle
```

The `.lake` cache is keyed on `lake-manifest.json` plus the toolchain.
`make test` keeps working without Lean.

---

### 4. Lean → C: design and first target

#### Design (translation validation)

1. **Source.** `Shogi/Tables.lean` defines the component in a **first-order Lean
   subset**: `Nat`/`UIntN` arithmetic, `if`, bounded `for` written as structural
   recursion on `Fin n`, and fixed-size arrays. It is also given as a deep-embedded
   `MiniC.Prog` built by a small Lean DSL (`LeanC`). Each `LeanC` construct maps
   one-to-one to a MiniC `Stmt`/`Expr`.
2. **Emit.** The **untrusted** `tools/lean2c.py` (or `lake exe lean2c`) prints C
   from the `LeanC` AST. For tables it emits the evaluated `static const` initializers
   plus, optionally, the generator function.
3. **Re-import.** The emitted `src/shogi_tables.h` goes through `c2lean.py`, which
   writes `GenTables.lean`. We then prove, in the kernel,
   `theorem tables_refine : MiniC.globalsOf GenTables.prog = Tables.encode Tables.init`.
   For the function form, the statement is "the generator returns, without UB, and
   writes exactly `Tables.encode Tables.init`".
   Because the emitted text is checked after it is produced, `lean2c.py` is **outside
   the trust base**. The trust base is the same as for the C → Lean direction:
   c2lean, clang and MiniC.
4. **Link to the spec.** `Tables.init` is proven to agree with the geometric spec.
   For example: `probe_sound_complete : (t ∈ probes c sq ↔ ∃ ty, stepAttacks c ty sq t)`
   and `ray_correct : rays sq d = the squares reached by stepping d until the edge`.
   With these, the C attack functions in T7 only need table lookups.

#### First target: attack tables (`step_attack_probes`, `attack_rays`, `attack_ray_length`, `attack_ray_masks`)

Why tables first:

* **Smallest semantic gap.** They are pure data (≈ 81·8·8 + 2·81·10·3 bytes), have
  no pointers or loops at runtime, and need only extensions E1 and E4.
* **Removes a blocker.** The tables go from mutable globals filled under an atomic
  guard (G12) to `static const` data. That is the refactor R2 needs anyway, so
  Lean → C pays for itself.
* **Cheap to check.** Equality of two concrete byte lists is `decide`-checkable in
  the kernel (≈ 15 KB; measured in T4 — fallback: split per square, 81 lemmas).
* **Hot path unchanged.** `square_attacked` and `king_safety_prepare` read the same
  arrays, now `const`. The perft and NPS gate in T5 confirms this.

The second target, after T11, is `add_pseudo_drops` (nifu and dead-drop masks plus
`ctz`). It is a real function with loops, so it exercises the function-form path.

#### Comparison

| Option | Verified? | Adds to the trust base |
|---|---|---|
| Translation validation (this plan) | yes, per output | nothing beyond MiniC, c2lean and clang, which are already trusted |
| Lean's own compiler (`lean --c`, IR → C) | no | the whole Lean compiler, its runtime (`lean.h`, RC/boxing, GMP) and the IR passes. The output is not idiomatic C and cannot replace `shogi.c` |
| Verified compilers from a Lean-embedded IR (e.g. CompCert-style Clight back ends, CertiCoq for Coq, CakeML for HOL4) | yes, but none target Lean 4 C emission today | a second semantics (Clight) and a link from it to MiniC. Too large for this project |
| Aeneas / Charon (Rust → Lean) | n/a (opposite direction, Rust) | — (mentioned only to show this is not covered elsewhere) |

---

### 5. Milestones

The effort is in focused engineer-weeks (w), assuming someone who knows Lean;
proof-heavy work has ±50 %. Each milestone ends with `lake build` green, no `sorry`,
and a `README.md` status row.

#### T0 — scaffold (0.5 w)
Scope: `formal/` Lake project, vendored MiniC unchanged (renamed namespace), c2lean
config with the 6 functions that already pass, CI job, `AxiomCheck`.
Exit: CI green, and `Gen.lean` contains `shogi_piece`, `row_of`, `col_of`, `square_at`.

#### T1 — spec core and SFEN/USI (2 w)
```lean
inductive Color | black | white
inductive PieceType | pawn | lance | knight | silver | gold | bishop | rook | king
                    | proPawn | proLance | proKnight | proSilver | horse | dragon
structure Piece where color : Color; type : PieceType
abbrev Square := Fin 81
structure Hand where counts : Fin 7 → Nat          -- P L N S G B R
structure Position where board : Square → Option Piece; hands : Color → Hand; side : Color; ply : Nat
inductive Move | normal (from to : Square) (promote : Bool) | drop (type : PieceType) (to : Square)

def Sfen.parse : String → Option Position
def Sfen.print : Position → String
def Sfen.Canonical : Position → Prop          -- valid material, hand order, no dead pieces
theorem sfen_roundtrip : Sfen.Canonical p → Sfen.parse (Sfen.print p) = some p
theorem sfen_print_parse : Sfen.parse s = some p → Sfen.print p = normalize s   -- e.g. "1R1r" ↦ "Rr"
theorem usi_roundtrip : Usi.parse (Usi.print m) = some m
```
Exit: every SFEN in `tests/test_rules.c` and in `fuzz/corpus` parses (or is rejected)
exactly as the C does, checked by `decide` in `Tests.lean`.

#### T2 — pseudo moves, attacks, legality (3 w)
```lean
def attacks (p : Position) (from to : Square) : Bool     -- geometric, needs empty path for sliders
def attacked (p : Position) (sq : Square) (by : Color) : Bool
def inCheck (p : Position) (c : Color) : Bool
def pseudoMoves (p : Position) : List Move
def apply (p : Position) (m : Move) : Position
def deadSquare (c : Color) (t : PieceType) (row : Fin 9) : Bool   -- pawn/lance last rank; knight last two ranks
def nifu (p : Position) (c : Color) (file : Fin 9) : Bool

/-- Declarative legality (independent of generation). -/
inductive IsLegal : Position → Move → Prop   -- piece moves geometrically, promotion zone (optional/forced),
                                              -- no dead piece, no nifu, own king not attacked after, ¬ uchifuzume
def uchifuzume (p : Position) (m : Move) : Bool  -- pawn drop gives mate: ∀ replies, ¬ legal
def legalMoves (p : Position) : List Move     -- termination_by pawnsInHands p
theorem legalMoves_sound    : m ∈ legalMoves p → IsLegal p m
theorem legalMoves_complete : IsLegal p m → WF p → m ∈ legalMoves p
theorem legalMoves_nodup    : (legalMoves p).Nodup
```
`IsLegal` and `uchifuzume` depend on each other through "opponent has no legal reply".
They are defined by well-founded recursion on `pawnsInHands`, which decreases by one
per drop of a checking pawn. This is the main design risk (§7).
Exit: soundness and completeness proven. Fixtures for pin, discovered check, nifu,
dead drop, forced promotion and uchifuzume are checked by `decide`.

#### T3 — invariants and make/unmake (2 w)
```lean
inductive Reachable : Position → Prop | start : Reachable start | step : Reachable p → m ∈ legalMoves p → Reachable (apply p m)
def WF (p : Position) : Prop   -- 40 pieces (board + hands, unpromoted counts 18/4/4/4/4/2/2/2), ≤ 1 king per side, no dead pieces, ≤ 1 unpromoted pawn per file per side
theorem reachable_wf : Reachable p → WF p
theorem apply_undo : IsLegal p m → undo (apply p m) (undoInfo p m) = p
theorem kings_exact : Reachable p → ∀ c, kingCount p c = 1
```
Exit: proven. `WF` also matches the C function `validate_material`
(`theorem validate_material_iff` at the spec level).

#### T4 — perft and kernel-speed measurement (1 w)
```lean
theorem perft1 : perft start 1 = 30  := by decide
theorem perft2 : perft start 2 = 900 := by decide
-- perft3 = 25470: attempted with `decide` + `Nat.decEq` by reflection; kept only if under the CI budget
```
Exit: measured kernel time per depth is recorded in the README. If depth 3 exceeds
about 10 minutes, it moves to `cdiff` (Lean compiled `#eval`, which is allowed
because it is a test and not a proof), together with depth 4 = 719731. Also
measures `decide` on the table equality from §4 (≈ 15 KB).

#### T5 — MiniC extensions and translator (3 w)
Scope: E1–E10, the `collect_enums` crash fix, a config-driven `c2lean.py` with
`--report` (the rejection list in §1.2), and translator unit tests.
Negative controls go into `Tests.lean`.
Exit: all **verified-core** functions translate (list below). `--check` is enforced
in CI. Every extension has controls plus `cdiff` coverage.
Verified core (≈ 40 functions): the piece and square helpers, `hand_index`,
`promoted_type`, `forced_promotion`, attacks, `find_king`, `same_king_ray`,
`king_safety_prepare`, `shogi_is_in_check`, `add_*`, `generate_pseudo*`,
`make/unmake_legal_probe`, `generate_legal_mut_internal`, `shogi_generate_legal{,_mut}`,
`shogi_position_copy_active`, `shogi_make_move{_internal,_undo,_undo_internal}`,
`shogi_unmake_move`, `shogi_repetition_result`, SFEN parse/write, `validate_material`,
USI parse/print. Excluded: `shogi_init` (atomics), `shogi_print_position`,
`display_piece`. `_fast` make/unmake is deferred to T10.
**C refactor gate:** R2 lands here (Lean-generated `shogi_tables.h`). Before and
after: `tests/test_rules` perft 1–4 is unchanged, `bench/` NPS changes by at most 1 %
(median of 5 runs), and `make test` passes. The numbers go in the PR.

#### T6 — abstraction function and table refinement (1.5 w)
```lean
def Abs.position (m : MiniC.Mem) (ptr : MiniC.Ptr) : Option Shogi.Position   -- decode board/hand/side bytes
def Abs.Inv (m : MiniC.Mem) (ptr : MiniC.Ptr) : Prop   -- WF + king_square cache coherent + history_length ≤ 4096
theorem tables_refine : MiniC.globalsOf GenTables.prog = Tables.encode Tables.init      -- Lean → C, §4
theorem probe_sound_complete, ray_correct                                                -- tables ↔ spec
```

#### T7 — bit helpers and attacks (2 w)
```lean
theorem piece_type_correct  : ∀ b, runs Gen.shogi_piece_type [b] = .ok (decodeType b)
theorem step_square_attacked_refines :
  Abs.Inv m p → Exec Gen.step_square_attacked [p, sq, c] m (.ret (boolOf (stepAttacked (abs m p) sq c))) m
theorem square_attacked_refines   : … = attacked (abs m p) sq c
theorem is_in_check_refines        : … = inCheck (abs m p) c
theorem king_safety_prepare_refines : … pinned[s] = true ↔ Pinned (abs m p) mover s     -- used as shortcut-soundness
```
All theorems have the tinygltf shape: no UB, terminates, the result equals the spec,
and the frame is "writes nothing" (or only the out-parameter).

#### T8 — per-piece generators and pseudo generation (3 w)
```lean
theorem add_step_refines / add_slide_refines / add_pseudo_drops_refines :
  writes exactly `encodeMoves (spec list)` at moves[count..], count' = count + len, nothing else
theorem generate_pseudo_refines : … moves[0..n) = encodeMoves (pseudoMoves (abs m p)) ∧ n ≤ 600
theorem pseudo_piece_field : m ∈ pseudo → m.piece = board[m.from]        -- makes unmake_legal_probe correct
```

#### T9 — make/unmake, legality filter, repetition (4 w)
```lean
theorem make_legal_probe_refines   : Abs (probe-state) = apply (abs m p) mv   (board/hand/side/king only)
theorem unmake_legal_probe_restores : unmake ∘ make = id on the bytes it touched
theorem shortcut_sound : ¬ needsProbe safety mv → (IsLegal p mv ↔ mv ∈ pseudo p)      -- the pin shortcut
theorem generate_legal_refines :
  Abs.Inv m p → Exec Gen.shogi_generate_legal [p, out, cap] m (.ret n) m' ∧ cap ≥ 600 →
  decode m' out n = legalMoves (abs m p) ∧ frame m m' [out, out+5n)
theorem make_move_refines : abs(after) = apply (abs m p) mv ∧ hash' = zobristOf keys (abs …) ∧ history appended
theorem repetition_refines :
  NoCollision keys window → result = Shogi.Game.sennichite (abs history)
```
The recursive uchifuzume call is proven by strong induction on `pawnsInHands`,
reusing the T2 measure. The fuel bound is derived from it.

#### T10 — `_fast` make/unmake and game result (1.5 w)
`shogi_make_move_undo_fast` and `shogi_unmake_move` round-trip;
`shogi_game_result_with_moves{,_mut}` = `Game.result` (repetition → declaration → mate).
Declaration is proven against `Shogi/Declaration.lean`, which is an optional module.

#### T11 — differential testing at full scale (1.5 w; starts in T5 and grows)
`tools/cdiff.py` runs four ways:

1. compiled `src/shogi.c` + `cdiff_c.c` under `-fsanitize=address,undefined`;
2. the MiniC interpreter on `Gen.lean` (`lake exe cdiff`, bounded fuel);
3. the Lean spec (`legalMoves`, `Sfen`, `Game.result`);
4. `python-shogi 1.1.1` (opt-in `--oracle`; reuse the move-set and SFEN comparison
   in `scripts/verify_rules.py`).

Inputs: random legal walks (seeded), positions from
`runs/strength/openings/development.sfens`, SFEN mutations of `fuzz/corpus`, and
hand-made edge cases (uchifuzume and near-uchifuzume where the drop is *not* mate,
nifu across promoted pawns, forced versus optional promotion on ranks 1–3, dead
lance and knight drops, perpetual-check loss for either side, four-fold repetition
with no checks, declaration 27 versus 28). Perft depth 4 = 719731 for C and the
compiled spec. Known oracle differences, if any (for example how python-shogi
treats sennichite and declaration), are listed and excluded explicitly rather than
silenced.

#### T12 — shared MiniC package (1 w, optional)
Extract `minic` as its own package, switch both tinyshogi and tinygltf to it, and
check that tinygltf's `Gen.lean` is byte-identical.

**Total ≈ 26 engineer-weeks** (T0–T11). T1–T4 (the spec) are useful on their own,
and T5 + T6 deliver the first Lean → C artifact.

---

### 6. Trust base

* **The Lean 4 kernel** (`v4.35.0`) and the three standard axioms.
* **The MiniC semantics** (`formal/MiniC/Semantics.lean`, vendored from tinygltf
  plus E1–E10). Every C11 UB that can occur in the subset is `ub`: signed overflow,
  oversized shifts, `ctz 0`, OOB, uninitialised reads, dangling locals, `memcpy`
  overlap, stores to `const`. Not modelled: strict aliasing, alignment, `volatile`,
  concurrency/atomics, the floating-point environment.
* **`c2lean.py` and clang's front end.** clang supplies types, implicit conversions
  and enum values; record layouts come from a probe built by the same clang.
  `lean2c.py` is **not** trusted (its output is re-imported).
* **The target ABI**: LP64, little-endian (x86-64, AArch64, RISC-V 64). Proofs do
  not cover the 32-bit WASM build. The `web/` build uses the same C but a different
  `size_t`; this is noted and covered by `cdiff` only if a WASM runner is added.
* **The C compiler**: nothing links the proofs to machine code. The
  ASan/UBSan `cdiff` runs are the evidence there.
* **Not modelled or not proven**: `shogi_init` (atomics; tested only), the Zobrist
  key values (proofs are parametric in them), hash collisions (repetition holds under
  `NoCollision`), search, eval, NNUE, SIMD, A64FX assembly, threads, GPU, WASM glue,
  the USI protocol loop in `main.c`, and time controls.

---

### 7. Risks and open questions

1. **Uchifuzume proof cost.** `IsLegal` needs "the opponent has no legal reply",
   which recurses into legality. The measure `pawnsInHands` is sound because a
   nested uchifuzume check happens only after a pawn drop. Proving the
   well-foundedness lemma inside the C refinement (fuel) may be the single most
   expensive step. *Mitigation:* state the spec as `uchifuzume p m := inCheck p' ∧
   legalReplies p' = []`, and prove `legalReplies` by strong induction once, so both
   the spec and the C proof reuse it. *Open:* can the C recursion be replaced by a
   non-recursive "evasions exist" check (faster too)? That would be a C change. It is
   deferred and gated on benchmarks.
2. **Sennichite over history.** The C compares hashes, while the spec must compare
   positions (board, hands, side). We keep the `NoCollision` hypothesis instead of
   modelling 64-bit collisions. The perpetual-check rule depends on which plies count
   as "the cycle": C uses the plies after the *first* of the last four occurrences.
   *Open:* confirm that this is the intended JSA reading, and check python-shogi's
   behaviour in T11.
3. **Kernel evaluation speed without `native_decide`.** Perft 2 (900 leaves, each
   needing legality with attack checks) may already be slow in the kernel. *Open*
   until T4 measures it. Fallbacks: reflection through a `Nat`-only fast path,
   checking `perft2` per first move (30 lemmas), or moving depth 2–3 to `cdiff` and
   documenting that.
4. **Table equality by `decide`.** About 15 KB of bytes. Fallback: per-square
   lemmas, or verify the generator *function* form instead of its output.
5. **MiniC aggregates (E6).** This is the largest semantic change. Getting padding
   wrong (e.g. `ShogiUndo`, `KingSafety` with `pinned[81]`) would be an unsound
   trust-base bug. *Mitigation:* the layout comes from the probe, and `cdiff`
   round-trips raw struct bytes.
6. **C refactors.** Only R2 (const tables) is planned. Anything else (removing the
   uchifuzume recursion, merging `_fast` and the normal make path) needs an NPS
   measurement and a separate PR. The proofs target the current code.
7. **Spec divergence from the engine.** Declaration uses 28 points for black and 27
   for white, and is checked before mate in `game_result`. *Open:* keep that exact
   rule in `Declaration.lean`, or model the CSA/USI 24/27-point variants as
   parameters?
8. **Toolchain churn.** Pin Lean `v4.35.0` to match tinygltf. Bump both together
   after T12.

---

### 8. Out of scope (this effort)

Search (`search.c`, PUCT, brute), evaluation and NNUE, int models, SIMD, the A64FX
assembly, threading, the GPU/CUDA/ROCm back ends, WASM/web glue, the USI front end
in `main.c`, time management, tsume (forced-mate) proofs, verification of minimax
(Wesselink et al. style), entering-king variants other than the one the engine
implements, and any proof that reaches compiled machine code.

---

#### Appendix: references

* tinygltf `formal/` (prior art, MIT) — `release` @ `97789b3`.
* Arthur742Ramos/chess-lean — reachable-position invariant by induction and perft
  regressions; this is the model for T3/T4.
* dwrensha/Chess.lean, elanroth/PuzzleProof — forced-mate theorems (future tsume work).
* Wesselink et al., *Formal Verification of Minimax Algorithms*, arXiv 2509.20138 (future search work).
* No earlier Lean/Coq/Isabelle formalization of shogi was found.
