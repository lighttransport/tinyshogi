# tinyshogi — formal specification and verification (Lean 4)

This directory holds a Lean 4 specification of the shogi rules implemented by
`src/shogi.c`, proofs about it, and (in progress) machine-checked proofs that
the C code refines the specification. The full plan, with milestones T0–T12,
is in [PLAN.md](PLAN.md).

Policy: `lake build` with no `sorry`, no Mathlib, no `native_decide`, no
`bv_decide`. Every theorem depends only on `propext`, `Classical.choice` and
`Quot.sound` (checked by `tools/axiomcheck.sh`).

## Build and check

```sh
cd formal
lake build                       # spec, kernel-checked fixtures, MiniC
python3 tools/c2lean.py --check  # Shogi/C/Gen.lean matches src/shogi.c
./tools/axiomcheck.sh            # axiom policy
python3 tools/cdiff.py --n 2000  # compiled C (ASan/UBSan) == Lean spec
```

Requirements: elan (installs the toolchain in `lean-toolchain`) and clang.

## Status

| Milestone | Scope | Status |
|---|---|---|
| T0 | scaffold, vendored MiniC, forked `c2lean.py`, CI, axiom check | **done** |
| T1 | pieces, positions, SFEN, USI | **done**: executable spec matching the C (incl. its tolerances). `Sfen.parse_print` (round trip for every well-formed position, including the 512-byte limit, `strtoul` and hand-count rules) and `parse_print_reachable`. `Usi.parse_print` |
| T2 | attacks, pseudo moves, legality, uchifuzume | **done**: executable spec. `legalMoves_iff` (fuel-free legality incl. the recursive uchifuzume rule), `legalAux_stable` (the recursion budget is adequate), king safety, no king or self capture, forced promotion, drop rules (hand, empty square, dead row, nifu) |
| T3 | invariants | **done**: `reachable_inv` (shape, no dead pieces), `reachable_kings` (exactly one king per side), `play_familyCount` / `reachable_material` (each unpromoted family is exactly a full set, so `validate_material` holds). make/unmake round trip: four-way tested (below), **todo** as a proof |
| T4 | perft, kernel speed | perft 1 kernel-checked (about 10 s). perft 2–5 compiled (`cdiff`, C tests). One fixture per rule is kernel-checked (5–25 s each) |
| T5 | MiniC/translator extensions | **done for the rules core**: E5 `alloc`, E7 `memcpy`/`memset`, E8 `ctz`. Translator: A-normal form (calls hoisted, short-circuit kept), memory locals, by-value structs, struct results, initialisers, enum typedefs (asserted by the probe), `_Bool`, `NULL`, `abs`, comma, `sizeof`, `static const` and after-init globals (bytes dumped by the probe), `switch` with `break`. Fuel monotonicity (`MiniC.Fuel`). 60/72 functions translate. The remaining 12 are SFEN/USI text I/O (libc `ctype`, `strtok_r`, `snprintf`), `shogi_init` (atomics) and printing |
| T6 | Lean → C tables | **done**: `src/shogi_tables.h` is generated from `Shogi/Tables.lean`; `*_refine` prove that the bytes clang emits equal the Lean tables; `probes_uncapped` (the 10-entry cap never drops an attacker). perft and NPS unchanged |
| T7 | helpers, attacks | layer 1 **done**: 17 helper refinements (piece bytes, types, promotion, hand index, squares, zone, `forced_promotion` = `deadRow`), every input. Layer 2: **`find_king_refines`** (symbolic, every position: the C search returns the spec's king square, stores it through `*square`, or returns 0 with memory unchanged). **`step_square_attacked_refines`** (symbolic, every position/target/attacker: returns 1 iff the spec's single-step attack holds; through `table_probes` and `probesAgree_all`, the probe table is exactly the spec's step geometry). **`square_attacked_refines`** (symbolic: the C attack detector returns exactly the spec's `attacked`, for every position, target and attacker; via `attacked_eq` and the decoded ray tables). **`shogi_is_in_check_refines`** (the C check test is exactly `Position.inCheck`; it composes `find_king` and `square_attacked` through a local allocated in memory). `shogi_piece_attacks_square`: four-way tested |
| T8–T10 | generators, make/unmake, legality, repetition | translated (`Shogi/C/Gen.lean`: move generation, king safety, probe make/unmake, `generate_legal_mut_internal` with the uchifuzume recursion, make/unmake with hash and history, repetition, declaration). The MiniC models agree with C and the spec (T11). Symbolic refinement proofs, every position: **`dropsC_spec`** (`add_pseudo_drops` appends exactly `dropMoves`, in order, hand counts < 256); **`pseudoC_spec`** (`generate_pseudo_for_color` appends a permutation of `pseudoMoves`: horse/dragon slides come before steps; the 600-move buffer cut is modelled exactly but not yet shown never to trigger); **`make_probe_spec`** (`make_legal_probe` leaves `encode (p.play m)` in the position block for every pseudo-legal move of a shaped position with at most one king per colour, and records the undo data); **`unmake_spec`** / **`probe_roundtrip`** (`unmake_legal_probe` restores `encode p`). **`king_safety_spec`** (`king_safety_prepare` builds the 84-byte record `ksRec`), with **`ksRec_inCheck`** (its `in_check` byte is `Position.inCheck`), **`ksRec_valid`** and **`ksRec_pinned`** (valid/king bytes, and `pinned[s]` = `pinnedSpec`: on some ray from the king, `s` is the first piece and an attacker slider is next); **`same_king_ray_spec`** (`same_king_ray` = `sameKingRay`, every king/from/to). Fast path of the legality filter: **`fastpath_sound`** (spec level: not in check, a non-king piece that is unpinned, or pinned and moving along the pin ray, never leaves the king attacked; ray geometry kernel-checked in `Geom.lean`, about 5 min), **`np_spec`** (the loop's `needs_probe` code computes `needsProbeC` from the record), **`skip_sound`** (`needsProbeC = false` implies the move is legal) and **`cKeep_eq`** (the C's two-path per-move decision equals the spec's `legalAux` test, given the recursive reply count). Loop iterations: **`iter_fast`** (fast path: copy, flags, `add_move`, `continue`) and **`probe_path`** (moves other than pawn drops: probe, check test, unprobe, keep exactly the legal ones; position restored). Memory frames for `square_attacked`/`shogi_is_in_check` via a generic no-write lemma (`NoWrite.lean`). **`probe_path_drop`** (pawn drops: kept exactly when legal and, if checking, the opponent has a reply, given `RecSpec` for the recursive call). Combined: **`iter_one`** (one iteration of the C loop appends a pseudo-legal move exactly when the spec's `legalAux` test keeps it, position unchanged). **`legal_loop`** (the whole filtering loop: over the pseudo-legal moves in the C's array it appends exactly `keepBytes`, the spec-kept moves, and leaves the position unchanged, given `RecSpec`, with bounded allocation per iteration). **`reachable_kingsUnique`** (positions reached by legal play satisfy `KingsUnique`). Glue: **`generate_pseudo_wrap`**, **`pseudoC_moves`** (the C's pseudo bytes are a move list that is a permutation of `pseudoMoves`) and **`keepBytes_perm`** (its kept moves are a permutation of `legalAux`). Body segments of `generate_legal_mut_internal`: **`legal_prologue`** (empty 600-move pseudo buffer), **`legal_call_pseudo`** (fills it with `pseudoC`), **`legal_count_init`** (empty output buffer), **`legal_safety`** (mover and `ksRec`, allocator state preserved). **todo**: chaining these segments with `legal_loop` and the final `return count` (pseudo generation into the 600-move buffer, `king_safety_prepare`, return count), the 600-move bound, the induction over the recursion that discharges `RecSpec`, full make/unmake with hash and history, repetition |
| T11 | differential testing | **done**: C (ASan/UBSan) vs spec on SFEN, legal moves, random walks, perft, game results (repetition, perpetual check, declaration). The **MiniC model of the C** vs compiled C vs spec on attacks, full legal-move generation, make-move (position and 64-bit Zobrist hash), and make/unmake round trips (both paths). python-shogi 1.1.1 with `--oracle` |

### Findings

* **python-shogi 1.1.1** allows a pawn-drop mate when the only piece that could
  capture the pawn is pinned (e.g. `9/9/gN7/P3+s4/4+p4/3g1L+s1p/k1p5p/3+PPP3/KG2r4
  w 3pSs2P 45`, `P*9h`). After the drop it reports checkmate itself. tinyshogi
  and the spec reject the drop. This position is now a kernel-checked fixture.
* **tinygltf `c2lean.py`** crashed on enumerators with implicit values, and
  translated a `for` condition before its init declaration. Both are fixed
  here and should go upstream.
* **Vendored `Hoare.lean`** referenced `C.store` after the namespace rename and
  had never compiled. Fixed.

## Layout

| File | Contents |
|---|---|
| `Shogi/Basic.lean` | colours, piece types (C codes), pieces, squares, moves, promotion zone, dead rows |
| `Shogi/Position.lean` | positions, hands, start position, material and king counts |
| `Shogi/Sfen.lean` | SFEN parse/print matching `shogi_position_from_sfen` / `write_sfen` |
| `Shogi/Usi.lean` | USI move parse/print, `parse_print` |
| `Shogi/Rules.lean` | attacks, pseudo-legal moves, drops, promotion, legality with uchifuzume, perft |
| `Shogi/Game.lean`, `Shogi/Declaration.lean` | history, sennichite with perpetual check, declaration, game result |
| `Shogi/Theorems.lean` | theorems about the rules (T2/T3) |
| `Shogi/SfenTheorems.lean` | SFEN round trip (T1) |
| `Shogi/Tables.lean` | attack tables (Lean source of `src/shogi_tables.h`) |
| `Shogi/Tests.lean`, `Shogi/RuleTests.lean` | kernel-checked fixtures |
| `Shogi/C/Model.lean` | abstraction: spec position ↦ `ShogiPosition` bytes, MiniC memory |
| `Shogi/AttackSpec.lean` | target-centred form of `attacked` (rays from the target) |
| `Shogi/TablesSpec.lean` | the probe table equals the spec's step-attack geometry (kernel-checked) |
| `Shogi/C/Proofs/Helpers.lean`, `Tables.lean`, `FindKing.lean`, `StepAttack.lean`, `SquareAttack.lean`, `InCheck.lean` | C refinement proofs (`FindKing.lean` sets up the method for loops over the board) |
| `Shogi/C/Proofs/AddMove.lean` … `DropsSpec.lean`, `Pseudo1`–`5`, `PseudoSpec.lean` | move generators: buffer model, `add_step`/`add_slide`/`add_pseudo_drops`, `generate_pseudo_for_color`, relation to `pseudoMoves` |
| `Shogi/C/Proofs/PlaySpec.lean`, `Probe1`–`9`, `Unmake.lean` | `Position.play` as byte edits, `make_legal_probe` / `unmake_legal_probe` |
| `Shogi/C/Proofs/KS1`–`3.lean`, `SameRay.lean` | `king_safety_prepare` (check and pin detection), `same_king_ray` |
| `Shogi/C/Proofs/FastPath.lean`, `Geom.lean`, `Geom2.lean`, `FastGlue.lean`, `NeedsProbe.lean` | soundness of the legality filter's no-probe fast path |
| `Shogi/C/Proofs/LegalIter.lean`, `LegalProbe.lean`, `LegalIter2.lean`, `LegalLoop.lean`, `NoWrite.lean`, `KingsUniq.lean` | the legality loop |
| `MiniC/Fuel.lean` | interpreter fuel monotonicity (tinyshogi addition) |
| `tools/GenTables.lean` | untrusted Lean → C emitter |
| `Shogi/C/Gen.lean` | **generated** from `src/shogi.c` by `tools/c2lean.py` — do not edit |
| `MiniC/*.lean` | MiniC semantics and proof rules, vendored from tinygltf (MIT, `MiniC/LICENSE-MIT`) |
| `CDiff.lean`, `tools/cdiff.py`, `tools/cdiff_c.c` | differential testing |

## What is trusted

The Lean kernel; the MiniC semantics (`MiniC/Semantics.lean`); `tools/c2lean.py`
and clang's front end; an LP64 little-endian target; the C compiler (proofs do
not reach machine code). See PLAN.md §6 for the full list, including what is not
modelled.

tinyshogi's additions to the MiniC semantics (all trusted, all exercised by the
four-way `cdiff`):

| Ext | Construct | Semantics, and what it does not detect |
|---|---|---|
| E5 | `Stmt.alloc` | fresh zero-filled block for an address-taken, array or struct local. The next block number lives in block 0. Blocks are never freed, so use after return and reads of uninitialised locals are **not** UB in the model |
| E7 | `Stmt.memcpy`, `Stmt.memset` | C semantics on byte ranges; overlapping `memcpy` is UB |
| E8 | `UnOp.ctz` | lowest set bit; `ctz 0` is UB |

Translator lowerings (validated by `--check`, `cdiff` and the four-way runs):
calls are hoisted out of expressions into statements, with `&&`, `||` and `?:`
expanded into `if` so short-circuiting is kept. Postfix `++`/`--` become
temporaries. By-value struct parameters are copied by the callee on entry.
Struct results go through a hidden first parameter. Struct assignment and
initialisation become `memcpy` or per-field stores. `static const` local
arrays are re-initialised per call (they are read-only). Global table bytes,
layouts and the enum representation are measured by a probe compiled with the
same clang.

## Attribution

`MiniC/` and `tools/c2lean.py` come from the `formal/` directory of
[syoyo/tinygltf](https://github.com/syoyo/tinygltf) (`release` @ `97789b3`,
MIT licence). Each file states its origin and what was changed.
