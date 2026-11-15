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
| T1 | pieces, positions, SFEN, USI | executable spec matching the C (incl. its tolerances), `Usi.parse_print` proven, fixtures kernel-checked. **todo**: general SFEN round-trip theorem |
| T2 | attacks, pseudo moves, legality, uchifuzume | **done**: executable spec. `legalMoves_iff` (fuel-free legality incl. the recursive uchifuzume rule), `legalAux_stable` (the recursion budget is adequate), king safety, no king or self capture, forced promotion, drop rules (hand, empty square, dead row, nifu) |
| T3 | invariants | **done**: `reachable_inv` (shape, no dead pieces), `reachable_kings` (exactly one king per side). **todo**: material conservation, make/unmake round trip |
| T4 | perft, kernel speed | perft 1 kernel-checked (about 10 s). perft 2–5 compiled (`cdiff`, C tests). One fixture per rule is kernel-checked (5–25 s each) |
| T5 | MiniC/translator extensions | **partial**: enum typedefs (checked by `_Static_assert` in the probe), `_Bool` conversion, `NULL`/pointer equality, `for` scoping, enum case labels, `abs`, the comma operator, `static const` globals (bytes dumped by the probe), fuel monotonicity (`MiniC.Fuel`). 34/72 functions translate (`tools/c2lean_report.py`) |
| T6 | Lean → C tables | **done**: `src/shogi_tables.h` is generated from `Shogi/Tables.lean`; `*_refine` prove that the bytes clang emits equal the Lean tables; `probes_uncapped` (the 10-entry cap never drops an attacker). perft and NPS unchanged |
| T7 | helpers, attacks | layer 1 **done**: 17 helper refinements (piece bytes, types, promotion, hand index, squares, zone, `forced_promotion` = `deadRow`), every input. Layer 2 (`square_attacked`, `shogi_piece_attacks_square`): translated and four-way tested; **todo**: symbolic proofs |
| T8–T10 | generators, make/unmake, legality, repetition | todo (four-way tested at spec level, see T11) |
| T11 | differential testing | **done**: C (ASan/UBSan) vs spec on SFEN, legal moves, random walks, perft, game results (repetition, perpetual check, declaration). MiniC model vs C vs spec on attacks. python-shogi 1.1.1 with `--oracle` |

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
| `Shogi/Tables.lean` | attack tables (Lean source of `src/shogi_tables.h`) |
| `Shogi/Tests.lean`, `Shogi/RuleTests.lean` | kernel-checked fixtures |
| `Shogi/C/Model.lean` | abstraction: spec position ↦ `ShogiPosition` bytes, MiniC memory |
| `Shogi/C/Proofs/Helpers.lean`, `Tables.lean` | C refinement proofs |
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

## Attribution

`MiniC/` and `tools/c2lean.py` come from the `formal/` directory of
[syoyo/tinygltf](https://github.com/syoyo/tinygltf) (`release` @ `97789b3`,
MIT licence). Each file states its origin and what was changed.
