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
| T0 | scaffold, vendored MiniC, forked `c2lean.py`, CI, axiom check | **done**: `Gen.lean` has `shogi_piece`, `row_of`, `col_of`, `square_at` |
| T1 | pieces, positions, SFEN and USI | **in progress**: executable SFEN/USI spec matching the C, including its tolerances. `Usi.parse_print` is proven. The fixtures from `tests/test_rules.c` are kernel-checked. `cdiff` agrees with the C on 40k inputs. The general SFEN round-trip theorem is still to do |
| T2–T12 | see PLAN.md | todo |

## Layout

| File | Contents |
|---|---|
| `Shogi/Basic.lean` | colours, piece types (C codes), pieces, squares, moves, promotion zone, dead rows |
| `Shogi/Position.lean` | positions, hands, start position, material and king counts |
| `Shogi/Sfen.lean` | SFEN parse/print matching `shogi_position_from_sfen` / `write_sfen` |
| `Shogi/Usi.lean` | USI move parse/print, `parse_print` |
| `Shogi/Tests.lean` | kernel-checked fixtures (`decide`) |
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
