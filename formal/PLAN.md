# tinyshogi `formal/` — plan for a Lean 4 formalization of the shogi rules

Status: **plan for review**. No proofs or C changes are in this PR. This file
answers the brief in `plan.md` (kept out of the tree).

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

## 1. Phase 0 findings

Prior art: local tinygltf checkout, branch `release` @ `97789b3`, `formal/`
(Lean `v4.35.0`, MiniC `GlTF/C/Semantics.lean` 620 lines, `tools/c2lean.py` 737 lines).

### 1.1 The rules core

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

### 1.2 `c2lean.py` on unmodified `src/shogi.c`

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

### 1.3 What MiniC cannot model, and what to do about it

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

### 1.4 Existing fixtures to reuse

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

## 2. Vendor, share, or fork the tinygltf pipeline?

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

### MiniC extensions and how each is validated

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

## 3. Directory layout, build, and CI

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

## 4. Lean → C: design and first target

### Design (translation validation)

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

### First target: attack tables (`step_attack_probes`, `attack_rays`, `attack_ray_length`, `attack_ray_masks`)

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

### Comparison

| Option | Verified? | Adds to the trust base |
|---|---|---|
| Translation validation (this plan) | yes, per output | nothing beyond MiniC, c2lean and clang, which are already trusted |
| Lean's own compiler (`lean --c`, IR → C) | no | the whole Lean compiler, its runtime (`lean.h`, RC/boxing, GMP) and the IR passes. The output is not idiomatic C and cannot replace `shogi.c` |
| Verified compilers from a Lean-embedded IR (e.g. CompCert-style Clight back ends, CertiCoq for Coq, CakeML for HOL4) | yes, but none target Lean 4 C emission today | a second semantics (Clight) and a link from it to MiniC. Too large for this project |
| Aeneas / Charon (Rust → Lean) | n/a (opposite direction, Rust) | — (mentioned only to show this is not covered elsewhere) |

---

## 5. Milestones

The effort is in focused engineer-weeks (w), assuming someone who knows Lean;
proof-heavy work has ±50 %. Each milestone ends with `lake build` green, no `sorry`,
and a `README.md` status row.

### T0 — scaffold (0.5 w)
Scope: `formal/` Lake project, vendored MiniC unchanged (renamed namespace), c2lean
config with the 6 functions that already pass, CI job, `AxiomCheck`.
Exit: CI green, and `Gen.lean` contains `shogi_piece`, `row_of`, `col_of`, `square_at`.

### T1 — spec core and SFEN/USI (2 w)
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

### T2 — pseudo moves, attacks, legality (3 w)
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

### T3 — invariants and make/unmake (2 w)
```lean
inductive Reachable : Position → Prop | start : Reachable start | step : Reachable p → m ∈ legalMoves p → Reachable (apply p m)
def WF (p : Position) : Prop   -- 40 pieces (board + hands, unpromoted counts 18/4/4/4/4/2/2/2), ≤ 1 king per side, no dead pieces, ≤ 1 unpromoted pawn per file per side
theorem reachable_wf : Reachable p → WF p
theorem apply_undo : IsLegal p m → undo (apply p m) (undoInfo p m) = p
theorem kings_exact : Reachable p → ∀ c, kingCount p c = 1
```
Exit: proven. `WF` also matches the C function `validate_material`
(`theorem validate_material_iff` at the spec level).

### T4 — perft and kernel-speed measurement (1 w)
```lean
theorem perft1 : perft start 1 = 30  := by decide
theorem perft2 : perft start 2 = 900 := by decide
-- perft3 = 25470: attempted with `decide` + `Nat.decEq` by reflection; kept only if under the CI budget
```
Exit: measured kernel time per depth is recorded in the README. If depth 3 exceeds
about 10 minutes, it moves to `cdiff` (Lean compiled `#eval`, which is allowed
because it is a test and not a proof), together with depth 4 = 719731. Also
measures `decide` on the table equality from §4 (≈ 15 KB).

### T5 — MiniC extensions and translator (3 w)
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

### T6 — abstraction function and table refinement (1.5 w)
```lean
def Abs.position (m : MiniC.Mem) (ptr : MiniC.Ptr) : Option Shogi.Position   -- decode board/hand/side bytes
def Abs.Inv (m : MiniC.Mem) (ptr : MiniC.Ptr) : Prop   -- WF + king_square cache coherent + history_length ≤ 4096
theorem tables_refine : MiniC.globalsOf GenTables.prog = Tables.encode Tables.init      -- Lean → C, §4
theorem probe_sound_complete, ray_correct                                                -- tables ↔ spec
```

### T7 — bit helpers and attacks (2 w)
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

### T8 — per-piece generators and pseudo generation (3 w)
```lean
theorem add_step_refines / add_slide_refines / add_pseudo_drops_refines :
  writes exactly `encodeMoves (spec list)` at moves[count..], count' = count + len, nothing else
theorem generate_pseudo_refines : … moves[0..n) = encodeMoves (pseudoMoves (abs m p)) ∧ n ≤ 600
theorem pseudo_piece_field : m ∈ pseudo → m.piece = board[m.from]        -- makes unmake_legal_probe correct
```

### T9 — make/unmake, legality filter, repetition (4 w)
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

### T10 — `_fast` make/unmake and game result (1.5 w)
`shogi_make_move_undo_fast` and `shogi_unmake_move` round-trip;
`shogi_game_result_with_moves{,_mut}` = `Game.result` (repetition → declaration → mate).
Declaration is proven against `Shogi/Declaration.lean`, which is an optional module.

### T11 — differential testing at full scale (1.5 w; starts in T5 and grows)
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

### T12 — shared MiniC package (1 w, optional)
Extract `minic` as its own package, switch both tinyshogi and tinygltf to it, and
check that tinygltf's `Gen.lean` is byte-identical.

**Total ≈ 26 engineer-weeks** (T0–T11). T1–T4 (the spec) are useful on their own,
and T5 + T6 deliver the first Lean → C artifact.

---

## 6. Trust base

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

## 7. Risks and open questions

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

## 8. Out of scope (this effort)

Search (`search.c`, PUCT, brute), evaluation and NNUE, int models, SIMD, the A64FX
assembly, threading, the GPU/CUDA/ROCm back ends, WASM/web glue, the USI front end
in `main.c`, time management, tsume (forced-mate) proofs, verification of minimax
(Wesselink et al. style), entering-king variants other than the one the engine
implements, and any proof that reaches compiled machine code.

---

### Appendix: references

* tinygltf `formal/` (prior art, MIT) — `release` @ `97789b3`.
* Arthur742Ramos/chess-lean — reachable-position invariant by induction and perft
  regressions; this is the model for T3/T4.
* dwrensha/Chess.lean, elanroth/PuzzleProof — forced-mate theorems (future tsume work).
* Wesselink et al., *Formal Verification of Minimax Algorithms*, arXiv 2509.20138 (future search work).
* No earlier Lean/Coq/Isabelle formalization of shogi was found.
