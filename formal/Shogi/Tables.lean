/-
  The target-centred attack tables of src/shogi.c, defined from the spec.

  This is the Lean source of the first Lean → C component (PLAN.md §4):
  `tools/GenTables.lean` prints `src/shogi_tables.h` from these definitions,
  `tools/c2lean.py` re-imports the header, and `Shogi/C/Proofs/Tables.lean`
  proves that the imported bytes are `encode` of these tables. The generator
  is therefore not trusted.

  Layout (as in the C):
  * `step_attack_probes[attacker][target][10]`: squares from which a piece
    of `attacker` attacks `target` by a single step, with a bit mask of the
    piece types that do (bit `t.code`); rows `tr-2..tr+2`, columns
    `tc-2..tc+2` in row-major order; at most 10 entries;
  * `step_attack_probe_count[attacker][target]`;
  * `attack_rays[target][ray][8]`, `attack_ray_length[target][ray]`: the
    squares from `target` outwards in the 8 directions
    `(-1,-1) (-1,0) (-1,1) (0,-1) (0,1) (1,-1) (1,0) (1,1)`;
  * `attack_ray_masks[attacker][target][ray]`: the sliders of `attacker`
    that attack along that ray (bishop/horse diagonally, rook/dragon
    orthogonally, plus lance on the ray pointing towards its owner).
-/
import Shogi.Rules

namespace Shogi.Tables

def allTypes : List PieceType :=
  [.pawn, .lance, .knight, .silver, .gold, .bishop, .rook, .king,
   .proPawn, .proLance, .proKnight, .proSilver, .horse, .dragon]

def colorOf : Fin 2 → Color
  | 0 => .black
  | 1 => .white

/-- Bit mask of the types of `attacker` that attack by one step along
    `(dr, dc)` (from the attacker to the target). -/
def stepMask (attacker : Color) (dr dc : Int) : Nat :=
  (allTypes.filter fun t => (stepOffsets attacker.fwd t).contains (dr, dc)).foldl
    (fun m t => m ||| (1 <<< t.code)) 0

structure Probe where
  square : Nat
  mask : Nat
  deriving DecidableEq, Repr

def offsets5 : List Int := [-2, -1, 0, 1, 2]

/-- Step probes of `attacker` around `target`, in the C's iteration order. -/
def probes (attacker : Color) (target : Fin 81) : List Probe :=
  let tr : Int := Square.row target
  let tc : Int := Square.col target
  let all := offsets5.flatMap fun a => offsets5.filterMap fun b =>
    let r := tr + a
    let c := tc + b
    if r < 0 || r ≥ 9 || c < 0 || c ≥ 9 || (a == 0 && b == 0) then none
    else
      let m := stepMask attacker (tr - r) (tc - c)
      if m == 0 then none else some ⟨(r * 9 + c).toNat, m⟩
  all.take 10

/-- `probes` before the C's 10-entry cap. -/
def probesUncapped (attacker : Color) (target : Fin 81) : List Probe :=
  let tr : Int := Square.row target
  let tc : Int := Square.col target
  offsets5.flatMap fun a => offsets5.filterMap fun b =>
    let r := tr + a
    let c := tc + b
    if r < 0 || r ≥ 9 || c < 0 || c ≥ 9 || (a == 0 && b == 0) then none
    else
      let m := stepMask attacker (tr - r) (tc - c)
      if m == 0 then none else some ⟨(r * 9 + c).toNat, m⟩

/-- The 10-entry cap of `step_attack_probes` never drops an attacker. -/
theorem probes_uncapped (c : Color) : ∀ t : Fin 81,
    (probesUncapped c t).length ≤ 10 ∧ probes c t = probesUncapped c t := by
  cases c <;> decide +kernel

def rayDirs : List (Int × Int) :=
  [(-1, -1), (-1, 0), (-1, 1), (0, -1), (0, 1), (1, -1), (1, 0), (1, 1)]

def raySquares (target : Fin 81) (d : Int × Int) : List Nat :=
  (ray target d).map (·.val)

def rayMask (attacker : Color) (d : Int × Int) : Nat :=
  let diag := d.1 != 0 && d.2 != 0
  let base := if diag then (1 <<< PieceType.bishop.code) ||| (1 <<< PieceType.horse.code)
              else (1 <<< PieceType.rook.code) ||| (1 <<< PieceType.dragon.code)
  if !diag && d.2 == 0 && d.1 == -attacker.fwd then base ||| (1 <<< PieceType.lance.code)
  else base

/-! ## Byte image of the C arrays (x86-64 layout, checked by the probe) -/

def le16 (n : Nat) : List UInt8 := [(n % 256).toUInt8, (n / 256 % 256).toUInt8]

/-- `StepAttackProbe` is `{uint8_t square; uint16_t piece_mask;}`: 4 bytes
    with one padding byte (zero in a static initializer). -/
def probeBytes (p : Probe) : List UInt8 := [p.square.toUInt8, 0] ++ le16 p.mask

def padTo {α} (n : Nat) (x : α) (l : List α) : List α := l ++ List.replicate (n - l.length) x

def colors : List Color := [.black, .white]

def stepAttackProbesBytes : List UInt8 :=
  colors.flatMap fun c => (List.finRange 81).flatMap fun t =>
    (padTo 10 ⟨0, 0⟩ (probes c t)).flatMap probeBytes

def stepAttackProbeCountBytes : List UInt8 :=
  colors.flatMap fun c => (List.finRange 81).map fun t => (probes c t).length.toUInt8

def attackRaysBytes : List UInt8 :=
  (List.finRange 81).flatMap fun t => rayDirs.flatMap fun d =>
    (padTo 8 0 (raySquares t d)).map (·.toUInt8)

def attackRayLengthBytes : List UInt8 :=
  (List.finRange 81).flatMap fun t => rayDirs.map fun d => (raySquares t d).length.toUInt8

def attackRayMasksBytes : List UInt8 :=
  colors.flatMap fun c => (List.finRange 81).flatMap fun _ => rayDirs.flatMap fun d =>
    le16 (rayMask c d)

end Shogi.Tables
