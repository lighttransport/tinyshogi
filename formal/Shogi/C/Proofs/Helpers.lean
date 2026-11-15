/-
  T7 layer 1: refinement of the piece and square helpers of src/shogi.c.

  Each theorem says: for every argument in the stated domain, the translated
  C function (MiniC, `Shogi.C.Gen`) terminates without undefined behaviour
  and returns the value the spec prescribes. `Returns` quantifies over all
  sufficiently large fuel, so it is the same judgement as `ExS` for a whole
  call. The proofs evaluate the interpreter in the kernel (`decide +kernel`)
  once per argument and lift with `MiniC.callFunc_mono`.

  These functions take scalars and touch no memory; they are run in the
  empty memory.
-/
import MiniC.Fuel
import Shogi.C.Gen
import Shogi.Basic

namespace Shogi.C.Proofs
open MiniC

def m0 : Mem := fun _ => none

def u8 (n : Nat) : Val := .int IntTy.u8 n
def i8 (n : Int) : Val := .int IntTy.i8 (IntTy.wrap IntTy.i8 n)
def u32 (n : Nat) : Val := .int IntTy.u32 n
def i32 (n : Int) : Val := .int IntTy.i32 (IntTy.wrap IntTy.i32 n)
def bool8 (b : Bool) : Val := u8 (if b then 1 else 0)

/-- `f(args)` terminates without UB and returns `v`. -/
def Returns (f : Nat) (args : List Val) (v : Val) : Prop :=
  ∃ K, ∀ k, K ≤ k → retOf (callFunc Gen.prog k f args m0) = some (some v)

def run (f : Nat) (args : List Val) : Option (Option Val) :=
  retOf (callFunc Gen.prog 64 f args m0)

theorem returns_of_run {f args v} (h : run f args = some (some v)) : Returns f args v :=
  ⟨64, callFunc_mono Gen.prog h⟩

/-! ## Piece bytes -/

/-- `shogi_piece(color, type) = type | color << 4`, the spec's `Piece.code`. -/
theorem shogi_piece_refines (c : Color) (t : PieceType) :
    Returns Gen.fid_shogi_piece [u32 c.idx, u32 t.code] (u8 (Piece.code ⟨c, t⟩)) :=
  returns_of_run (by cases c <;> cases t <;> decide +kernel)

/-- On every byte, `shogi_piece_type` is the low nibble... -/
theorem shogi_piece_type_total :
    ∀ b : Fin 256, run Gen.fid_shogi_piece_type [u8 b.val] = some (some (u32 (b.val % 16))) := by
  decide +kernel

/-- ...and `shogi_piece_color` is bit 4. -/
theorem shogi_piece_color_total :
    ∀ b : Fin 256, run Gen.fid_shogi_piece_color [u8 b.val]
      = some (some (u32 (if b.val / 16 % 2 = 1 then 1 else 0))) := by
  decide +kernel

/-- Decoding a piece byte gives back the spec piece. -/
theorem shogi_piece_type_refines (pc : Piece) :
    Returns Gen.fid_shogi_piece_type [u8 pc.code] (u32 pc.type.code) :=
  returns_of_run (by obtain ⟨c, t⟩ := pc; cases c <;> cases t <;> decide +kernel)

theorem shogi_piece_color_refines (pc : Piece) :
    Returns Gen.fid_shogi_piece_color [u8 pc.code] (u32 pc.color.idx) :=
  returns_of_run (by obtain ⟨c, t⟩ := pc; cases c <;> cases t <;> decide +kernel)

/-! ## Piece types -/

theorem shogi_is_promoted_refines (t : PieceType) :
    Returns Gen.fid_shogi_is_promoted [u32 t.code] (bool8 t.isPromoted) :=
  returns_of_run (by cases t <;> decide +kernel)

theorem shogi_can_promote_refines (t : PieceType) :
    Returns Gen.fid_shogi_can_promote [u32 t.code] (bool8 t.canPromote) :=
  returns_of_run (by cases t <;> decide +kernel)

theorem promoted_type_refines (t : PieceType) :
    Returns Gen.fid_promoted_type [u32 t.code] (u32 t.promote.code) :=
  returns_of_run (by cases t <;> decide +kernel)

theorem shogi_unpromoted_type_refines (t : PieceType) :
    Returns Gen.fid_shogi_unpromoted_type [u32 t.code] (u32 t.unpromote.code) :=
  returns_of_run (by cases t <;> decide +kernel)

/-- `hand_index`: the slot, or -1 for king and promoted types. -/
theorem hand_index_refines (t : PieceType) :
    Returns Gen.fid_hand_index [u32 t.code]
      (i32 (match t.handIndex with | some i => (i.val : Int) | none => -1)) :=
  returns_of_run (by cases t <;> decide +kernel)

theorem piece_letter_refines (t : PieceType) :
    Returns Gen.fid_piece_letter [u32 t.code] (i8 t.letter.toNat) :=
  returns_of_run (by cases t <;> decide +kernel)

/-! ## Squares and rows -/

theorem row_of_refines : ∀ s : Fin 81,
    run Gen.fid_row_of [u8 s.val] = some (some (i32 (Square.row s))) := by decide +kernel

theorem col_of_refines : ∀ s : Fin 81,
    run Gen.fid_col_of [u8 s.val] = some (some (i32 (Square.col s))) := by decide +kernel

theorem square_at_refines : ∀ r c : Fin 9,
    run Gen.fid_square_at [i32 r.val, i32 c.val] = some (some (u8 (r.val * 9 + c.val))) := by
  decide +kernel

/-- `on_board` agrees with `Square.mk?` on every row/column in `[-9, 17]`
    (every offset the generators can produce from a board square). -/
theorem on_board_refines : ∀ r c : Fin 27,
    run Gen.fid_on_board [i32 (r.val - 9 : Int), i32 (c.val - 9 : Int)]
      = some (some (bool8 (Square.mk? (r.val - 9 : Int) (c.val - 9 : Int)).isSome)) := by
  decide +kernel

/-- `in_promotion_zone` is the spec's `inZone`. -/
theorem in_promotion_zone_refines (c : Color) : ∀ r : Fin 9,
    run Gen.fid_in_promotion_zone [u32 c.idx, i32 r.val] = some (some (bool8 (inZone c r.val))) := by
  cases c <;> decide +kernel

/-- `forced_promotion` is the spec's `deadRow`: the C rule for mandatory
    promotion and for illegal drops coincides with "no further move". -/
theorem forced_promotion_refines (c : Color) (t : PieceType) : ∀ r : Fin 9,
    run Gen.fid_forced_promotion [u32 c.idx, u32 t.code, i32 r.val]
      = some (some (bool8 (deadRow c t r.val))) := by
  cases c <;> cases t <;> decide +kernel

end Shogi.C.Proofs
