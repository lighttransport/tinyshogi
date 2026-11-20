/-
  R3: `validate_material` (fid 48) refines the spec's `Position.materialOk`.
  The C fills a 7-entry maximum array, counts each unpromoted family on the
  board into a total array, adds both hands, and rejects if any total exceeds
  the maximum. The proof keeps the two arrays as symbolic functions of the
  loop index.
-/
import Shogi.C.Proofs.Pseudo4
import Shogi.C.Proofs.EntryPoints

set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

namespace Shogi.C.Proofs
variable {posBlock : Nat}
open MiniC Shogi Shogi.C

/-- The C maximum array (handMax) at each slot. -/
def maxArr (i : Fin 7) : Nat := PieceType.handMax i

/-- The family index of a piece byte, or 7 if it has no hand slot. -/
def famOfByte (b : UInt8) : Nat :=
  match PieceType.ofCode (b.toNat % 16) with
  | none => 7
  | some t =>
    match t.unpromote.handIndex with
    | some i => i.val
    | none => 7

/-- Board-family count among the first `k` squares. -/
def famAt (p : Position) (s : Nat) : Nat :=
  if h : s < 81 then famOfByte (pieceByte (p.pieceAt ⟨s, h⟩)) else 7

def boardFamCount (p : Position) (k : Nat) (i : Fin 7) : Nat :=
  (List.range k).countP (fun s => famAt p s = i.val)

@[simp] theorem code_mod_16 (t : PieceType) : t.code % 16 = t.code :=
  Nat.mod_eq_of_lt (by cases t <;> decide)

theorem famOfByte_eq (o : Option Piece) (i : Fin 7) :
    (famOfByte (pieceByte o) = i.val) ↔
      (match o with | some pc => pc.type.unpromote.handIndex == some i | none => false) := by
  cases o with
  | none => simp [pieceByte, famOfByte, PieceType.ofCode]; omega
  | some pc =>
      obtain ⟨c, t⟩ := pc
      cases c <;> cases t <;>
        simp [pieceByte, famOfByte, Piece.code, PieceType.ofCode_code,
          PieceType.unpromote, PieceType.handIndex, Fin.ext_iff, code_mod_16] <;> omega

theorem boardFamCount_take (p : Position) (hs : p.board.length = 81) (k : Nat) (i : Fin 7) :
    boardFamCount p k i =
      (p.board.take k).countP (fun o => famOfByte (pieceByte o) = i.val) := by
  induction k with
  | zero => simp [boardFamCount]
  | succ k ih =>
      rw [show boardFamCount p (k + 1) i =
          boardFamCount p k i + (if famAt p k = i.val then 1 else 0) by
        unfold boardFamCount
        rw [List.range_succ, List.countP_append]
        simp]
      rw [ih]
      by_cases hk81 : k < p.board.length
      · have ht : p.board.take (k + 1) = p.board.take k ++ [p.board[k]] := by
          rw [List.take_succ]
          simp [List.getElem?_eq_getElem hk81]
        rw [ht, List.countP_append]
        congr 1
        have hget : pieceByte p.board[k] = pieceByte (p.pieceAt ⟨k, by omega⟩) := by
          simp [Position.pieceAt, List.getD_eq_getElem?_getD, hk81]
        have hfameq : famAt p k = famOfByte (pieceByte p.board[k]) := by
          unfold famAt
          rw [dif_pos (show k < 81 by omega)]
          rw [hget]
        rw [hfameq]
        simp
      · have hlen : p.board.length ≤ k := by omega
        have ht : p.board.take (k + 1) = p.board.take k := by
          rw [List.take_of_length_le (show p.board.length ≤ k + 1 by omega),
            List.take_of_length_le (show p.board.length ≤ k by omega)]
        rw [ht]
        have hb : p.board[k]? = none := List.getElem?_eq_none hlen
        simp [famAt, show ¬ k < 81 by omega, hb]
        omega

theorem boardFamCount_81 (p : Position) (hs : p.board.length = 81) (i : Fin 7) :
    boardFamCount p 81 i + p.hand .black i + p.hand .white i = p.familyCount i := by
  rw [boardFamCount_take p hs, List.take_of_length_le (by omega)]
  unfold Position.familyCount
  apply congrArg (fun t => t + p.hand Color.black i + p.hand Color.white i)
  apply List.countP_congr
  intro o ho
  simp [famOfByte_eq]
  cases o <;> simp


/-- The unpromoted type code after `shogi_piece_type` + `shogi_unpromoted_type`. -/
def unpromotedCode (c : Nat) : Nat :=
  match PieceType.ofCode c with
  | none => 0
  | some t => t.unpromote.code

/-- The hand slot of a piece byte after unpromotion, or -1. -/
def byteFam (b : UInt8) : Int :=
  match PieceType.ofCode (unpromotedCode (b.toNat % 16)) with
  | none => -1
  | some t => match t.handIndex with
    | some i => (i.val : Int)
    | none => -1

theorem hand_index_compose (b : Fin 256) (h15 : b.val % 16 ≠ 15) :
    run Gen.fid_hand_index [u32 (unpromotedCode (b.val % 16))] =
      some (some (i32 (byteFam ⟨b.val, b.isLt⟩))) := by
  cases hb : PieceType.ofCode (b.val % 16) with
  | none =>
      have hc : b.val % 16 < 16 := Nat.mod_lt _ (by decide)
      have hall : ∀ c : Fin 16, c.val ≠ 0 → c.val ≠ 15 → PieceType.ofCode c.val ≠ none := by decide +kernel
      have h0 : b.val % 16 = 0 := by
        by_cases h : b.val % 16 = 0
        · exact h
        · exact False.elim (hall ⟨b.val % 16, hc⟩ h h15 hb)
      simp [unpromotedCode, byteFam, hb, h0]
      decide +kernel
  | some t =>
      simp [unpromotedCode, byteFam, hb, PieceType.ofCode_code]
      cases htu : t.unpromote <;> decide +kernel

end Shogi.C.Proofs

