/-
  T8: `make_legal_probe`, part 1 — reading and writing the position block
  held as `enc …`.
-/
import Shogi.C.Proofs.PlaySpec

namespace Shogi.C.Proofs
variable {posBlock : Nat}
open MiniC Shogi Shogi.C

section encread
variable (pa : Square → Option Piece) (h : Color → Fin 7 → Nat) (sd : Color) (kb kw : UInt8)

theorem enc_getD_board (x : Square) : (enc pa h sd kb kw).getD x.val 0 = pieceByte (pa x) := by
  unfold enc; simp only [List.append_assoc]
  rw [List.getD_eq_getElem?_getD, List.getElem?_append_left (by simp)]
  simp

theorem enc_getD_hand (c : Color) (i : Fin 7) :
    (enc pa h sd kb kw).getD (81 + 7 * c.idx + i.val) 0 = (h c i).toUInt8 := by
  unfold enc; simp only [List.append_assoc]
  rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by simp; omega)]
  simp only [List.length_map, List.length_finRange]
  cases c
  · rw [show 81 + 7 * Color.black.idx + i.val - 81 = i.val by simp [Color.idx],
      List.getElem?_append_left (by simp)]; simp
  · rw [show 81 + 7 * Color.white.idx + i.val - 81 = 7 + i.val by simp [Color.idx]; omega,
      List.getElem?_append_right (by simp), List.getElem?_append_left (by simp)]; simp

theorem enc_getD_king (c : Color) :
    (enc pa h sd kb kw).getD (112 + c.idx) 0 = (match c with | .black => kb | .white => kw) := by
  cases c <;> simp [enc, Color.idx, List.getD_eq_getElem?_getD, List.getElem?_append_right, le32]

theorem enc_side :
    ((enc pa h sd kb kw).drop 96).take 4 = le32 sd.idx := by
  let P : List UInt8 := (List.finRange 81).map (fun s => pieceByte (pa s)) ++
      ((List.finRange 7).map (fun i => (h .black i).toUInt8) ++ (List.finRange 7).map (fun i => (h .white i).toUInt8)) ++
      [0]
  have hP : P.length = 96 := by simp [P]
  have e : enc pa h sd kb kw = P ++ (le32 sd.idx ++ (List.replicate 12 0 ++ [kb, kw])) := by
    simp [enc, P, List.append_assoc]
  rw [e, List.drop_left' hP, List.take_left' (by simp [le32])]

end encread

end Shogi.C.Proofs
