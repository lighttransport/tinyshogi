import Shogi.C.Proofs.Fid18Guard
namespace Shogi.C.Proofs
open MiniC Shogi Shogi.C Shogi.C.Proofs

theorem piece_code_color (q : Piece) : q.code / 16 % 2 = q.color.idx := by
  obtain ⟨c, ty⟩ := q
  cases c <;> cases ty <;> decide +kernel

theorem piece_code_mod16 (q : Piece) : q.code % 16 = q.type.code := by
  obtain ⟨c, ty⟩ := q
  cases c <;> cases ty <;> decide +kernel

theorem piece_code_lt256 (q : Piece) : q.code < 256 := by
  obtain ⟨c, ty⟩ := q
  cases c <;> cases ty <;> decide +kernel

theorem piece_code_ne_zero (q : Piece) : q.code ≠ 0 := by
  obtain ⟨c, ty⟩ := q
  cases c <;> cases ty <;> decide

set_option maxRecDepth 100000 in
theorem slide_geom_finite : ∀ (f t : Square), f ≠ t →
  ((if (t.row : Int) - f.row < 0 then -((t.row : Int) - f.row) else (t.row : Int) - f.row) =
   (if (t.col : Int) - f.col < 0 then -((t.col : Int) - f.col) else (t.col : Int) - f.col) ∧
   (t.row : Int) - f.row ≠ 0) ∨
  ((t.row : Int) - f.row = 0 ∧ (t.col : Int) - f.col ≠ 0) ∨
  ((t.col : Int) - f.col = 0 ∧ (t.row : Int) - f.row ≠ 0) →
  let dr : Int := (t.row : Int) - f.row
  let dc : Int := (t.col : Int) - f.col
  let rs : Int := if dr > 0 then 1 else if dr < 0 then -1 else 0
  let cs : Int := if dc > 0 then 1 else if dc < 0 then -1 else 0
  let k : Nat := max dr.natAbs dc.natAbs
  let d : Nat := k - 1
  let row : Int := (f.row : Int) + rs
  let col : Int := (f.col : Int) + cs
  (t.row : Int) = row + (d : Int) * rs ∧
  (t.col : Int) = col + (d : Int) * cs ∧
  (∀ i, i ≤ d → 0 ≤ row + (i : Int) * rs ∧ row + (i : Int) * rs < 9 ∧
                  0 ≤ col + (i : Int) * cs ∧ col + (i : Int) * cs < 9) ∧
  (rs ≠ 0 ∨ cs ≠ 0) ∧
  1 ≤ k ∧ k ≤ 8
:= by decide +kernel


end Shogi.C.Proofs
