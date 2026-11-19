/-
  T7: `add_pseudo_drops` produces exactly the spec's drop moves
  (`Position.dropMoves`), in the same order, as move bytes.
-/
import Shogi.C.Proofs.AddDrops2

namespace Shogi.C.Proofs
variable {posBlock : Nat}
open MiniC Shogi Shogi.C

theorem and_two_pow_ne (x i : Nat) : decide (x &&& 2 ^ i ≠ 0) = x.testBit i := by
  have h : x &&& 2 ^ i = if x.testBit i then 2 ^ i else 0 := by
    apply Nat.eq_of_testBit_eq; intro j
    rw [Nat.testBit_and, Nat.testBit_two_pow]
    split
    · next hb => rw [Nat.testBit_two_pow]; by_cases e : i = j
                 · subst e; simp [hb]
                 · simp [e]
    · next hb => by_cases e : i = j
                 · subst e; simp [hb]
                 · simp [e]
  rw [h]; split
  · next hb => simp [hb, Nat.two_pow_pos]
  · next hb => simp [hb]

theorem actUpTo_testBit (p : Position) (c : Color) :
    ∀ i j, (actUpTo p c i).testBit j = (decide (j < i) && decide (hb p c j ≠ 0)) := by
  intro i; induction i with
  | zero => intro j; simp [actUpTo]
  | succ i ih =>
    intro j; simp only [actUpTo]; split
    · next h => rw [Nat.testBit_or, ih, Nat.testBit_two_pow]
                by_cases e : i = j
                · subst e; simp [h]
                · have : j < i + 1 ↔ j < i := by omega
                  simp [e, this]
    · next h => rw [ih]
                by_cases e : j = i
                · subst e; simp at h; simp [h]
                · have : j < i + 1 ↔ j < i := by omega
                  simp [this]

theorem pawnUpTo_testBit (p : Position) (K col : Nat) (hcol : col < 9) :
    ∀ k, (pawnUpTo p K k).testBit col = (List.range k).any (fun j => bb p j == K && j % 9 == col) := by
  intro k; induction k with
  | zero => simp [pawnUpTo]
  | succ k ih =>
    simp only [pawnUpTo, List.range_succ, List.any_append, List.any_cons, List.any_nil, Bool.or_false]
    split
    · next h => rw [Nat.testBit_or, ih, Nat.testBit_two_pow]; simp only [h, beq_self_eq_true, Bool.true_and]; rfl
    · next h => rw [ih]; simp [h]

theorem hb_eq (p : Position) (c : Color) (i : Fin 7) : hb p c i.val = p.hand c i % 256 := by
  unfold hb encode
  rw [List.getD_eq_getElem?_getD]
  have hi := i.isLt
  cases c
  · simp [List.getElem?_append_left, List.getElem?_append_right, Color.idx, hi, Gen.off_side,
      Gen.off_king_square, Position.hand]
  · simp only [Color.idx, List.append_assoc]
    rw [List.getElem?_append_right (by simp; omega), List.getElem?_append_right (by simp; omega),
      List.getElem?_append_left (by simp; omega)]
    simp [Position.hand, show 81 + 7 * 1 + i.val - 81 - 7 = i.val by omega]

theorem bb_pawn (p : Position) (c : Color) (j : Nat) (hj : j < 81) :
    (bb p j == Piece.code ⟨c, .pawn⟩) = (p.pieceAt ⟨j, hj⟩ == some ⟨c, .pawn⟩) := by
  unfold bb; rw [dif_pos hj, pieceByte_toNat]
  cases h : p.pieceAt ⟨j, hj⟩ with
  | none => cases c <;> decide
  | some q => obtain ⟨qc, qt⟩ := q; cases qc <;> cases qt <;> cases c <;> decide

theorem bb_empty (p : Position) (j : Nat) (hj : j < 81) :
    decide (bb p j ≠ 0) = !(p.isEmpty ⟨j, hj⟩) := by
  unfold bb Position.isEmpty; rw [dif_pos hj, pieceByte_toNat]
  cases h : p.pieceAt ⟨j, hj⟩ with
  | none => rfl
  | some q => obtain ⟨qc, qt⟩ := q; cases qc <;> cases qt <;> decide

theorem finRange81_val : (List.finRange 81).map Fin.val = List.range 81 := by decide

theorem pawnOnFile_eq (p : Position) (c : Color) (col : Nat) (hcol : col < 9) :
    (pawnUpTo p (Piece.code ⟨c, .pawn⟩) 81).testBit col = p.pawnOnFile c col := by
  rw [pawnUpTo_testBit p _ col hcol, ← finRange81_val, List.any_map]
  unfold Position.pawnOnFile
  congr 1; funext s
  simp only [Function.comp]
  rw [bb_pawn p c s.val s.isLt]
  simp only [Square.col, Bool.and_comm]

theorem code_ofHandIndex (i : Fin 7) : (PieceType.ofHandIndex i).code = i.val + 1 := by revert i; decide

theorem ofHandIndex_pawn (i : Fin 7) : (PieceType.ofHandIndex i == .pawn) = (i.val == 0) := by revert i; decide

theorem map_filter_eq_filterMap {α β : Type} (q : α → Bool) (g : α → β) :
    ∀ l : List α, (l.filter q).map g = l.filterMap (fun x => if q x then some (g x) else none) := by
  intro l; induction l with
  | nil => rfl
  | cons a l ih => by_cases h : q a = true <;> simp [List.filter_cons, h, ih, List.filterMap_cons]

/-- The spec's drops on one square, as move bytes. -/
def specCell (p : Position) (c : Color) (d : Square) : List (List UInt8) :=
  ((List.finRange 7).filterMap fun i =>
    let t := PieceType.ofHandIndex i
    if p.hand c i > 0 && p.dropAllowed c t d then some (Move.drop t d) else none).map (moveBytes p)

theorem cell_eq (p : Position) (c : Color) (hw : ∀ i, p.hand c i < 256) (r col : Nat) (hr : r < 9) (hcol : col < 9) :
    cellOut p c (actUpTo p c 7) (pawnUpTo p (Piece.code ⟨c, .pawn⟩) 81) r col =
      specCell p c ⟨r * 9 + col, by omega⟩ := by
  have hd : r * 9 + col < 81 := by omega
  have hrow : Square.row ⟨r * 9 + col, hd⟩ = r := by simp [Square.row]; omega
  have hcl : Square.col ⟨r * 9 + col, hd⟩ = col := by simp [Square.col]; omega
  unfold cellOut specCell
  rw [List.map_filterMap]
  have hE := bb_empty p (r * 9 + col) hd
  split
  · next hocc =>
    have : p.isEmpty ⟨r * 9 + col, hd⟩ = false := by simpa [hocc] using hE
    symm; apply List.filterMap_eq_nil_iff.mpr
    intro i _; simp [Position.dropAllowed, this]
  · next hocc =>
    have hemp : p.isEmpty ⟨r * 9 + col, hd⟩ = true := by simpa [hocc] using hE
    unfold allowedS
    rw [List.map_map, map_filter_eq_filterMap]
    congr 1; funext i
    have hbit := actUpTo_testBit p c 7 i.val
    rw [hb_eq p c i, Nat.mod_eq_of_lt (hw i)] at hbit
    have hpf := pawnOnFile_eq p c col hcol
    rw [← and_two_pow_ne] at hpf
    simp only [hbit, hpf, i.isLt, decide_true, Bool.true_and, Position.dropAllowed, hemp, hrow, hcl,
      ofHandIndex_pawn]
    by_cases h0 : p.hand c i = 0
    · simp [h0]
    · have : 0 < p.hand c i := Nat.pos_of_ne_zero h0
      simp only [h0, this, ne_eq, not_false_eq_true, decide_true, Bool.true_and]
      generalize deadRow c (PieceType.ofHandIndex i) r = a
      generalize (i.val == 0 && p.pawnOnFile c col) = b
      cases a <;> cases b <;> simp [moveBytes, dmBytes, code_ofHandIndex]

theorem flatMap_congr_mem {α β : Type} {f g : α → List β} :
    ∀ l : List α, (∀ x ∈ l, f x = g x) → l.flatMap f = l.flatMap g := by
  intro l; induction l with
  | nil => intro _; rfl
  | cons a l ih =>
    intro h; simp only [List.flatMap_cons]
    rw [h a (by simp), ih (fun x hx => h x (by simp [hx]))]

theorem range81_rows : List.range 81 =
    (List.range' 0 9).flatMap (fun r => (List.range' 0 9).map (fun col => r * 9 + col)) := by decide

/-- The square loops visit squares 0..80 in order. -/
theorem rowsOut_spec (p : Position) (c : Color) (hw : ∀ i, p.hand c i < 256) :
    rowsOut p c (actUpTo p c 7) (pawnUpTo p (Piece.code ⟨c, .pawn⟩) 81) 0 9 =
      (List.finRange 81).flatMap (specCell p c) := by
  let G : Nat → List (List UInt8) := fun j => if h : j < 81 then specCell p c ⟨j, h⟩ else []
  have h1 : (List.finRange 81).flatMap (specCell p c) = (List.range 81).flatMap G := by
    rw [← finRange81_val, List.flatMap_map]
    exact flatMap_congr_mem _ (fun s _ => by simp [G, s.isLt])
  rw [h1, range81_rows, List.flatMap_assoc]
  unfold rowsOut
  apply flatMap_congr_mem; intro r hr
  rw [List.flatMap_map]; unfold colsOut
  apply flatMap_congr_mem; intro col hcol
  simp only [List.mem_range'] at hr hcol
  have : r * 9 + col < 81 := by omega
  simp only [G, this, dif_pos]
  exact cell_eq p c hw r col (by omega) (by omega)

theorem rowsOut_zero (p : Position) (c : Color) (pfm : Nat) : rowsOut p c 0 pfm 0 9 = [] := by
  have hc : ∀ r col, cellOut p c 0 pfm r col = [] := by
    intro r col; unfold cellOut allowedS; split
    · rfl
    · simp
  unfold rowsOut colsOut; simp [hc]

/-- **`add_pseudo_drops` refines `Position.dropMoves`**: the bytes the C
    function appends are exactly the spec's drop moves, in order. -/
theorem dropsC_spec (p : Position) (hw : ∀ i, p.hand p.side i < 256) :
    dropsC p p.side = p.dropMoves.map (moveBytes p) := by
  have hR : p.dropMoves.map (moveBytes p) = (List.finRange 81).flatMap (specCell p p.side) := by
    unfold Position.dropMoves specCell; rw [List.map_flatMap]
  rw [hR, ← rowsOut_spec p p.side hw]
  unfold dropsC; split
  · next h => rw [h, rowsOut_zero]
  · rfl

end Shogi.C.Proofs
