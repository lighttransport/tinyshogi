/-
  Zobrist hashing at the spec level (R4a).

  `position_hash` in `src/shogi.c` maintains a 64-bit hash incrementally.
  The spec hash is a pure function of the position, parametric in the key
  arrays: the key VALUES are never assumed (collisions stay a hypothesis).
  This file sets up the spec hash and proves it decomposes into board / hand /
  side parts, the form used by the C's incremental update rule.
-/
import Shogi.Rules
import Shogi.SfenTheorems

namespace Shogi

/-- The Zobrist key arrays, indexed as in the C globals. Keys are 64-bit
    values; we keep them as `Nat` because the proofs never use their size. -/
structure Keys where
  board : Fin 81 → Fin 32 → Nat
  hand  : Fin 2 → Fin 7 → Fin 19 → Nat
  side  : Nat

namespace Position

/-- Board contribution to `position_hash`. -/
def zobristBoard (K : Keys) (p : Position) : Nat :=
  (List.finRange 81).foldl (fun acc s =>
    match p.pieceAt s with
    | none => acc
    | some pc => acc ^^^ K.board s ⟨pc.code, by
        have ht : pc.type.code ≤ 14 := by cases pc.type <;> decide
        have hi : pc.color.idx ≤ 1 := by cases pc.color <;> decide
        simp [Piece.code]
        omega⟩) 0

/-- Hand contribution (counts clamped at 18, as in the C). -/
def zobristHand (K : Keys) (p : Position) : Nat :=
  (List.finRange 2).foldl (fun acc c =>
    (List.finRange 7).foldl (fun acc i =>
      let col := if c.val = 0 then .black else .white
      let n := p.hand col i
      let k := if n > 18 then 18 else n
      acc ^^^ K.hand c i ⟨k, by
        dsimp [k]
        by_cases h : n > 18
        · simp [h]
        · simp [h]
          omega⟩) acc) 0

/-- Full recomputation of `position_hash`. -/
def zobrist (K : Keys) (p : Position) : Nat :=
  let h := zobristBoard K p ^^^ zobristHand K p
  if p.side == .white then h ^^^ K.side else h

end Position
end Shogi

namespace XorList

/-- XOR of a list of keys (left fold). -/
def xorList : List Nat → Nat
  | [] => 0
  | x :: xs => x ^^^ xorList xs

theorem xorList_append (a b : List Nat) : xorList (a ++ b) = xorList a ^^^ xorList b := by
  induction a with
  | nil => simp [xorList]
  | cons x xs ih =>
      simp [xorList, ih, Nat.xor_assoc]

theorem xorList_self (a : List Nat) (x : Nat) : xorList (x :: a ++ [x]) = xorList a := by
  rw [xorList_append]
  simp only [xorList, Nat.xor_zero]
  rw [Nat.xor_comm x (xorList a), Nat.xor_assoc, Nat.xor_self, Nat.xor_zero]

theorem foldl_acc (f : α → Nat) (l : List α) (acc : Nat) :
    l.foldl (fun acc x => acc ^^^ f x) acc = acc ^^^ xorList (l.map f) := by
  induction l generalizing acc with
  | nil => simp [xorList, Nat.xor_zero]
  | cons x xs ih =>
      rw [List.foldl_cons]
      rw [ih]
      simp [xorList, List.map_cons, Nat.xor_assoc]

theorem foldl_eq_xorList (f : α → Nat) (l : List α) :
    l.foldl (fun acc x => acc ^^^ f x) 0 = xorList (l.map f) := by
  rw [foldl_acc]
  simp [Nat.xor_zero]

end XorList
