/-
  M5: loose but provable bound on the number of pseudo-legal moves, used to
  discharge the `h600` side condition of the legal-move refinement.  The
  measured maximum (591) is tight; this proves a generous bound of 7200,
  which is what `SHOGI_MAX_MOVES` is now set to.
-/
import Shogi.Rules
import Shogi.Basic
import Shogi.Position
import Shogi.Theorems

namespace Shogi
open Position

/-- Generic flatMap length bound (List.length_flatMap_le is not in core). -/
theorem length_flatMap_le {α β : Type} (f : α → List β) (l : List α) (n : Nat)
    (h : ∀ x, (f x).length ≤ n) : (l.flatMap f).length ≤ l.length * n := by
  induction l with
  | nil => simp [List.flatMap]
  | cons a l ih =>
    simp only [List.flatMap_cons, List.length_append, List.length_cons]
    have hn : (l.length + 1) * n = l.length * n + n := by simp [Nat.add_mul]
    have h1 := h a
    have h2 := ih
    omega

theorem ray_length_le (s : Square) (d : Int × Int) : (ray s d).length ≤ 8 := by
  have go_le : ∀ (n : Nat) (t : Square), (ray.go d n t).length ≤ n := by
    intro n
    induction n with
    | zero => intro t; simp [ray.go]
    | succ n ih =>
      intro t
      simp only [ray.go]
      cases h : t.offset d with
      | none => simp
      | some u =>
        have ih' := ih u
        simp only [List.length_cons]
        omega
  show (ray.go d 8 s).length ≤ 8
  exact go_le 8 s

/-- A slide yields a prefix of the ray, so at most 8 targets. -/
theorem slideTargets_length_le (p : Position) (s : Square) (d : Int × Int) :
    (p.slideTargets s d).length ≤ 8 := by
  have go_le : ∀ (l : List Square), (slideTargets.go p l).length ≤ l.length := by
    intro l
    induction l with
    | nil => simp [slideTargets.go]
    | cons t r ih =>
      simp only [slideTargets.go]
      split <;> simp_all
  have h := ray_length_le s d
  show (slideTargets.go p (ray s d)).length ≤ 8
  exact Nat.le_trans (go_le (ray s d)) h

/-- `stepOffsets` has at most 8 offsets (king is the worst case). -/
theorem stepOffsets_length_le (f : Int) (t : PieceType) : (stepOffsets f t).length ≤ 8 := by
  cases t <;> simp [stepOffsets] <;> omega

/-- `slideDirs` has at most 4 directions. -/
theorem slideDirs_length_le (f : Int) (t : PieceType) : (slideDirs f t).length ≤ 4 := by
  cases t <;> simp [slideDirs, diagonals, orthogonals] <;> omega

/-- Promotion choices are at most 2. -/
theorem promoChoices_length_le (c : Color) (t : PieceType) (src dst : Square) :
    (promoChoices c t src dst).length ≤ 2 := by
  unfold promoChoices
  split
  · simp
  · split
    · simp
    · simp

/-- Attack squares: at most 8 steps plus 4 slides × 8 squares. -/
theorem attackSquares_length_le (p : Position) (s : Square) (pc : Piece) :
    (p.attackSquares s pc).length ≤ 40 := by
  unfold Position.attackSquares
  simp only [List.length_append]
  have hst := stepOffsets_length_le pc.color.fwd pc.type
  have hsl := slideDirs_length_le pc.color.fwd pc.type
  have hstep : ((stepOffsets pc.color.fwd pc.type).filterMap s.offset).length ≤ 8 :=
    Nat.le_trans (List.length_filterMap_le _ _) hst
  have hslide : ((slideDirs pc.color.fwd pc.type).flatMap (p.slideTargets s)).length ≤ 32 := by
    have hflat : ((slideDirs pc.color.fwd pc.type).flatMap (p.slideTargets s)).length ≤
        (slideDirs pc.color.fwd pc.type).length * 8 := by
      apply length_flatMap_le
      intro d
      exact slideTargets_length_le p s d
    exact Nat.le_trans hflat (by omega)
  omega

/-- One piece contributes at most 80 pseudo-legal moves. -/
theorem boardMoves_length_le (p : Position) (s : Square) (pc : Piece) :
    (p.boardMoves s pc).length ≤ 80 := by
  unfold Position.boardMoves
  have hAtk := attackSquares_length_le p s pc
  have cell_le : ∀ d, (match p.pieceAt d with
      | some q => if q.color == pc.color || q.type == PieceType.king then []
                  else (promoChoices pc.color pc.type s d).map (Move.normal s d)
      | none => (promoChoices pc.color pc.type s d).map (Move.normal s d)).length ≤ 2 := by
    intro d
    cases h : p.pieceAt d with
    | none => simp [List.length_map]; exact promoChoices_length_le pc.color pc.type s d
    | some q =>
      by_cases hb : q.color == pc.color || q.type == PieceType.king
      · simp [hb]
      · simp [hb, List.length_map]; exact promoChoices_length_le pc.color pc.type s d
  have h1 := length_flatMap_le _ (p.attackSquares s pc) 2 cell_le
  have h2 := attackSquares_length_le p s pc
  apply Nat.le_trans h1
  apply Nat.le_trans (Nat.mul_le_mul h2 (Nat.le_refl 2))
  decide

/-- One board move cell contributes at most 80 moves. -/
theorem positionBoardCell_length_le (p : Position) (s : Square) :
    (match p.pieceAt s with
    | some pc => if pc.color == p.side then p.boardMoves s pc else []
    | none => []).length ≤ 80 := by
  cases h1 : p.pieceAt s with
  | none => simp
  | some pc =>
    by_cases h2 : pc.color == p.side
    · simp [h2]; exact boardMoves_length_le p s pc
    · simp [h2]

/-- Drop moves: at most 81 squares × 7 piece types. -/
theorem dropMoves_length_le (p : Position) : (p.dropMoves).length ≤ 567 := by
  unfold Position.dropMoves
  have h81 : (List.finRange 81).length = 81 := by simp [List.length_finRange]
  have cell_le : ∀ d, ((List.finRange 7).filterMap fun i =>
        let t := PieceType.ofHandIndex i
        if p.hand p.side i > 0 && p.dropAllowed p.side t d then some (Move.drop t d) else none).length ≤ 7 := by
    intro d
    exact Nat.le_trans (List.length_filterMap_le _ _) (by simp [List.length_finRange])
  exact Nat.le_trans (length_flatMap_le _ (List.finRange 81) 7 cell_le) (by omega)

/-- Board moves over all 81 squares: at most 81 × 80. -/
theorem positionBoardMoves_length_le (p : Position) :
    ((List.finRange 81).flatMap fun s =>
      match p.pieceAt s with
      | some pc => if pc.color == p.side then p.boardMoves s pc else []
      | none => []).length ≤ 6480 := by
  have h81 : (List.finRange 81).length = 81 := by simp [List.length_finRange]
  exact Nat.le_trans (length_flatMap_le _ (List.finRange 81) 80 (fun s => positionBoardCell_length_le p s)) (by omega)

/-- **Pseudo-legal move count bound.** -/
theorem pseudoMoves_le_7200 (p : Position) : p.pseudoMoves.length ≤ 7200 := by
  have h1 := positionBoardMoves_length_le p
  have h2 := dropMoves_length_le p
  unfold Position.pseudoMoves
  rw [List.length_append]
  exact Nat.le_trans (Nat.add_le_add h1 h2) (by omega)

end Shogi
