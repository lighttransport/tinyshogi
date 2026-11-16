/-
  T8: geometry for the fast path: a move the C allows "along the pin" stays on
  the pin ray.
-/
import Shogi.C.Proofs.FastPath

namespace Shogi.C.Proofs
open MiniC Shogi Shogi.C Shogi.Tables

set_option maxRecDepth 100000 in
theorem sameKingRay_ray : ∀ k : Fin 81, ∀ r : Fin 8,
    (ray k (rdir r.val)).all (fun s => (List.finRange 81).all (fun d =>
      !sameKingRay k s d || (ray k (rdir r.val)).contains d)) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Continuing a ray from its `i`-th square is its tail. -/
theorem ray_suffix_all : ∀ k : Fin 81, ∀ r : Fin 8,
    ((List.range (ray k (rdir r.val)).length).all fun i =>
      ray ((ray k (rdir r.val)).getD i k) (rdir r.val) == (ray k (rdir r.val)).drop (i + 1)) = true := by
  decide +kernel

def allSteps : List (Int × Int) :=
  [(-1, -1), (-1, 0), (-1, 1), (0, -1), (0, 1), (1, -1), (1, 0), (1, 1), (-2, -1), (-2, 1), (2, -1), (2, 1)]

theorem stepOffsets_sub (c : Color) (t : PieceType) : ∀ o ∈ stepOffsets c.fwd t, o ∈ allSteps := by
  cases c <;> cases t <;> decide

set_option maxRecDepth 100000 in
/-- A single step never skips a square of a ray. -/
theorem step_adj_all : ∀ k : Fin 81, ∀ r : Fin 8,
    ((List.range (ray k (rdir r.val)).length).all fun i => (List.range (ray k (rdir r.val)).length).all fun j =>
      decide (j ≤ i + 1) || allSteps.all fun o =>
        ((ray k (rdir r.val)).getD i k).offset o != some ((ray k (rdir r.val)).getD j k)) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- A ray from a square of `ray k d` in another direction never meets the part
    of `ray k d` beyond that square. -/
theorem offline_all : ∀ k : Fin 81, ∀ r : Fin 8,
    ((List.range (ray k (rdir r.val)).length).all fun i => (List.finRange 8).all fun r' =>
      r' == r || (ray ((ray k (rdir r.val)).getD i k) (rdir r'.val)).all fun x =>
        !((ray k (rdir r.val)).drop (i + 1)).contains x) = true := by
  decide +kernel

end Shogi.C.Proofs
