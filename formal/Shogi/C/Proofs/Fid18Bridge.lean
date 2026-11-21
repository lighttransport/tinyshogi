import Shogi.C.Proofs.RayGeom
open Shogi Shogi.C.Proofs
set_option maxHeartbeats 4000000
namespace Shogi.C.Proofs

def rayWalk (p : Position) (l : List Square) (t : Nat) : Nat → Nat → Bool
  | 0, _ => false
  | d+1, j =>
      if h : j < l.length then
        if j = t then false
        else if p.isEmpty (l[j]'h) then rayWalk p l t d (j + 1) else true
      else true

theorem rayWalk_clear (p : Position) (l : List Square) (t : Nat) (htlen : t < l.length) :
    ∀ d j (hjlen : j < l.length), j + d = t →
      (rayWalk p l t d j = false ↔
        ∀ k (hk : k < t) (hkl : k < l.length), j ≤ k → k < j + d → p.isEmpty (l[k]'hkl) = true) := by
  intro d
  induction d with
  | zero =>
    intro j hjlen hj
    simp [rayWalk]
    intro k hk hkl hjk hkj
    omega
  | succ d ih =>
    intro j hjlen hj
    by_cases hjl : j < l.length
    · rw [rayWalk]
      simp only [hjl, ↓reduceDIte]
      by_cases hjt : j = t
      · subst j
        exfalso
        omega
      · simp [hjt]
        by_cases hem : p.isEmpty (l[j]'hjl) = true
        · simp [hem]
          have hlen' : j + 1 < l.length := by omega
          have hj' : j + 1 + d = t := by omega
          have ihs := ih (j+1) hlen' hj'
          rw [ihs]
          constructor
          · intro h k hk hkl hjk hkj
            by_cases hkj0 : k = j
            · subst k; exact hem
            · exact h k hk hkl (by omega) (by omega)
          · intro h k hk hkl hjk hkj
            exact h k hk hkl (by omega) (by omega)
        · have hjlt : j < t := by omega
          simp [hem]
          refine ⟨j, hjlt, by omega, by omega, ?_⟩
          cases hbj : p.isEmpty (l[j]'hjl) <;> simp_all
    · have : j < l.length := hjlen
      contradiction

end Shogi.C.Proofs

namespace Shogi.Position
theorem mem_slide_go_at (p : Position) (l : List Square) (ti : Nat) (hnd : l.Nodup)
    (htl : ti < l.length) :
    l[ti]'htl ∈ slideTargets.go p l ↔ ∀ j (hj : j < ti) (hjl : j < l.length), p.isEmpty (l[j]'hjl) = true := by
  rw [mem_slide_go p l (l[ti]'htl) hnd]
  constructor
  · rintro ⟨i, hi, hit, hpre⟩
    have heq : i = ti := (hnd.getElem_inj).mp hit
    subst i
    intro j hj hjl
    exact hpre j hj
  · intro h
    refine ⟨ti, htl, rfl, ?_⟩
    intro j hj
    exact h j hj (by omega)

end Shogi.Position

set_option maxRecDepth 100000 in
theorem sq_mk_self : ∀ q : Square, Square.mk? (q.row : Int) (q.col : Int) = some q := by decide +kernel
set_option maxRecDepth 100000 in
theorem ray_next_finite : ∀ (s : Square) (r : Fin 8) (j : Fin 8)
    (hj : j.val < (ray s (rdir r.val)).length)
    (hj1 : j.val + 1 < (ray s (rdir r.val)).length),
    Square.mk? (((ray s (rdir r.val))[j.val]'hj).row + (rdir r.val).1)
               (((ray s (rdir r.val))[j.val]'hj).col + (rdir r.val).2) =
      some ((ray s (rdir r.val))[j.val+1]'hj1) := by decide +kernel
set_option maxRecDepth 100000 in
theorem ray_next_row : ∀ (s : Square) (r : Fin 8) (j : Fin 8)
    (hj : j.val < (ray s (rdir r.val)).length)
    (hj1 : j.val + 1 < (ray s (rdir r.val)).length),
    (((ray s (rdir r.val))[j.val+1]'hj1).row : Int) =
      (((ray s (rdir r.val))[j.val]'hj).row : Int) + (rdir r.val).1 := by decide +kernel
set_option maxRecDepth 100000 in
theorem ray_next_col : ∀ (s : Square) (r : Fin 8) (j : Fin 8)
    (hj : j.val < (ray s (rdir r.val)).length)
    (hj1 : j.val + 1 < (ray s (rdir r.val)).length),
    (((ray s (rdir r.val))[j.val+1]'hj1).col : Int) =
      (((ray s (rdir r.val))[j.val]'hj).col : Int) + (rdir r.val).2 := by decide +kernel
