/-
  Bridge from the fid 18 ray-walk predicate to the spec slideTargets.
-/
import Shogi.C.Proofs.Fid18Bridge
open Shogi Shogi.C.Proofs
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000 in
theorem sq_eq_of_row_col : ∀ q r : Square,
    (q.row : Int) = r.row → (q.col : Int) = r.col → q = r := by
  decide +kernel

theorem walkErr_eq_rayWalk_aux (p : Position) (s : Square) (r : Fin 8) :
  ∀ (d ti j : Nat) (hti : ti < (ray s (rdir r.val)).length) (hjl : j < (ray s (rdir r.val)).length),
    j + d = ti →
    walkErr p (rdir r.val).1 (rdir r.val).2 ((ray s (rdir r.val))[ti]'hti) d
      ((((ray s (rdir r.val))[j]'hjl).row : Int)) ((((ray s (rdir r.val))[j]'hjl).col : Int)) =
      rayWalk p (ray s (rdir r.val)) ti d j := by
  intro d
  induction d with
  | zero =>
    intro ti j hti hjl hjd
    have hj : j = ti := by omega
    subst j
    simp [walkErr, rayWalk]
  | succ d ih =>
    intro ti j hti hjl hjd
    let rs := (rdir r.val).1
    let cs := (rdir r.val).2
    let l := ray s (rdir r.val)
    have hlen8 : l.length ≤ 8 := by simpa [l] using Shogi.C.Proofs.ray_length_le s (rdir r.val)
    have hti' : ti < l.length := by simpa [l] using hti
    have hjl' : j < l.length := by simpa [l] using hjl
    have hjti : j < ti := by omega
    have hneq : (l[j]'hjl') ≠ (l[ti]'hti') := by
      intro heq
      have hidx := (Shogi.C.Proofs.ray_nodup_finite s r).getElem_inj.mp heq
      omega
    have hcur_ne : ¬ ((((l[j]'hjl').row : Int) = ((l[ti]'hti').row : Int)) ∧
                      (((l[j]'hjl').col : Int) = ((l[ti]'hti').col : Int))) := by
      rintro ⟨hr, hc⟩
      exact hneq (sq_eq_of_row_col (l[j]'hjl') (l[ti]'hti') hr hc)
    have hmk : Square.mk? (((l[j]'hjl').row : Int)) (((l[j]'hjl').col : Int)) = some (l[j]'hjl') :=
      sq_mk_self _
    by_cases hem : p.isEmpty (l[j]'hjl') = true
    · have hj1 : j + 1 < l.length := by omega
      have hj1' : j + 1 < (ray s (rdir r.val)).length := by simpa [l] using hj1
      have hrow := ray_next_row s r ⟨j, by omega⟩ hjl' hj1'
      have hcol := ray_next_col s r ⟨j, by omega⟩ hjl' hj1'
      have ihs := ih ti (j+1) hti hj1' (by omega)
      rw [walkErr]
      rw [if_neg hcur_ne]
      rw [hmk]
      simp only [hem, ↓reduceDIte]
      rw [rayWalk]
      rw [dif_pos hjl]
      rw [if_neg (by omega : ¬ j = ti)]
      have hem' : p.isEmpty ((ray s (rdir r.val))[j]'hjl) = true := by simpa [l] using hem
      rw [if_pos hem']
      have hrow' := ray_next_row s r ⟨j, by omega⟩ hjl (by omega)
      have hcol' := ray_next_col s r ⟨j, by omega⟩ hjl (by omega)
      rw [← hrow', ← hcol']
      simpa [l] using ihs

    · have hbf : p.isEmpty (l[j]'hjl') = false := by
        cases hp : p.isEmpty (l[j]'hjl') <;> simp_all
      have hcur_ne' := hcur_ne
      have hmk' := hmk
      have hbf' := hbf
      dsimp [l] at hcur_ne' hmk' hbf'
      simp [walkErr, rayWalk, l, hcur_ne', hmk', hbf']
      exact Or.inr (by omega)

set_option maxRecDepth 100000 in
theorem ray_head_row : ∀ (s : Square) (r : Fin 8) (h : 0 < (ray s (rdir r.val)).length),
    (((ray s (rdir r.val))[0]'h).row : Int) = (s.row : Int) + (rdir r.val).1 := by decide +kernel
set_option maxRecDepth 100000 in
theorem ray_head_col : ∀ (s : Square) (r : Fin 8) (h : 0 < (ray s (rdir r.val)).length),
    (((ray s (rdir r.val))[0]'h).col : Int) = (s.col : Int) + (rdir r.val).2 := by decide +kernel

theorem walkErr_slide (p : Position) (s : Square) (r : Fin 8) (ti : Nat)
    (hti : ti < (ray s (rdir r.val)).length) :
    walkErr p (rdir r.val).1 (rdir r.val).2 ((ray s (rdir r.val))[ti]'hti) ti
      ((s.row : Int) + (rdir r.val).1) ((s.col : Int) + (rdir r.val).2) = false ↔
      ((ray s (rdir r.val))[ti]'hti) ∈ p.slideTargets s (rdir r.val) := by
  let l := ray s (rdir r.val)
  have haux := walkErr_eq_rayWalk_aux p s r ti ti 0 hti (by omega) (by omega)
  have hclear := rayWalk_clear p l ti (by simpa [l] using hti) ti 0
    (by simpa [l] using (Nat.lt_of_le_of_lt (Nat.zero_le ti) hti)) (by omega)
  have hslide := Shogi.Position.mem_slide_go_at p l ti
    (Shogi.C.Proofs.ray_nodup_finite s r) (by simpa [l] using hti)
  dsimp [l] at haux hclear hslide
  have hheadrow := ray_head_row s r (Nat.lt_of_le_of_lt (Nat.zero_le ti) hti)
  have hheadcol := ray_head_col s r (Nat.lt_of_le_of_lt (Nat.zero_le ti) hti)
  rw [← hheadrow, ← hheadcol]
  rw [haux]
  rw [hclear]
  rw [Position.slideTargets]
  rw [hslide]
  constructor
  · intro h j hj hjl
    exact h j hj hjl (Nat.zero_le j) (by omega)
  · intro h k hk hkl _ _
    exact h k hk hkl
