/-
  Target-centred form of the attack relation (what `square_attacked` scans):
  `attacked_eq` splits the spec's attacker-centred `attacked` into single-step
  attacks and `rayAttacked` (first occupied square on each ray from the
  target). Geometry and masks are kernel-checked (`geom_all`, `mask_slide`).
-/
import Shogi.TablesSpec
namespace Shogi.Position
open Shogi Shogi.Tables

/-- First occupied square of a list. -/
def firstOcc (p : Position) : List Square → Option Square
  | [] => none
  | x :: r => if p.isEmpty x then firstOcc p r else some x

/-- `t` is in `slideTargets.go l` iff it is in `l` and everything before it is empty. -/
theorem mem_slide_go (p : Position) : ∀ (l : List Square) (t : Square), l.Nodup →
    (t ∈ slideTargets.go p l ↔ ∃ i, ∃ h : i < l.length, l[i] = t ∧ ∀ j (hj : j < i), p.isEmpty (l[j]'(by omega)) = true) := by
  intro l
  induction l with
  | nil => intro t _; simp [slideTargets.go]
  | cons x r ih =>
    intro t hnd
    simp only [List.nodup_cons] at hnd
    simp only [slideTargets.go]
    by_cases hx : p.isEmpty x = true
    · simp only [hx, ite_true, List.mem_cons]
      rw [ih t hnd.2]
      constructor
      · rintro (rfl | ⟨i, hi, hit, hpre⟩)
        · exact ⟨0, by simp, rfl, fun j hj => absurd hj (by omega)⟩
        · refine ⟨i + 1, by simp; omega, by simpa using hit, ?_⟩
          intro j hj
          cases j with
          | zero => simpa using hx
          | succ j => simpa using hpre j (by omega)
      · rintro ⟨i, hi, hit, hpre⟩
        cases i with
        | zero => left; simpa using hit.symm
        | succ i =>
          right
          refine ⟨i, by simp at hi; omega, by simpa using hit, ?_⟩
          intro j hj
          simpa using hpre (j + 1) (by omega)
    · simp only [hx, Bool.false_eq_true, ite_false, List.mem_singleton]
      constructor
      · rintro rfl; exact ⟨0, by simp, rfl, fun j hj => absurd hj (by omega)⟩
      · rintro ⟨i, hi, hit, hpre⟩
        cases i with
        | zero => simpa using hit.symm
        | succ i => exact absurd (hpre 0 (by omega)) (by simpa using hx)

theorem firstOcc_eq (p : Position) : ∀ (l : List Square) (s : Square), l.Nodup →
    (firstOcc p l = some s ↔ ∃ i, ∃ h : i < l.length, l[i] = s ∧ p.isEmpty s = false ∧
      ∀ j (hj : j < i), p.isEmpty (l[j]'(by omega)) = true) := by
  intro l
  induction l with
  | nil => intro s _; simp [firstOcc]
  | cons x r ih =>
    intro s hnd
    simp only [List.nodup_cons] at hnd
    simp only [firstOcc]
    by_cases hx : p.isEmpty x = true
    · simp only [hx, ite_true]
      rw [ih s hnd.2]
      constructor
      · rintro ⟨i, hi, his, hne, hpre⟩
        refine ⟨i + 1, by simp; omega, by simpa using his, hne, ?_⟩
        intro j hj
        cases j with
        | zero => simpa using hx
        | succ j => simpa using hpre j (by omega)
      · rintro ⟨i, hi, his, hne, hpre⟩
        cases i with
        | zero => simp at his; subst his; rw [hx] at hne; cases hne
        | succ i =>
          refine ⟨i, by simp at hi; omega, by simpa using his, hne, ?_⟩
          intro j hj
          simpa using hpre (j + 1) (by omega)
    · simp only [hx, Bool.false_eq_true, ite_false, Option.some.injEq]
      constructor
      · rintro rfl
        exact ⟨0, by simp, rfl, by simpa using hx, fun j hj => absurd hj (by omega)⟩
      · rintro ⟨i, hi, his, hne, hpre⟩
        cases i with
        | zero => simpa using his
        | succ i => exact absurd (hpre 0 (by omega)) (by simpa using hx)

end Shogi.Position

namespace Shogi.Tables
open Shogi

def negD (d : Int × Int) : Int × Int := (-d.1, -d.2)

def geomOK (s t : Square) (d : Int × Int) : Bool :=
  let L1 := ray s d
  let L2 := ray t (negD d)
  let i := L1.idxOf t
  !(L1.contains t) || (L2.take (i + 1) == (L1.take i).reverse ++ [s])


theorem geom_all : ∀ s t : Fin 81, rayDirs.all (geomOK s t) = true := by decide +kernel

theorem rays_nodup : ∀ s : Fin 81, rayDirs.all (fun d => (ray s d).Nodup) = true := by decide +kernel

theorem mask_slide (c : Color) : ∀ d ∈ rayDirs, ∀ ty ∈ allTypes,
    maskHas (rayMask c d) ty = (slideDirs c.fwd ty).contains (negD d) := by
  cases c <;> decide

theorem negD_mem : ∀ d ∈ rayDirs, negD d ∈ rayDirs := by decide
theorem negD_negD (d : Int × Int) : negD (negD d) = d := by simp [negD]

end Shogi.Tables

namespace Shogi.Position
open Shogi Shogi.Tables

/-- Target-centred slider attacks, the way `square_attacked` scans: on each
    ray from `t`, the first occupied square holds a slider of `c` that moves
    along that line towards `t`. -/
def rayAttacked (p : Position) (t : Square) (c : Color) : Bool :=
  rayDirs.any fun d =>
    match firstOcc p (ray t d) with
    | some s => match p.pieceAt s with
      | some pc => pc.color == c && maskHas (rayMask c d) pc.type
      | none => false
    | none => false

/-- Attacker-centred slider attacks, as in the spec's `attackSquares`. -/
def slideAttacked (p : Position) (t : Square) (c : Color) : Bool :=
  (List.finRange 81).any fun s =>
    match p.pieceAt s with
    | some pc => pc.color == c && (slideDirs c.fwd pc.type).any fun d => (p.slideTargets s d).contains t
    | none => false

theorem slideDirs_sub (c : Color) (ty : PieceType) : ∀ d ∈ slideDirs c.fwd ty, d ∈ rayDirs := by
  cases c <;> cases ty <;> decide

theorem take_eq_facts {L R : List Square} {i : Nat} {s : Square} (hR : R.length = i)
    (h : L.take (i + 1) = R ++ [s]) :
    ∃ hi : i < L.length, L[i] = s ∧ ∀ j (hj : j < i), L[j]'(by omega) ∈ R := by
  have hlen : (L.take (i + 1)).length = i + 1 := by rw [h]; simp [hR]
  have hi : i < L.length := by simp at hlen; omega
  refine ⟨hi, ?_, ?_⟩
  · have := congrArg (fun l => l[i]?) h
    simp only [List.getElem?_take, show i < i + 1 by omega, ite_true, List.getElem?_eq_getElem hi] at this
    rw [List.getElem?_append_right (by omega), hR] at this
    simpa using this
  · intro j hj
    have := congrArg (fun l => l[j]?) h
    simp only [List.getElem?_take, show j < i + 1 by omega, ite_true,
      List.getElem?_eq_getElem (show j < L.length by omega)] at this
    rw [List.getElem?_append_left (by omega)] at this
    rw [List.getElem?_eq_getElem (by omega)] at this
    simp only [Option.some.injEq] at this
    rw [this]; exact List.getElem_mem _

/-- The geometric core: if `t` is the `i`-th square from `s` along `d`, then
    `s` is the `i`-th square from `t` along `-d`, and the squares before it
    are those before `t`, reversed. -/
theorem ray_back {s t : Square} {d : Int × Int} (hd : d ∈ rayDirs) {i : Nat}
    (hi : i < (ray s d).length) (hit : (ray s d)[i] = t) :
    ∃ hi2 : i < (ray t (negD d)).length, (ray t (negD d))[i] = s ∧
      ∀ j (hj : j < i), (ray t (negD d))[j]'(by omega) ∈ (ray s d).take i := by
  have hg := List.all_eq_true.mp (geom_all s t) d hd
  have hnd := List.all_eq_true.mp (rays_nodup s) d hd
  simp only [geomOK, Bool.or_eq_true, Bool.not_eq_true', beq_iff_eq] at hg
  have hmem : (ray s d).contains t = true := by
    rw [List.contains_iff_mem]; rw [← hit]; exact List.getElem_mem _
  rcases hg with hg | hg
  · rw [hmem] at hg; cases hg
  · have hidx : (ray s d).idxOf t = i := by
      rw [← hit]; exact List.Nodup.idxOf_getElem (by simpa using hnd) i hi
    rw [hidx] at hg
    obtain ⟨hi2, h1, h2⟩ := take_eq_facts (R := ((ray s d).take i).reverse) (by simp; omega) hg
    exact ⟨hi2, h1, fun j hj => List.mem_reverse.mp (h2 j hj)⟩

end Shogi.Position

namespace Shogi.Position
open Shogi Shogi.Tables

theorem ray_nodup (s : Square) {d : Int × Int} (hd : d ∈ rayDirs) : (ray s d).Nodup := by
  have := List.all_eq_true.mp (rays_nodup s) d hd
  simpa using this

theorem mem_take_empty {p : Position} {L : List Square} {i : Nat} (hi : i ≤ L.length)
    (hpre : ∀ j (hj : j < i), p.isEmpty (L[j]'(by omega)) = true) :
    ∀ x ∈ L.take i, p.isEmpty x = true := by
  intro x hx
  obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hx
  simp only [List.getElem_take]
  exact hpre k (by simp at hk; omega)

theorem allTypes_mem (ty : PieceType) : ty ∈ allTypes := by cases ty <;> decide

/-- **Slider attacks, both ways.** -/
theorem slide_eq_ray (p : Position) (t : Square) (c : Color) :
    slideAttacked p t c = rayAttacked p t c := by
  apply Bool.eq_iff_iff.mpr
  simp only [slideAttacked, rayAttacked, List.any_eq_true]
  constructor
  · rintro ⟨s, _, hs⟩
    split at hs
    · rename_i pc hpc
      simp only [Bool.and_eq_true, beq_iff_eq, List.any_eq_true, List.contains_iff_mem] at hs
      obtain ⟨hcol, d, hd, htd⟩ := hs
      have hdr := slideDirs_sub c pc.type d hd
      obtain ⟨i, hi, hit, hpre⟩ := (mem_slide_go p (ray s d) t (ray_nodup s hdr)).mp htd
      obtain ⟨hi2, hback, hbetween⟩ := ray_back hdr hi hit
      refine ⟨negD d, negD_mem d hdr, ?_⟩
      have hocc : firstOcc p (ray t (negD d)) = some s := by
        rw [firstOcc_eq p _ s (ray_nodup t (negD_mem d hdr))]
        refine ⟨i, hi2, hback, ?_, ?_⟩
        · simp [isEmpty, hpc]
        · intro j hj
          exact mem_take_empty (by omega) hpre _ (hbetween j hj)
      rw [hocc]
      simp only [hpc, Bool.and_eq_true, beq_iff_eq, hcol, true_and]
      rw [mask_slide c (negD d) (negD_mem d hdr) pc.type (allTypes_mem _), negD_negD]
      simpa [List.contains_iff_mem] using hd
    · simp at hs
  · rintro ⟨d, hd, hh⟩
    split at hh
    · rename_i s hocc
      split at hh
      · rename_i pc hpc
        simp only [Bool.and_eq_true, beq_iff_eq] at hh
        obtain ⟨hcol, hmask⟩ := hh
        rw [mask_slide c d hd pc.type (allTypes_mem _)] at hmask
        obtain ⟨i, hi, his, _, hpre⟩ := (firstOcc_eq p _ s (ray_nodup t hd)).mp hocc
        obtain ⟨hi2, hback, hbetween⟩ := ray_back hd hi his
        refine ⟨s, List.mem_finRange s, ?_⟩
        rw [hpc]
        simp only [Bool.and_eq_true, beq_iff_eq, hcol, true_and, List.any_eq_true,
          List.contains_iff_mem]
        refine ⟨negD d, by simpa [List.contains_iff_mem] using hmask, ?_⟩
        exact (mem_slide_go p _ t (ray_nodup s (negD_mem d hd))).mpr
          ⟨i, hi2, hback, fun j hj => mem_take_empty (by omega) hpre _ (hbetween j hj)⟩
      · simp at hh
    · simp at hh

end Shogi.Position

namespace Shogi.Position
open Shogi Shogi.Tables

/-- Single-step attacks (as in `Shogi.C.Proofs.stepAttacked`). -/
def stepAttackedS (p : Position) (t : Square) (c : Color) : Bool :=
  (List.finRange 81).any fun s =>
    match p.pieceAt s with
    | some pc => pc.color == c && ((stepOffsets c.fwd pc.type).filterMap (Square.offset s)).contains t
    | none => false

theorem any_or' {α} (l : List α) (a b : α → Bool) :
    (l.any fun x => a x || b x) = (l.any a || l.any b) := by
  induction l with
  | nil => rfl
  | cons x l ih =>
    simp only [List.any_cons, ih]
    cases a x <;> cases b x <;> simp

/-- **The spec's attack relation, target-centred**: a square is attacked iff
    a piece attacks it by one step or the first occupied square on some ray
    holds a matching slider. This is the decomposition `square_attacked`
    implements. -/
theorem attacked_eq (p : Position) (t : Square) (c : Color) :
    p.attacked t c = (stepAttackedS p t c || rayAttacked p t c) := by
  rw [← slide_eq_ray]
  unfold attacked stepAttackedS slideAttacked
  rw [← any_or']
  congr 1
  funext s
  cases p.pieceAt s with
  | none => rfl
  | some pc =>
    simp only [attackSquares, List.contains_append, Bool.and_or_distrib_left]
    by_cases hcol : pc.color = c
    · subst hcol
      congr 1
      congr 1
      apply Bool.eq_iff_iff.mpr
      simp [List.contains_iff_mem, List.mem_flatMap, List.any_eq_true]
    · have : (pc.color == c) = false := by simpa using hcol
      simp [this]

end Shogi.Position
