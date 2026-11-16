/-
  T8: `king_safety_prepare`, part 3 — the record's `in_check` byte is the
  spec's `Position.inCheck`.
-/
import Shogi.C.Proofs.KS2

namespace Shogi.C.Proofs
open MiniC Shogi Shogi.C Shogi.Tables

theorem opp_of_ne {x c : Color} (h : x ≠ c) : x = c.opp := by cases x <;> cases c <;> simp_all [Color.opp]

/-- With no own piece seen yet, the scan reports check iff the first occupied
    square holds an attacker slider for this ray. -/
theorem kres_chk (p : Position) (c : Color) (mk : Nat) :
    ∀ L : List Square, (kres p c mk L none).1 =
      match Position.firstOcc p L with
      | some s => match p.pieceAt s with
        | some pc => pc.color == c.opp && maskHas mk pc.type
        | none => false
      | none => false := by
  have hown : ∀ L (o : Square), (kres p c mk L (some o)).1 = false := by
    intro L; induction L with
    | nil => intro o; rfl
    | cons x r ih =>
      intro o; simp only [kres]
      cases hx : p.pieceAt x with
      | none => exact ih o
      | some q => by_cases h : q.color = c <;> simp [h]
  intro L; induction L with
  | nil => rfl
  | cons x r ih =>
    by_cases hn : p.pieceAt x = none
    · simp [kres, Position.firstOcc, Position.isEmpty, hn, ih]
    · obtain ⟨q, hx⟩ : ∃ q, p.pieceAt x = some q := Option.ne_none_iff_exists'.mp hn
      simp only [kres, Position.firstOcc, Position.isEmpty, hx, Option.isNone_some, Bool.false_eq_true, ite_false]
      by_cases h : q.color = c
      · simp only [h, if_true, hown]; cases c <;> rfl
      · simp only [h, if_false]
        have := opp_of_ne h
        simp only [this, maskHas, shl_eq]
        by_cases h' : mk &&& 2 ^ q.type.code = 0 <;> simp [h']

theorem applyK_2 (S : List UInt8) (x : Bool × Option Square) (hS : 2 < S.length) :
    (applyK S x).getD 2 0 = if x.1 then 1 else S.getD 2 0 := by
  obtain ⟨chk, pin⟩ := x
  cases pin <;> cases chk <;> simp [applyK, List.getD_eq_getElem?_getD, List.getElem?_set, hS]
  all_goals (rw [List.getElem_set_ne (by omega)]; try simp)

theorem ksAll_2 (p : Position) (c a : Color) (t : Square) (S : List UInt8) (hS : 2 < S.length) :
    ∀ r, (ksAll p c a t S r).getD 2 0 =
      if (List.range r).any (fun r' => (kres p c (rayMask a (rdir r')) (ray t (rdir r')) none).1) then 1
      else S.getD 2 0 := by
  intro r; induction r with
  | zero => simp [ksAll]
  | succ r ih =>
    simp only [ksAll]
    rw [applyK_2 _ _ (by rw [kAll_len]; exact hS), ih, List.range_succ, List.any_append]
    by_cases h1 : (kres p c (rayMask a (rdir r)) (ray t (rdir r)) none).1 = true
    · simp [h1]
    · simp [h1]

theorem kres_ray (p : Position) (c : Color) (t : Square) (r : Nat) :
    (kres p c (rayMask c.opp (rdir r)) (ray t (rdir r)) none).1 = rayHitFrom p c.opp t r 0 := by
  rw [kres_chk]; unfold rayHitFrom; rfl

/-- **The `in_check` byte of `king_safety_prepare`'s record is `Position.inCheck`.** -/
theorem ksRec_inCheck (p : Position) (c : Color) :
    (ksRec p c).getD 2 0 = if p.inCheck c then 1 else 0 := by
  unfold ksRec Position.inCheck
  cases hk : p.kingSquare c with
  | none => simp [List.getD_eq_getElem?_getD]
  | some k =>
    simp only
    rw [ksAll_2 _ _ _ _ _ (by simp [ksInit])]
    have hi : (ksInit p c k).getD 2 0 = if stepAttacked p k c.opp then 1 else 0 := by
      simp [ksInit, List.getD_eq_getElem?_getD, List.getElem?_set]
    rw [hi]
    simp only [Position.attacked_eq, ← stepAttacked_eqS, ← raysFrom_zero]
    have hr : ((List.range 8).any fun r' => (kres p c (rayMask c.opp (rdir r')) (ray k (rdir r')) none).1) =
        raysFrom p c.opp k 0 := by
      unfold raysFrom; simp only [List.drop_zero]; congr 1; funext r'; exact kres_ray p c k r'
    simp only [hr]
    cases stepAttacked p k c.opp <;> cases raysFrom p c.opp k 0 <;> rfl

end Shogi.C.Proofs
