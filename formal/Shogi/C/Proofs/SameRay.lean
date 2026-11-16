/-
  T8: `same_king_ray` refines a Lean function: a pinned piece moving from
  `from` to `to` stays on the king's ray, on the same side.
-/
import Shogi.C.Proofs.KS3

namespace Shogi.C.Proofs
open MiniC Shogi Shogi.C

def iabs (z : Int) : Int := if z < 0 then -z else z

def sameKingRay (k f t : Square) : Bool :=
  let dr : Int := (f.row : Int) - k.row
  let dc : Int := (f.col : Int) - k.col
  let tr : Int := (t.row : Int) - k.row
  let tc : Int := (t.col : Int) - k.col
  let col := if dr = 0 then decide (tr = 0) else if dc = 0 then decide (tc = 0)
    else decide (iabs dr = iabs dc) && decide (iabs tr = iabs tc) && decide (dr * tc = dc * tr)
  col && decide (dr * tr + dc * tc > 0)

section ints
variable {s : State} {e1 e2 : Expr} {a b : Int}

def Sm (z : Int) : Prop := -1000 ≤ z ∧ z ≤ 1000

theorem evI_sub (h1 : EvE Gen.prog s e1 (i32 a)) (h2 : EvE Gen.prog s e2 (i32 b)) (ha : Sm a) (hb : Sm b) :
    EvE Gen.prog s (.bin .sub (some ⟨32, true⟩) e1 e2) (i32 (a - b)) :=
  EvE.bin h1 h2 (sub_i32 a b (by unfold Sm at *; omega) (by unfold Sm at *; omega) (by unfold Sm at *; omega)
    (by unfold Sm at *; omega) (by unfold Sm at *; omega) (by unfold Sm at *; omega))

theorem evI_add (h1 : EvE Gen.prog s e1 (i32 a)) (h2 : EvE Gen.prog s e2 (i32 b)) (ha : Sm a) (hb : Sm b) :
    EvE Gen.prog s (.bin .add (some ⟨32, true⟩) e1 e2) (i32 (a + b)) :=
  EvE.bin h1 h2 (add_i32 a b (by unfold Sm at *; omega) (by unfold Sm at *; omega) (by unfold Sm at *; omega)
    (by unfold Sm at *; omega) (by unfold Sm at *; omega) (by unfold Sm at *; omega))

theorem mul_i32 (a b : Int) (ha : -1000 ≤ a ∧ a ≤ 1000) (hb : -1000 ≤ b ∧ b ≤ 1000) :
    evalBin .mul (some ⟨32, true⟩) (i32 a) (i32 b) = .ok (i32 (a * b)) := by
  have na : a.natAbs ≤ 1000 := by rcases Int.natAbs_eq a with h | h <;> omega
  have nb : b.natAbs ≤ 1000 := by rcases Int.natAbs_eq b with h | h <;> omega
  have hn : (a * b).natAbs ≤ 1000000 := by
    rw [Int.natAbs_mul]; exact Nat.mul_le_mul na nb
  have h1 : -2147483648 ≤ a * b ∧ a * b < 2147483648 := by
    rcases Int.natAbs_eq (a * b) with h | h <;> omega
  simp [evalBin, isPtr, evalBinInt, binInt, intOf, i32, IntTy.i32, Res.bind, arith,
    toInt_wrap32 a (by omega) (by omega), toInt_wrap32 b (by omega) (by omega), IntTy.inRange, IntTy.minVal,
    IntTy.maxVal]
  omega

theorem cmp_i32 (op : BinOp) (a b : Int) (ha : -1000 ≤ a ∧ a ≤ 1000) (hb : -1000 ≤ b ∧ b ≤ 1000)
    (hop : op = .eq ∨ op = .lt ∨ op = .gt) :
    evalBin op (some ⟨32, true⟩) (i32 a) (i32 b) =
      .ok (boolVal (if op = .eq then decide (a = b) else if op = .lt then decide (a < b) else decide (a > b))) := by
  rcases hop with rfl | rfl | rfl <;>
  simp [evalBin, isPtr, evalBinInt, binInt, intOf, i32, IntTy.i32, Res.bind,
    toInt_wrap32 a (by omega) (by omega), toInt_wrap32 b (by omega) (by omega)]

theorem neg_i32 (a : Int) (ha : -1000 ≤ a ∧ a ≤ 1000) :
    evalUn .neg ⟨32, true⟩ (i32 a) = .ok (i32 (-a)) := by
  simp [evalUn, intOf, i32, IntTy.i32, Res.bind, arith, toInt_wrap32 a (by omega) (by omega), IntTy.inRange,
    IntTy.minVal, IntTy.maxVal]
  omega

theorem evAbs {j : Nat} {z : Int} (hj : s.locals j = some (i32 z)) (hz : -1000 ≤ z ∧ z ≤ 1000) :
    EvE Gen.prog s (.cond (.bin .lt (some ⟨32, true⟩) (.var j) (.const (.int ⟨32, true⟩ 0)))
      (.un .neg ⟨32, true⟩ (.var j)) (.var j)) (i32 (iabs z)) := by
  apply EvE_of_eval (n := 4)
  have h0 : (Val.int ⟨32, true⟩ 0) = i32 0 := rfl
  simp only [evalExpr, hj, h0, Res.bind_eq, Res.bind_ok]
  rw [cmp_i32 .lt z 0 hz (by omega) (Or.inr (Or.inl rfl))]
  simp only [Res.bind_ok, show BinOp.lt ≠ BinOp.eq by decide, if_false, if_true, truthy_boolVal]
  by_cases h : z < 0
  · simp only [decide_eq_true h, if_true, evalExpr, hj, Res.bind_eq, Res.bind_ok]
    rw [neg_i32 z hz]; simp [iabs, h]
  · simp only [decide_eq_false h, Bool.false_eq_true, if_false, evalExpr, hj]; simp [iabs, h]

theorem evI_mul (h1 : EvE Gen.prog s e1 (i32 a)) (h2 : EvE Gen.prog s e2 (i32 b)) (ha : Sm a) (hb : Sm b) :
    EvE Gen.prog s (.bin .mul (some ⟨32, true⟩) e1 e2) (i32 (a * b)) :=
  EvE.bin h1 h2 (mul_i32 a b ha hb)

theorem evI_eq (h1 : EvE Gen.prog s e1 (i32 a)) (h2 : EvE Gen.prog s e2 (i32 b)) (ha : Sm a) (hb : Sm b) :
    EvE Gen.prog s (.bin .eq (some ⟨32, true⟩) e1 e2) (boolVal (decide (a = b))) :=
  EvE.bin h1 h2 (by rw [cmp_i32 .eq a b ha hb (Or.inl rfl)]; rfl)

theorem evI_gt (h1 : EvE Gen.prog s e1 (i32 a)) (h2 : EvE Gen.prog s e2 (i32 b)) (ha : Sm a) (hb : Sm b) :
    EvE Gen.prog s (.bin .gt (some ⟨32, true⟩) e1 e2) (boolVal (decide (a > b))) :=
  EvE.bin h1 h2 (by rw [cmp_i32 .gt a b ha hb (Or.inr (Or.inr rfl))]; rfl)

theorem evB_and {x y : Bool} (h1 : EvE Gen.prog s e1 (boolVal x)) (h2 : EvE Gen.prog s e2 (boolVal y)) :
    EvE Gen.prog s (.land e1 e2) (boolVal (x && y)) := by
  cases x
  · exact EvE.land_false h1 (truthy_boolVal _)
  · simpa using EvE.land_true h1 (truthy_boolVal _) h2 (truthy_boolVal _)

theorem evB_u8 {x : Bool} (h1 : EvE Gen.prog s e1 (boolVal x)) :
    EvE Gen.prog s (.cast ⟨8, false⟩ (.bin .ne (some ⟨32, true⟩) e1 (.const (.int ⟨32, true⟩ 0))))
      (u8 (if x then 1 else 0)) := by
  refine EvE.cast (EvE.bin h1 (EvE.const _) (v := boolVal x) ?_) ?_
  · cases x <;> simp [evalBin, isPtr, evalBinInt, binInt, intOf, boolVal, IntTy.i32, IntTy.toInt, Res.bind]
  · cases x <;> simp [evalCast, boolVal, u8, IntTy.i32, IntTy.u8, IntTy.toInt, IntTy.wrap, IntTy.modulus]

end ints

theorem sm_mul (a b : Int) (ha : -8 ≤ a ∧ a ≤ 8) (hb : -8 ≤ b ∧ b ≤ 8) : Sm (a * b) := by
  have na : a.natAbs ≤ 8 := by rcases Int.natAbs_eq a with h | h <;> omega
  have nb : b.natAbs ≤ 8 := by rcases Int.natAbs_eq b with h | h <;> omega
  have hn : (a * b).natAbs ≤ 64 := by rw [Int.natAbs_mul]; exact Nat.mul_le_mul na nb
  unfold Sm; rcases Int.natAbs_eq (a * b) with h | h <;> omega

theorem mul64 (a b : Int) (ha : -8 ≤ a ∧ a ≤ 8) (hb : -8 ≤ b ∧ b ≤ 8) : -64 ≤ a * b ∧ a * b ≤ 64 := by
  have na : a.natAbs ≤ 8 := by rcases Int.natAbs_eq a with h | h <;> omega
  have nb : b.natAbs ≤ 8 := by rcases Int.natAbs_eq b with h | h <;> omega
  have hn : (a * b).natAbs ≤ 64 := by rw [Int.natAbs_mul]; exact Nat.mul_le_mul na nb
  rcases Int.natAbs_eq (a * b) with h | h <;> omega

theorem same_king_ray_spec (k f t : Square) (m : Mem) (ro : Bool) :
    ∃ s', ExS Gen.prog ⟨frameLocals Gen.same_king_ray.params [u8 k.val, u8 f.val, u8 t.val], m, ro⟩
      Gen.same_king_ray.body (.ret (some (u8 (if sameKingRay k f t then 1 else 0)))) s' := by
  let s0 : State := ⟨frameLocals Gen.same_king_ray.params [u8 k.val, u8 f.val, u8 t.val], m, ro⟩
  have hk := k.isLt; have hf := f.isLt; have ht := t.isLt
  let KR : Int := (Square.row k : Nat); let KC : Int := (Square.col k : Nat)
  let FR : Int := (Square.row f : Nat); let FC : Int := (Square.col f : Nat)
  let TR : Int := (Square.row t : Nat); let TC : Int := (Square.col t : Nat)
  have bK : Square.row k < 9 ∧ Square.col k < 9 := by simp [Square.row, Square.col]; omega
  have bF : Square.row f < 9 ∧ Square.col f < 9 := by simp [Square.row, Square.col]; omega
  have bT : Square.row t < 9 ∧ Square.col t < 9 := by simp [Square.row, Square.col]; omega
  -- the six coordinate calls
  have cr : ∀ (x : Square) (st : State) (j d : Nat), st.locals j = some (u8 x.val) →
      ExS Gen.prog st (.call (some d) 7 [(.var j)]) .normal { st with locals := st.locals.upd d (i32 (Square.row x)) } :=
    fun x st j d h => call_pure rfl rfl rfl rfl (row_of_refines x) (EvArgs.cons (EvE.var h) EvArgs.nil)
  have cc : ∀ (x : Square) (st : State) (j d : Nat), st.locals j = some (u8 x.val) →
      ExS Gen.prog st (.call (some d) 8 [(.var j)]) .normal { st with locals := st.locals.upd d (i32 (Square.col x)) } :=
    fun x st j d h => call_pure rfl rfl rfl rfl (col_of_refines x) (EvArgs.cons (EvE.var h) EvArgs.nil)
  have l0 : s0.locals 0 = some (u8 k.val) := rfl
  have l1 : s0.locals 1 = some (u8 f.val) := rfl
  have l2 : s0.locals 2 = some (u8 t.val) := rfl
  -- king coordinates
  let a1 : State := { s0 with locals := s0.locals.upd 4 (i32 KR) }
  have x1 := cr k s0 0 4 l0
  let a2 : State := { a1 with locals := a1.locals.upd 3 (i32 KR) }
  have x2 : ExS Gen.prog a1 (.set 3 (.var 4)) .normal a2 := ExS.set (EvE.var (by simp [a1, Locals.upd]))
  let a3 : State := { a2 with locals := a2.locals.upd 6 (i32 KC) }
  have x3 := cc k a2 0 6 (by simp [a2, a1, Locals.upd]; exact l0)
  let a4 : State := { a3 with locals := a3.locals.upd 5 (i32 KC) }
  have x4 : ExS Gen.prog a3 (.set 5 (.var 6)) .normal a4 := ExS.set (EvE.var (by simp [a3, Locals.upd]))
  -- from coordinates
  let b1 : State := { a4 with locals := a4.locals.upd 8 (i32 FR) }
  have y1 := cr f a4 1 8 (by simp [a4, a3, a2, a1, Locals.upd]; exact l1)
  let b2 : State := { b1 with locals := b1.locals.upd 7 (i32 FR) }
  have y2 : ExS Gen.prog b1 (.set 7 (.var 8)) .normal b2 := ExS.set (EvE.var (by simp [b1, Locals.upd]))
  let b3 : State := { b2 with locals := b2.locals.upd 10 (i32 FC) }
  have y3 := cc f b2 1 10 (by simp [b2, b1, a4, a3, a2, a1, Locals.upd]; exact l1)
  let b4 : State := { b3 with locals := b3.locals.upd 9 (i32 FC) }
  have y4 : ExS Gen.prog b3 (.set 9 (.var 10)) .normal b4 := ExS.set (EvE.var (by simp [b3, Locals.upd]))
  -- to coordinates
  let c1 : State := { b4 with locals := b4.locals.upd 12 (i32 TR) }
  have z1 := cr t b4 2 12 (by simp [b4, b3, b2, b1, a4, a3, a2, a1, Locals.upd]; exact l2)
  let c2 : State := { c1 with locals := c1.locals.upd 11 (i32 TR) }
  have z2 : ExS Gen.prog c1 (.set 11 (.var 12)) .normal c2 := ExS.set (EvE.var (by simp [c1, Locals.upd]))
  let c3 : State := { c2 with locals := c2.locals.upd 14 (i32 TC) }
  have z3 := cc t c2 2 14 (by simp [c2, c1, b4, b3, b2, b1, a4, a3, a2, a1, Locals.upd]; exact l2)
  let c4 : State := { c3 with locals := c3.locals.upd 13 (i32 TC) }
  have z4 : ExS Gen.prog c3 (.set 13 (.var 14)) .normal c4 := ExS.set (EvE.var (by simp [c3, Locals.upd]))
  have g3 : c4.locals 3 = some (i32 KR) := by simp [c4, c3, c2, c1, b4, b3, b2, b1, a4, a3, a2, Locals.upd]
  have g5 : c4.locals 5 = some (i32 KC) := by simp [c4, c3, c2, c1, b4, b3, b2, b1, a4, Locals.upd]
  have g7 : c4.locals 7 = some (i32 FR) := by simp [c4, c3, c2, c1, b4, b3, b2, Locals.upd]
  have g9 : c4.locals 9 = some (i32 FC) := by simp [c4, c3, c2, c1, b4, Locals.upd]
  have g11 : c4.locals 11 = some (i32 TR) := by simp [c4, c3, c2, Locals.upd]
  have g13 : c4.locals 13 = some (i32 TC) := by simp [c4, Locals.upd]
  have sK : Sm KR ∧ Sm KC := by simp only [Sm, KR, KC]; omega
  have sF : Sm FR ∧ Sm FC := by simp only [Sm, FR, FC]; omega
  have sT : Sm TR ∧ Sm TC := by simp only [Sm, TR, TC]; omega
  let DR := FR - KR; let DC := FC - KC; let XR := TR - KR; let XC := TC - KC
  have sD : Sm DR ∧ Sm DC ∧ Sm XR ∧ Sm XC := by simp only [Sm, DR, DC, XR, XC, KR, KC, FR, FC, TR, TC]; omega
  have b8 : (-8 ≤ DR ∧ DR ≤ 8) ∧ (-8 ≤ DC ∧ DC ≤ 8) ∧ (-8 ≤ XR ∧ XR ≤ 8) ∧ (-8 ≤ XC ∧ XC ≤ 8) := by
    simp only [DR, DC, XR, XC, KR, KC, FR, FC, TR, TC]; omega
  let d1 : State := { c4 with locals := c4.locals.upd 15 (i32 DR) }
  have w1 : ExS Gen.prog c4 (.set 15 (.bin .sub (some ⟨32, true⟩) (.var 7) (.var 3))) .normal d1 :=
    ExS.set (evI_sub (EvE.var g7) (EvE.var g3) sF.1 sK.1)
  let d2 : State := { d1 with locals := d1.locals.upd 16 (i32 DC) }
  have w2 : ExS Gen.prog d1 (.set 16 (.bin .sub (some ⟨32, true⟩) (.var 9) (.var 5))) .normal d2 :=
    ExS.set (evI_sub (EvE.var (by simp [d1, Locals.upd]; exact g9)) (EvE.var (by simp [d1, Locals.upd]; exact g5))
      sF.2 sK.2)
  let d3 : State := { d2 with locals := d2.locals.upd 17 (i32 XR) }
  have w3 : ExS Gen.prog d2 (.set 17 (.bin .sub (some ⟨32, true⟩) (.var 11) (.var 3))) .normal d3 :=
    ExS.set (evI_sub (EvE.var (by simp [d2, d1, Locals.upd]; exact g11)) (EvE.var (by simp [d2, d1, Locals.upd]; exact g3))
      sT.1 sK.1)
  let d4 : State := { d3 with locals := d3.locals.upd 18 (i32 XC) }
  have w4 : ExS Gen.prog d3 (.set 18 (.bin .sub (some ⟨32, true⟩) (.var 13) (.var 5))) .normal d4 :=
    ExS.set (evI_sub (EvE.var (by simp [d3, d2, d1, Locals.upd]; exact g13))
      (EvE.var (by simp [d3, d2, d1, Locals.upd]; exact g5)) sT.2 sK.2)
  have v15 : EvE Gen.prog d4 (.var 15) (i32 DR) := EvE.var (by simp [d4, d3, d2, d1, Locals.upd])
  have v16 : EvE Gen.prog d4 (.var 16) (i32 DC) := EvE.var (by simp [d4, d3, d2, Locals.upd])
  have v17 : EvE Gen.prog d4 (.var 17) (i32 XR) := EvE.var (by simp [d4, d3, Locals.upd])
  have v18 : EvE Gen.prog d4 (.var 18) (i32 XC) := EvE.var (by simp [d4, Locals.upd])
  have zero : EvE Gen.prog d4 (.const (.int ⟨32, true⟩ 0)) (i32 0) := EvE.const _
  have s0' : Sm 0 := by simp [Sm]
  let B : Bool := if DR = 0 then decide (XR = 0) else if DC = 0 then decide (XC = 0)
    else decide (iabs DR = iabs DC) && decide (iabs XR = iabs XC) && decide (DR * XC = DC * XR)
  have hab : ∀ z, Sm z → Sm (iabs z) := fun z hz => by unfold Sm iabs at *; split <;> omega
  obtain ⟨d5, w5, l19⟩ : ∃ d5, ExS Gen.prog d4 (.ite (.bin .eq (some ⟨32, true⟩) (.var 15) (.const (.int ⟨32, true⟩ 0))) (.set 19 (.cast ⟨8, false⟩ (.bin .ne (some ⟨32, true⟩) (.bin .eq (some ⟨32, true⟩) (.var 17) (.const (.int ⟨32, true⟩ 0))) (.const (.int ⟨32, true⟩ 0))))) (.ite (.bin .eq (some ⟨32, true⟩) (.var 16) (.const (.int ⟨32, true⟩ 0))) (.set 19 (.cast ⟨8, false⟩ (.bin .ne (some ⟨32, true⟩) (.bin .eq (some ⟨32, true⟩) (.var 18) (.const (.int ⟨32, true⟩ 0))) (.const (.int ⟨32, true⟩ 0))))) (.set 19 (.cast ⟨8, false⟩ (.bin .ne (some ⟨32, true⟩) (.land (.land (.bin .eq (some ⟨32, true⟩) (.cond (.bin .lt (some ⟨32, true⟩) (.var 15) (.const (.int ⟨32, true⟩ 0))) (.un .neg ⟨32, true⟩ (.var 15)) (.var 15)) (.cond (.bin .lt (some ⟨32, true⟩) (.var 16) (.const (.int ⟨32, true⟩ 0))) (.un .neg ⟨32, true⟩ (.var 16)) (.var 16))) (.bin .eq (some ⟨32, true⟩) (.cond (.bin .lt (some ⟨32, true⟩) (.var 17) (.const (.int ⟨32, true⟩ 0))) (.un .neg ⟨32, true⟩ (.var 17)) (.var 17)) (.cond (.bin .lt (some ⟨32, true⟩) (.var 18) (.const (.int ⟨32, true⟩ 0))) (.un .neg ⟨32, true⟩ (.var 18)) (.var 18)))) (.bin .eq (some ⟨32, true⟩) (.bin .mul (some ⟨32, true⟩) (.var 15) (.var 18)) (.bin .mul (some ⟨32, true⟩) (.var 16) (.var 17)))) (.const (.int ⟨32, true⟩ 0))))))) .normal d5 ∧
      d5.locals = d4.locals.upd 19 (u8 (if B then 1 else 0)) := by
    have c15 := evI_eq v15 zero sD.1 s0'
    by_cases h1 : DR = 0
    · refine ⟨_, ExS.ite (bc := true) c15 (by simp [truthy_boolVal, h1]) (ExS.set (evB_u8 (evI_eq v17 zero sD.2.2.1 s0'))), ?_⟩
      simp [B, h1]
    · have c16 := evI_eq v16 zero sD.2.1 s0'
      by_cases h2 : DC = 0
      · refine ⟨_, ExS.ite (bc := false) c15 (by simp [truthy_boolVal, h1]) (ExS.ite (bc := true) c16
          (by simp [truthy_boolVal, h2]) (ExS.set (evB_u8 (evI_eq v18 zero sD.2.2.2 s0')))), ?_⟩
        simp [B, h1, h2]
      · have a15 := evAbs (s := d4) (j := 15) (by simp [d4, d3, d2, d1, Locals.upd]) sD.1
        have a16 := evAbs (s := d4) (j := 16) (by simp [d4, d3, d2, Locals.upd]) sD.2.1
        have a17 := evAbs (s := d4) (j := 17) (by simp [d4, d3, Locals.upd]) sD.2.2.1
        have a18 := evAbs (s := d4) (j := 18) (by simp [d4, Locals.upd]) sD.2.2.2
        have hex := evB_u8 (evB_and (evB_and (evI_eq a15 a16 (hab _ sD.1) (hab _ sD.2.1))
          (evI_eq a17 a18 (hab _ sD.2.2.1) (hab _ sD.2.2.2)))
          (evI_eq (evI_mul v15 v18 sD.1 sD.2.2.2) (evI_mul v16 v17 sD.2.1 sD.2.2.1) (sm_mul _ _ b8.1 b8.2.2.2) (sm_mul _ _ b8.2.1 b8.2.2.1)))
        refine ⟨_, ExS.ite (bc := false) c15 (by simp [truthy_boolVal, h1]) (ExS.ite (bc := false) c16
          (by simp [truthy_boolVal, h2]) (ExS.set hex)), ?_⟩
        simp [B, h1, h2]
  have v19 : EvE Gen.prog d5 (.cast ⟨32, true⟩ (.var 19)) (boolVal B) :=
    EvE.cast (EvE.var (v := u8 (if B then 1 else 0)) (by rw [l19]; simp [Locals.upd])) (by cases B <;> rfl)
  have e5s : ∀ j, j ≠ 19 → d5.locals j = d4.locals j := fun j hj => by rw [l19]; simp [Locals.upd, hj]
  have u15 : EvE Gen.prog d5 (.var 15) (i32 DR) := EvE.var (by rw [e5s 15 (by decide)]; simp [d4, d3, d2, d1, Locals.upd])
  have u16 : EvE Gen.prog d5 (.var 16) (i32 DC) := EvE.var (by rw [e5s 16 (by decide)]; simp [d4, d3, d2, Locals.upd])
  have u17 : EvE Gen.prog d5 (.var 17) (i32 XR) := EvE.var (by rw [e5s 17 (by decide)]; simp [d4, d3, Locals.upd])
  have u18 : EvE Gen.prog d5 (.var 18) (i32 XC) := EvE.var (by rw [e5s 18 (by decide)]; simp [d4, Locals.upd])
  have m1 := sm_mul _ _ b8.1 b8.2.2.1
  have m2 := sm_mul _ _ b8.2.1 b8.2.2.2
  have hsum : Sm (DR * XR + DC * XC) := by
    have q1 := mul64 _ _ b8.1 b8.2.2.1; have q2 := mul64 _ _ b8.2.1 b8.2.2.2
    unfold Sm; constructor <;> omega
  have zero5 : EvE Gen.prog d5 (.const (.int ⟨32, true⟩ 0)) (i32 0) := EvE.const _
  have hret := evB_u8 (evB_and v19 (evI_gt (evI_add (evI_mul u15 u17 sD.1 sD.2.2.1) (evI_mul u16 u18 sD.2.1 sD.2.2.2)
    m1 m2) zero5 hsum (by simp [Sm])))
  have hspec : sameKingRay k f t = (B && decide (DR * XR + DC * XC > 0)) := rfl
  refine ⟨d5, ?_⟩
  rw [hspec]
  exact ExS.seq (ExS.seq x1 (ExS.seq x2 (ExS.seq x3 x4))) (ExS.seq (ExS.seq y1 (ExS.seq y2 (ExS.seq y3 y4)))
    (ExS.seq (ExS.seq z1 (ExS.seq z2 (ExS.seq z3 z4))) (ExS.seq (ExS.seq w1 w2) (ExS.seq (ExS.seq w3 w4)
      (ExS.seq w5 (ExS.ret hret))))))

end Shogi.C.Proofs
