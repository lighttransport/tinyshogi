/-
  T7 generators, layer 2 (cont.): the row/column loops of `add_pseudo_drops`.
-/
import Shogi.C.Proofs.AddDrops

namespace Shogi.C.Proofs
variable {posBlock : Nat}
open MiniC Shogi Shogi.C

/-! ### The column loop (`loop3`) -/

def sq3 : Stmt := (.seq (.call (some 15) 10 [(.var 12), (.var 13)]) (.set 14 (.var 15)))
def occ3 : Stmt := (.ite (.bin .ne (some ⟨32, true⟩) (.cast ⟨32, true⟩ (.load (.int ⟨8, false⟩) (.index (.field (.var 0) 0) (.var 14) 1))) (.const (.int ⟨32, true⟩ 0))) .cont .skip)
def pf3 : Stmt := (.ite (.bin .ne (some ⟨32, false⟩) (.bin .band (some ⟨32, false⟩) (.var 5) (.bin .shl (some ⟨32, false⟩) (.const (.int ⟨32, false⟩ 1)) (.var 13))) (.const (.int ⟨32, false⟩ 0))) (.set 16 (.cast ⟨32, false⟩ (.bin .band (some ⟨32, false⟩) (.cast ⟨32, false⟩ (.var 16)) (.cast ⟨32, false⟩ (.un .bnot ⟨32, false⟩ (.const (.int ⟨32, false⟩ 1))))))) .skip)
def row3 : Stmt := (.ite (.lor (.land (.bin .eq (some ⟨32, false⟩) (.cast ⟨32, false⟩ (.var 1)) (.cast ⟨32, false⟩ (.const (.int ⟨32, true⟩ 0)))) (.bin .eq (some ⟨32, true⟩) (.var 12) (.const (.int ⟨32, true⟩ 0)))) (.land (.bin .eq (some ⟨32, false⟩) (.cast ⟨32, false⟩ (.var 1)) (.cast ⟨32, false⟩ (.const (.int ⟨32, true⟩ 1)))) (.bin .eq (some ⟨32, true⟩) (.var 12) (.const (.int ⟨32, true⟩ 8))))) (.set 16 (.cast ⟨32, false⟩ (.bin .band (some ⟨32, false⟩) (.cast ⟨32, false⟩ (.var 16)) (.cast ⟨32, false⟩ (.un .bnot ⟨32, false⟩ (.const (.int ⟨32, false⟩ 7))))))) (.ite (.lor (.land (.bin .eq (some ⟨32, false⟩) (.cast ⟨32, false⟩ (.var 1)) (.cast ⟨32, false⟩ (.const (.int ⟨32, true⟩ 0)))) (.bin .eq (some ⟨32, true⟩) (.var 12) (.const (.int ⟨32, true⟩ 1)))) (.land (.bin .eq (some ⟨32, false⟩) (.cast ⟨32, false⟩ (.var 1)) (.cast ⟨32, false⟩ (.const (.int ⟨32, true⟩ 1)))) (.bin .eq (some ⟨32, true⟩) (.var 12) (.const (.int ⟨32, true⟩ 7))))) (.set 16 (.cast ⟨32, false⟩ (.bin .band (some ⟨32, false⟩) (.cast ⟨32, false⟩ (.var 16)) (.cast ⟨32, false⟩ (.un .bnot ⟨32, false⟩ (.bin .shl (some ⟨32, false⟩) (.const (.int ⟨32, false⟩ 1)) (.const (.int ⟨32, true⟩ 2)))))))) .skip))
def step3 : Stmt := (.set 13 (.cast ⟨32, true⟩ (.bin .add (some ⟨32, true⟩) (.cast ⟨32, true⟩ (.var 13)) (.const (.int ⟨32, true⟩ 1)))))
def body3 : Stmt := .ite (.bin .lt (some ⟨32, true⟩) (.var 13) (.const (.int ⟨32, true⟩ 9)))
  (.seq sq3 (.seq occ3 (.seq (.set 16 (.var 6)) (.seq pf3 (.seq row3 (.loop bitBody .skip)))))) .brk

theorem add_pseudo_drops_loop3_eq : Gen.add_pseudo_drops_loop3 = .loop body3 step3 := rfl

theorem upd_same {l : Locals} {j : Nat} {v : Val} (h : l j = some v) : l.upd j v = l := by
  funext x; by_cases hx : x = j
  · subst hx; simp [Locals.upd, h]
  · simp [Locals.upd, hx]

/-- The restriction masks: `allowed` becomes `allowedC`. -/
theorem mask_spec {s : State} {c : Color} {pfm act r col : Nat} (hact : act < 2 ^ 32)
    (hr : r < 9) (hcol : col < 9)
    (h1 : s.locals 1 = some (.int IntTy.u32 c.idx)) (h5 : s.locals 5 = some (.int IntTy.u32 pfm))
    (h6 : s.locals 6 = some (.int IntTy.u32 act)) (h12 : s.locals 12 = some (.int IntTy.i32 r))
    (h13 : s.locals 13 = some (.int IntTy.i32 col)) (hpfm : pfm < 2 ^ 32) :
    ∃ s', (∀ {rest o s''}, ExS Gen.prog s' rest o s'' →
        ExS Gen.prog s (.seq (.set 16 (.var 6)) (.seq pf3 (.seq row3 rest))) o s'') ∧ s'.mem = s.mem ∧
      s'.ro = s.ro ∧
      s'.locals 16 = some (.int IntTy.u32 (allowedC act (decide (pfm &&& 2 ^ col ≠ 0)) c r)) ∧
      ∀ x, x ≠ 16 → s'.locals x = s.locals x := by
  let s1 : State := { s with locals := s.locals.upd 16 (.int IntTy.u32 act) }
  have e1 : ExS Gen.prog s (.set 16 (.var 6)) .normal s1 := ExS.set (EvE.var h6)
  have hc32 : 2 ^ col < 2 ^ 32 := Nat.pow_lt_pow_right (by decide) (by omega)
  let pf := decide (pfm &&& 2 ^ col ≠ 0)
  let a1 := if pf then act &&& (2 ^ 32 - 1 - 1) else act
  have ha1 : a1 < 2 ^ 32 := by
    simp only [a1]; split
    · exact Nat.lt_of_le_of_lt Nat.and_le_left hact
    · exact hact
  let s2 : State := { s1 with locals := s1.locals.upd 16 (.int IntTy.u32 a1) }
  have h5' : s1.locals 5 = some (.int IntTy.u32 pfm) := by simp [s1, Locals.upd, h5]
  have h13' : s1.locals 13 = some (.int IntTy.i32 col) := by simp [s1, Locals.upd, h13]
  have h16' : s1.locals 16 = some (.int IntTy.u32 act) := by simp [s1, Locals.upd]
  have e2 : ExS Gen.prog s1 pf3 .normal s2 := by
    have hcond : EvE Gen.prog s1 (.bin .ne (some ⟨32, false⟩) (.bin .band (some ⟨32, false⟩) (.var 5)
        (.bin .shl (some ⟨32, false⟩) (.const (.int ⟨32, false⟩ 1)) (.var 13))) (.const (.int ⟨32, false⟩ 0)))
        (boolVal pf) := by
      apply EvE_of_eval (n := 5)
      simp [evalExpr, h5', h13', evalBin, isPtr, evalBinInt, binInt, intOf, IntTy.u32, IntTy.i32, IntTy.toInt,
        IntTy.modulus, Res.bind, MiniC.guard, show ¬ (2147483648 ≤ col) by omega, show (col : Int) < 32 by omega,
        Nat.mod_eq_of_lt hc32, Nat.mod_eq_of_lt hpfm, pf,
        Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt Nat.and_le_left hpfm)]
    by_cases hp : pf = true
    · refine ExS.ite (bc := true) hcond (by simp [truthy_boolVal, hp]) (ExS.set (EvE_of_eval (n := 6) ?_))
      simp [evalExpr, h16', evalCast, evalBin, evalUn, isPtr, evalBinInt, binInt, intOf, IntTy.u32,
        IntTy.modulus, Res.bind, a1, hp, Nat.mod_eq_of_lt hact,
        Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt Nat.and_le_left hact)]
    · have : s2 = s1 := by
        have hl : s1.locals.upd 16 (.int IntTy.u32 act) = s1.locals := by
          funext x; by_cases hx : x = 16
          · subst hx; simp [Locals.upd, h16']
          · simp [Locals.upd, hx]
        have ha : a1 = act := by simp [a1, hp]
        simp only [s2, ha, hl]
      rw [this]; exact ExS.ite (bc := false) hcond (by simp [truthy_boolVal, hp]) ExS.skip
  have h1' : s2.locals 1 = some (.int IntTy.u32 c.idx) := by simp [s2, s1, Locals.upd, h1]
  have h12' : s2.locals 12 = some (.int IntTy.i32 r) := by simp [s2, s1, Locals.upd, h12]
  have h16'' : s2.locals 16 = some (.int IntTy.u32 a1) := by simp [s2, Locals.upd]
  let d3 := (c == .black && r == 0) || (c == .white && r == 8)
  let d2 := (c == .black && r == 1) || (c == .white && r == 7)
  have hr32 : ¬ (2147483648 ≤ r) := by omega
  have ev3 : EvE Gen.prog s2 (.lor (.land (.bin .eq (some ⟨32, false⟩) (.cast ⟨32, false⟩ (.var 1)) (.cast ⟨32, false⟩ (.const (.int ⟨32, true⟩ 0)))) (.bin .eq (some ⟨32, true⟩) (.var 12) (.const (.int ⟨32, true⟩ 0)))) (.land (.bin .eq (some ⟨32, false⟩) (.cast ⟨32, false⟩ (.var 1)) (.cast ⟨32, false⟩ (.const (.int ⟨32, true⟩ 1)))) (.bin .eq (some ⟨32, true⟩) (.var 12) (.const (.int ⟨32, true⟩ 8))))) (boolVal d3) := by
    apply EvE_of_eval (n := 5)
    cases c <;> simp [evalExpr, h1', h12', evalCast, evalBin, isPtr, evalBinInt, binInt, intOf, IntTy.u32,
      IntTy.i32, IntTy.toInt, IntTy.modulus, IntTy.wrap, Res.bind, truthy, boolVal, d3, Color.idx, hr32] <;> split <;> simp_all <;> omega
  have ev2 : EvE Gen.prog s2 (.lor (.land (.bin .eq (some ⟨32, false⟩) (.cast ⟨32, false⟩ (.var 1)) (.cast ⟨32, false⟩ (.const (.int ⟨32, true⟩ 0)))) (.bin .eq (some ⟨32, true⟩) (.var 12) (.const (.int ⟨32, true⟩ 1)))) (.land (.bin .eq (some ⟨32, false⟩) (.cast ⟨32, false⟩ (.var 1)) (.cast ⟨32, false⟩ (.const (.int ⟨32, true⟩ 1)))) (.bin .eq (some ⟨32, true⟩) (.var 12) (.const (.int ⟨32, true⟩ 7))))) (boolVal d2) := by
    apply EvE_of_eval (n := 5)
    cases c <;> simp [evalExpr, h1', h12', evalCast, evalBin, isPtr, evalBinInt, binInt, intOf, IntTy.u32,
      IntTy.i32, IntTy.toInt, IntTy.modulus, IntTy.wrap, Res.bind, truthy, boolVal, d2, Color.idx, hr32] <;> split <;> simp_all <;> omega
  have hm7 : a1 &&& (2 ^ 32 - 1 - 7) < 2 ^ 32 := Nat.lt_of_le_of_lt Nat.and_le_left ha1
  have hm4 : a1 &&& (2 ^ 32 - 1 - 4) < 2 ^ 32 := Nat.lt_of_le_of_lt Nat.and_le_left ha1
  have hfin : allowedC act pf c r = if d3 then a1 &&& (2 ^ 32 - 1 - 7) else if d2 then a1 &&& (2 ^ 32 - 1 - 4)
      else a1 := rfl
  obtain ⟨s3, e3, hs3m, hs3ro, hs3l, hs3o⟩ : ∃ s3, ExS Gen.prog s2 row3 .normal s3 ∧ s3.mem = s2.mem ∧
      s3.ro = s2.ro ∧ s3.locals 16 = some (.int IntTy.u32 (allowedC act pf c r)) ∧
      ∀ x, x ≠ 16 → s3.locals x = s2.locals x := by
    rw [hfin]
    by_cases hd3 : d3 = true
    · refine ⟨_, ExS.ite (bc := true) ev3 (by simp [truthy_boolVal, hd3]) (ExS.set (v := .int IntTy.u32 (a1 &&& (2 ^ 32 - 1 - 7))) (EvE_of_eval (n := 6) ?_)),
        rfl, rfl, by simp [Locals.upd, hd3], fun x hx => by simp [Locals.upd, hx]⟩
      simp [evalExpr, h16'', evalCast, evalBin, evalUn, isPtr, evalBinInt, binInt, intOf, IntTy.u32,
        IntTy.modulus, Res.bind, Nat.mod_eq_of_lt ha1, Nat.mod_eq_of_lt hm7]
    by_cases hd2 : d2 = true
    · refine ⟨_, ExS.ite (bc := false) ev3 (by simp [truthy_boolVal, hd3])
        (ExS.ite (bc := true) ev2 (by simp [truthy_boolVal, hd2]) (ExS.set (v := .int IntTy.u32 (a1 &&& (2 ^ 32 - 1 - 4))) (EvE_of_eval (n := 7) ?_))),
        rfl, rfl, by simp [Locals.upd, hd3, hd2], fun x hx => by simp [Locals.upd, hx]⟩
      simp [evalExpr, h16'', evalCast, evalBin, evalUn, isPtr, evalBinInt, binInt, intOf, IntTy.u32, IntTy.i32,
        IntTy.toInt, IntTy.modulus, Res.bind, MiniC.guard, Nat.mod_eq_of_lt ha1, Nat.mod_eq_of_lt hm4]
    · refine ⟨s2, ExS.ite (bc := false) ev3 (by simp [truthy_boolVal, hd3])
        (ExS.ite (bc := false) ev2 (by simp [truthy_boolVal, hd2]) ExS.skip), rfl, rfl,
        by simp [hd3, hd2, h16''], fun _ _ => rfl⟩
  refine ⟨s3, fun h => ExS.seq e1 (ExS.seq e2 (ExS.seq e3 h)), by rw [hs3m], by rw [hs3ro], hs3l, fun x hx => ?_⟩
  rw [hs3o x hx]; simp [s2, s1, Locals.upd, hx]

theorem allowedC_le (act : Nat) (pf : Bool) (c : Color) (r : Nat) : allowedC act pf c r ≤ act := by
  have h1 : (if pf then act &&& (2 ^ 32 - 1 - 1) else act) ≤ act := by
    split
    · exact Nat.and_le_left
    · exact Nat.le_refl _
  unfold allowedC; simp only
  split
  · exact Nat.le_trans Nat.and_le_left h1
  · split
    · exact Nat.le_trans Nat.and_le_left h1
    · exact h1

theorem ev_board_u8 {s : State} {p : Position} {j k : Nat} (hk : k < 81)
    (h0 : s.locals 0 = some (posPtr' posBlock)) (hj : s.locals j = some (.int IntTy.u8 k))
    (hm : s.mem posBlock = some (encode p)) :
    EvE Gen.prog s (.load (.int ⟨8, false⟩) (.index (.field (.var 0) 0) (.var j) 1)) (.int IntTy.u8 (bb p k)) := by
  have hlen := encode_length p
  refine EvE.load (pa := .ptr posBlock k) (EvE.index (pb := .ptr posBlock (0 + 0))
    (EvE.field (EvE.var h0) (by simp [ptrAddN, posPtr', hm, hlen])) (EvE.var hj) ?_) ?_
  · simp [IntTy.u8, ptrAddN, hm, hlen, IntTy.toInt]; omega
  · simp only [load, Ty.size, IntTy.bytes, show (8 : Nat) / 8 = 1 by rfl, readBoard hm k hk]
    simp [Res.bind, decodeLE, bb, hk]; rfl

/-- What one empty-or-occupied square contributes. -/
def cellOut (p : Position) (c : Color) (act pfm r col : Nat) : List (List UInt8) :=
  if bb p (r * 9 + col) ≠ 0 then []
  else (allowedS act (decide (pfm &&& 2 ^ col ≠ 0)) c r).map (dmBytes (r * 9 + col))

theorem allowedS_length (act : Nat) (pf : Bool) (c : Color) (r : Nat) : (allowedS act pf c r).length ≤ 7 := by
  unfold allowedS; rw [List.length_map]
  exact Nat.le_trans (List.length_filter_le _ _) (by simp [List.length_finRange])

theorem cellOut_length (p : Position) (c : Color) (act pfm r col : Nat) : (cellOut p c act pfm r col).length ≤ 7 := by
  unfold cellOut; split
  · simp
  · rw [List.length_map]; exact allowedS_length _ _ _ _

def cellStmt : Stmt := .seq sq3 (.seq occ3 (.seq (.set 16 (.var 6)) (.seq pf3 (.seq row3 (.loop bitBody .skip)))))

theorem cell_spec {s : State} {p : Position} {c : Color} {act pfm r col mb mo cb co cap n : Nat}
    {L : List (List UInt8)} (hact : act < 128) (hpfm : pfm < 2 ^ 32) (hr : r < 9) (hcol : col < 9)
    (h0 : s.locals 0 = some (posPtr' posBlock)) (h1 : s.locals 1 = some (.int IntTy.u32 c.idx))
    (h2 : s.locals 2 = some (.ptr mb mo)) (h3 : s.locals 3 = some (.ptr cb co))
    (h4 : s.locals 4 = some (.int IntTy.u64 cap))
    (h5 : s.locals 5 = some (.int IntTy.u32 pfm)) (h6 : s.locals 6 = some (.int IntTy.u32 act))
    (h12 : s.locals 12 = some (.int IntTy.i32 r)) (h13 : s.locals 13 = some (.int IntTy.i32 col))
    (hm : s.mem posBlock = some (encode p)) (hro : s.ro = false)
    (hb : Buf s.mem mb mo cb co cap L) (hf : Fresh s.mem n) (h64 : n + 16 < 2 ^ 64) :
    ∃ s' o, ExS Gen.prog s cellStmt o s' ∧ (o = .normal ∨ o = .cont) ∧
      Buf s'.mem mb mo cb co cap (L ++ cellOut p c act pfm r col) ∧
      Fresh s'.mem (n + 2 * (cellOut p c act pfm r col).length) ∧ Frame s.mem s'.mem mb cb ∧ s'.ro = false ∧
      ∀ x, x ≠ 14 → x ≠ 15 → x ≠ 16 → x ≠ 17 → x ≠ 18 → s'.locals x = s.locals x := by
  have hto : r * 9 + col < 81 := by omega
  have hsqa : run Gen.fid_square_at [i32 (r : Int), i32 (col : Int)] = some (some (u8 (r * 9 + col))) :=
    square_at_refines ⟨r, hr⟩ ⟨col, hcol⟩
  let sA : State := { s with locals := s.locals.upd 15 (u8 (r * 9 + col)) }
  let sB : State := { sA with locals := sA.locals.upd 14 (u8 (r * 9 + col)) }
  have eS : ExS Gen.prog s sq3 .normal sB :=
    ExS.seq (call_pure rfl rfl rfl rfl hsqa (EvArgs.cons (EvE.var (by rw [h12, i32_nat r (by omega)]))
      (EvArgs.cons (EvE.var (by rw [h13, i32_nat col (by omega)])) EvArgs.nil)))
      (ExS.set (EvE.var (by simp [sA, Locals.upd])))
  have hB : ∀ x, x ≠ 14 → x ≠ 15 → sB.locals x = s.locals x := fun x a b => by simp [sB, sA, Locals.upd, a, b]
  have hB14 : sB.locals 14 = some (.int IntTy.u8 (r * 9 + col)) := by simp [sB, Locals.upd, u8]
  have hne := ev_ne0e (bb_lt p _) (ev_board_u8 (s := sB) hto (by rw [hB 0 (by decide) (by decide)]; exact h0)
    hB14 hm)
  by_cases hocc : bb p (r * 9 + col) ≠ 0
  · have hc : cellOut p c act pfm r col = [] := by simp [cellOut, hocc]
    refine ⟨sB, .cont, ExS.seq eS (ExS.seq_cont (ExS.ite (bc := true) hne (by simp [truthy_boolVal, hocc])
      ExS.cont)), Or.inr rfl, by rw [hc]; simpa using hb, by rw [hc]; simpa using hf, Frame.refl _ _ _, hro,
      fun x a b _ _ _ => hB x a b⟩
  · have hoc : bb p (r * 9 + col) = 0 := by omega
    obtain ⟨sC, eM, hCm, hCro, hC16, hCo⟩ := mask_spec (s := sB) (c := c) (pfm := pfm) (act := act) (r := r)
      (col := col) (by omega) hr hcol (by rw [hB 1 (by decide) (by decide)]; exact h1)
      (by rw [hB 5 (by decide) (by decide)]; exact h5) (by rw [hB 6 (by decide) (by decide)]; exact h6)
      (by rw [hB 12 (by decide) (by decide)]; exact h12) (by rw [hB 13 (by decide) (by decide)]; exact h13) hpfm
    let pf := decide (pfm &&& 2 ^ col ≠ 0)
    have ha : allowedC act pf c r < 128 := Nat.lt_of_le_of_lt (allowedC_le _ _ _ _) hact
    have hCx : ∀ x, x ≠ 14 → x ≠ 15 → x ≠ 16 → sC.locals x = s.locals x := fun x a b d => by
      rw [hCo x d, hB x a b]
    obtain ⟨sD, eD, hbD, hfD, hfrD, hroD, hlD⟩ := bit_loop (to := r * 9 + col) (by omega) 8
      (allowedC act pf c r) sC L n ha (bits_done ⟨_, ha⟩)
      (by rw [hCo 14 (by decide)]; exact hB14) hC16
      (by rw [hCx 2 (by decide) (by decide) (by decide)]; exact h2)
      (by rw [hCx 3 (by decide) (by decide) (by decide)]; exact h3)
      (by rw [hCx 4 (by decide) (by decide) (by decide)]; exact h4)
      (by rw [hCro]; exact hro) (by rw [hCm]; exact hb) (by rw [hCm]; exact hf) (by omega)
    have hbits := allowed_bits c ⟨act, hact⟩ pf ⟨r, hr⟩
    simp only at hbits
    have hc : cellOut p c act pfm r col = (allowedS act pf c r).map (dmBytes (r * 9 + col)) := by
      simp [cellOut, hoc, pf]
    refine ⟨sD, .normal, ExS.seq eS (ExS.seq (ExS.ite (bc := false) hne (by simp [truthy_boolVal, hoc]) ExS.skip)
      (eM eD)), Or.inl rfl, ?_, ?_, ?_, hroD, ?_⟩
    · rw [hc, ← hbits]; exact hbD
    · rw [hc, ← hbits, List.length_map]; exact hfD
    · rw [hCm] at hfrD; exact hfrD
    · intro x a b d e f; rw [hlD x d e f, hCx x a b d]

theorem incr_i32 {s : State} {j k : Nat} (hk : k + 1 < 2147483648) (hv : s.locals j = some (.int IntTy.i32 k)) :
    ExS Gen.prog s (.set j (.cast ⟨32, true⟩ (.bin .add (some ⟨32, true⟩) (.cast ⟨32, true⟩ (.var j))
      (.const (.int ⟨32, true⟩ 1))))) .normal { s with locals := s.locals.upd j (.int IntTy.i32 (k + 1)) } := by
  have hv' : s.locals j = some (i32 (k : Int)) := by rw [hv, i32_nat k (by omega)]
  have := ExS.set (p := Gen.prog) (i := j) (s := s) (EvE.cast (EvE.bin (EvE.cast (EvE.var hv')
    (cast_i32 k (by omega) (by omega))) (EvE.const (.int ⟨32, true⟩ 1))
    (add_i32 (k : Int) 1 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)))
    (cast_i32 _ (by omega) (by omega)))
  rw [show ((k : Int) + 1) = ((k + 1 : Nat) : Int) by omega, i32_nat (k + 1) (by omega)] at this
  exact this

def colsOut (p : Position) (c : Color) (act pfm r col d : Nat) : List (List UInt8) :=
  (List.range' col d).flatMap (cellOut p c act pfm r)

theorem body3_eq : body3 = .ite (.bin .lt (some ⟨32, true⟩) (.var 13) (.const (.int ⟨32, true⟩ 9))) cellStmt .brk := rfl

theorem col_loop {p : Position} {c : Color} {act pfm r mb mo cb co cap : Nat}
    (hact : act < 128) (hpfm : pfm < 2 ^ 32) (hr : r < 9) (hpm : posBlock ≠ mb) (hpc : posBlock ≠ cb) :
    ∀ d col (s : State) (L : List (List UInt8)) n, col + d = 9 →
      s.locals 0 = some (posPtr' posBlock) → s.locals 1 = some (.int IntTy.u32 c.idx) →
      s.locals 2 = some (.ptr mb mo) → s.locals 3 = some (.ptr cb co) →
      s.locals 4 = some (.int IntTy.u64 cap) →
      s.locals 5 = some (.int IntTy.u32 pfm) → s.locals 6 = some (.int IntTy.u32 act) →
      s.locals 12 = some (.int IntTy.i32 r) → s.locals 13 = some (.int IntTy.i32 col) →
      s.mem posBlock = some (encode p) → s.ro = false →
      Buf s.mem mb mo cb co cap L → Fresh s.mem n → n + 16 * d < 2 ^ 64 →
      ∃ s', ExS Gen.prog s (.loop body3 step3) .normal s' ∧
        Buf s'.mem mb mo cb co cap (L ++ colsOut p c act pfm r col d) ∧
        Fresh s'.mem (n + 2 * (colsOut p c act pfm r col d).length) ∧ Frame s.mem s'.mem mb cb ∧
        s'.ro = false ∧
        ∀ x, x ≠ 13 → x ≠ 14 → x ≠ 15 → x ≠ 16 → x ≠ 17 → x ≠ 18 → s'.locals x = s.locals x := by
  intro d
  induction d with
  | zero =>
    intro col s L n hd h0 h1 h2 h3 h4 h5 h6 h12 h13 hm hro hb hf _
    have : col = 9 := by omega
    subst this
    refine ⟨s, ExS.loop_brk (ExS.ite (bc := false) (vc := boolVal false) (EvE_of_eval (n := 4) ?_) rfl ExS.brk),
      by simpa [colsOut] using hb, by simpa [colsOut] using hf, Frame.refl _ _ _, hro, fun _ _ _ _ _ _ _ => rfl⟩
    simp [evalExpr, h13, evalBin, isPtr, evalBinInt, binInt, intOf, IntTy.i32, IntTy.toInt, Res.bind]
  | succ d ih =>
    intro col s L n hd h0 h1 h2 h3 h4 h5 h6 h12 h13 hm hro hb hf h64
    have hcol : col < 9 := by omega
    have hcond : EvE Gen.prog s (.bin .lt (some ⟨32, true⟩) (.var 13) (.const (.int ⟨32, true⟩ 9)))
        (boolVal true) := by
      apply EvE_of_eval (n := 4)
      simp [evalExpr, h13, evalBin, isPtr, evalBinInt, binInt, intOf, IntTy.i32, IntTy.toInt, Res.bind,
        show ¬ (2147483648 ≤ col) by omega]
      rw [decide_eq_true (by omega : (col : Int) < 9)]
    obtain ⟨s1, o, e1, ho, hb1, hf1, hfr1, hro1, hl1⟩ := cell_spec (p := p) (c := c) (act := act) (pfm := pfm)
      (r := r) (col := col) hact hpfm hr hcol h0 h1 h2 h3 h4 h5 h6 h12 h13 hm hro hb hf (by omega)
    have hlen := cellOut_length p c act pfm r col
    have hl1' : ∀ x, x ≠ 13 → x ≠ 14 → x ≠ 15 → x ≠ 16 → x ≠ 17 → x ≠ 18 → s1.locals x = s.locals x :=
      fun x a b c d e f => hl1 x b c d e f
    let s2 : State := { s1 with locals := s1.locals.upd 13 (.int IntTy.i32 (col + 1)) }
    have es : ExS Gen.prog s1 step3 .normal s2 :=
      incr_i32 (by omega) (by rw [hl1 13 (by decide) (by decide) (by decide) (by decide) (by decide)]; exact h13)
    have hl2 : ∀ x, x ≠ 13 → x ≠ 14 → x ≠ 15 → x ≠ 16 → x ≠ 17 → x ≠ 18 → s2.locals x = s.locals x :=
      fun x a b c d e f => by simp [s2, Locals.upd, a]; exact hl1' x a b c d e f
    obtain ⟨s', e', hb', hf', hfr', hro', hl'⟩ := ih (col + 1) s2 _ _ (by omega)
      (by rw [hl2 0 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact h0)
      (by rw [hl2 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact h1)
      (by rw [hl2 2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact h2)
      (by rw [hl2 3 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact h3)
      (by rw [hl2 4 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact h4)
      (by rw [hl2 5 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact h5)
      (by rw [hl2 6 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact h6)
      (by rw [hl2 12 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact h12)
      (by simp [s2, Locals.upd]) (hfr1.pos hpm hpc hm (posBlock_ne_zero hf.1 hm)) hro1 hb1 hf1 (by omega)
    have hout : colsOut p c act pfm r col (d + 1) = cellOut p c act pfm r col ++ colsOut p c act pfm r (col + 1) d := by
      simp [colsOut, List.range'_succ]
    refine ⟨s', ExS.loop_next (by rw [body3_eq]; exact ExS.ite (bc := true) hcond rfl e1) ho es e', ?_, ?_,
      Frame.trans hfr1 hfr', hro', ?_⟩
    · rw [hout, ← List.append_assoc]; exact hb'
    · rw [hout, List.length_append]
      rw [show n + 2 * ((cellOut p c act pfm r col).length + (colsOut p c act pfm r (col + 1) d).length) =
        n + 2 * (cellOut p c act pfm r col).length + 2 * (colsOut p c act pfm r (col + 1) d).length by omega]
      exact hf'
    · intro x a b c d e f; rw [hl' x a b c d e f, hl2 x a b c d e f]

/-! ### The row loop (`loop4`) and the whole function -/

def body4 : Stmt := .ite (.bin .lt (some ⟨32, true⟩) (.var 12) (.const (.int ⟨32, true⟩ 9)))
  (.seq (.set 13 (.const (.int ⟨32, true⟩ 0))) (.loop body3 step3)) .brk
def step4 : Stmt := (.set 12 (.cast ⟨32, true⟩ (.bin .add (some ⟨32, true⟩) (.cast ⟨32, true⟩ (.var 12)) (.const (.int ⟨32, true⟩ 1)))))

theorem add_pseudo_drops_loop4_eq : Gen.add_pseudo_drops_loop4 = .loop body4 step4 := rfl

def rowsOut (p : Position) (c : Color) (act pfm r d : Nat) : List (List UInt8) :=
  (List.range' r d).flatMap (fun r => colsOut p c act pfm r 0 9)

theorem colsOut_length (p : Position) (c : Color) (act pfm r col : Nat) :
    ∀ d, (colsOut p c act pfm r col d).length ≤ 7 * d := by
  intro d; induction d generalizing col with
  | zero => simp [colsOut]
  | succ d ih =>
    have := ih (col + 1); have h := cellOut_length p c act pfm r col
    simp only [colsOut, List.range'_succ, List.flatMap_cons, List.length_append] at this ⊢
    omega

theorem row_loop {p : Position} {c : Color} {act pfm mb mo cb co cap : Nat}
    (hact : act < 128) (hpfm : pfm < 2 ^ 32) (hpm : posBlock ≠ mb) (hpc : posBlock ≠ cb) :
    ∀ d r (s : State) (L : List (List UInt8)) n, r + d = 9 →
      s.locals 0 = some (posPtr' posBlock) → s.locals 1 = some (.int IntTy.u32 c.idx) →
      s.locals 2 = some (.ptr mb mo) → s.locals 3 = some (.ptr cb co) →
      s.locals 4 = some (.int IntTy.u64 cap) →
      s.locals 5 = some (.int IntTy.u32 pfm) → s.locals 6 = some (.int IntTy.u32 act) →
      s.locals 12 = some (.int IntTy.i32 r) →
      s.mem posBlock = some (encode p) → s.ro = false →
      Buf s.mem mb mo cb co cap L → Fresh s.mem n → n + 144 * d < 2 ^ 64 →
      ∃ s', ExS Gen.prog s (.loop body4 step4) .normal s' ∧
        Buf s'.mem mb mo cb co cap (L ++ rowsOut p c act pfm r d) ∧
        Fresh s'.mem (n + 2 * (rowsOut p c act pfm r d).length) ∧ Frame s.mem s'.mem mb cb ∧
        s'.ro = false := by
  intro d
  induction d with
  | zero =>
    intro r s L n hd h0 h1 h2 h3 h4 h5 h6 h12 hm hro hb hf _
    have : r = 9 := by omega
    subst this
    refine ⟨s, ExS.loop_brk (ExS.ite (bc := false) (vc := boolVal false) (EvE_of_eval (n := 4) ?_) rfl ExS.brk),
      by simpa [rowsOut] using hb, by simpa [rowsOut] using hf, Frame.refl _ _ _, hro⟩
    simp [evalExpr, h12, evalBin, isPtr, evalBinInt, binInt, intOf, IntTy.i32, IntTy.toInt, Res.bind]
  | succ d ih =>
    intro r s L n hd h0 h1 h2 h3 h4 h5 h6 h12 hm hro hb hf h64
    have hr : r < 9 := by omega
    have hcond : EvE Gen.prog s (.bin .lt (some ⟨32, true⟩) (.var 12) (.const (.int ⟨32, true⟩ 9)))
        (boolVal true) := by
      apply EvE_of_eval (n := 4)
      simp [evalExpr, h12, evalBin, isPtr, evalBinInt, binInt, intOf, IntTy.i32, IntTy.toInt, Res.bind,
        show ¬ (2147483648 ≤ r) by omega]
      rw [decide_eq_true (by omega : (r : Int) < 9)]
    let s0 : State := { s with locals := s.locals.upd 13 (.int IntTy.i32 0) }
    have e0 : ExS Gen.prog s (.set 13 (.const (.int ⟨32, true⟩ 0))) .normal s0 := ExS.set (EvE.const _)
    have hs0 : ∀ x, x ≠ 13 → s0.locals x = s.locals x := fun x hx => by simp [s0, Locals.upd, hx]
    obtain ⟨s1, e1, hb1, hf1, hfr1, hro1, hl1⟩ := col_loop (p := p) (c := c) (act := act) (pfm := pfm) (r := r)
      hact hpfm hr hpm hpc 9 0 s0 L n (by omega)
      (by rw [hs0 0 (by decide)]; exact h0) (by rw [hs0 1 (by decide)]; exact h1)
      (by rw [hs0 2 (by decide)]; exact h2) (by rw [hs0 3 (by decide)]; exact h3)
      (by rw [hs0 4 (by decide)]; exact h4) (by rw [hs0 5 (by decide)]; exact h5)
      (by rw [hs0 6 (by decide)]; exact h6) (by rw [hs0 12 (by decide)]; exact h12)
      (by simp [s0, Locals.upd]) hm hro hb hf (by omega)
    have hlen := colsOut_length p c act pfm r 0 9
    have hl1' : ∀ x, x ≠ 13 → x ≠ 14 → x ≠ 15 → x ≠ 16 → x ≠ 17 → x ≠ 18 → s1.locals x = s.locals x :=
      fun x a b c d e f => by rw [hl1 x a b c d e f, hs0 x a]
    let s2 : State := { s1 with locals := s1.locals.upd 12 (.int IntTy.i32 (r + 1)) }
    have es : ExS Gen.prog s1 step4 .normal s2 :=
      incr_i32 (by omega) (by
        rw [hl1' 12 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact h12)
    have hl2 : ∀ x, x ≠ 12 → x ≠ 13 → x ≠ 14 → x ≠ 15 → x ≠ 16 → x ≠ 17 → x ≠ 18 → s2.locals x = s.locals x :=
      fun x z a b c d e f => by simp [s2, Locals.upd, z]; exact hl1' x a b c d e f
    obtain ⟨s', e', hb', hf', hfr', hro'⟩ := ih (r + 1) s2 _ _ (by omega)
      (by rw [hl2 0 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact h0)
      (by rw [hl2 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact h1)
      (by rw [hl2 2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact h2)
      (by rw [hl2 3 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact h3)
      (by rw [hl2 4 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact h4)
      (by rw [hl2 5 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact h5)
      (by rw [hl2 6 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact h6)
      (by simp [s2, Locals.upd]) (hfr1.pos hpm hpc hm (posBlock_ne_zero hf.1 hm)) hro1 hb1 hf1 (by omega)
    have hout : rowsOut p c act pfm r (d + 1) = colsOut p c act pfm r 0 9 ++ rowsOut p c act pfm (r + 1) d := by
      simp [rowsOut, List.range'_succ]
    refine ⟨s', ExS.loop_next (ExS.ite (bc := true) hcond rfl (ExS.seq e0 e1)) (Or.inl rfl) es e', ?_, ?_,
      Frame.trans hfr1 hfr', hro'⟩
    · rw [hout, ← List.append_assoc]; exact hb'
    · rw [hout, List.length_append]
      rw [show n + 2 * ((colsOut p c act pfm r 0 9).length + (rowsOut p c act pfm (r + 1) d).length) =
        n + 2 * (colsOut p c act pfm r 0 9).length + 2 * (rowsOut p c act pfm (r + 1) d).length by omega]
      exact hf'

/-- Bytes of `add_pseudo_drops(position, color, ...)`: nothing if the hand is
    empty, else per square (row-major) the drops allowed there. -/
def dropsC (p : Position) (c : Color) : List (List UInt8) :=
  if actUpTo p c 7 = 0 then []
  else rowsOut p c (actUpTo p c 7) (pawnUpTo p (Piece.code ⟨c, .pawn⟩) 81) 0 9

theorem rowsOut_length (p : Position) (c : Color) (act pfm r : Nat) :
    ∀ d, (rowsOut p c act pfm r d).length ≤ 63 * d := by
  intro d; induction d generalizing r with
  | zero => simp [rowsOut]
  | succ d ih =>
    have := ih (r + 1); have h := colsOut_length p c act pfm r 0 9
    simp only [rowsOut, List.range'_succ, List.flatMap_cons, List.length_append] at this ⊢
    omega

theorem pawn_code_lt (c : Color) : Piece.code ⟨c, .pawn⟩ < 256 := by cases c <;> decide

theorem add_pseudo_drops_spec {p : Position} {c : Color} {m : Mem} {mb mo cb co cap n : Nat}
    {L : List (List UInt8)} (hbuf : Buf m mb mo cb co cap L) (hf : Fresh m n) (h64 : n + 1296 < 2 ^ 64)
    (hm : m posBlock = some (encode p)) (hpm : posBlock ≠ mb) (hpc : posBlock ≠ cb) :
    ∃ s' o, ExS Gen.prog ⟨frameLocals Gen.add_pseudo_drops.params
        [posPtr' posBlock, .int IntTy.u32 c.idx, .ptr mb mo, .ptr cb co, .int IntTy.u64 cap], m, false⟩
      Gen.add_pseudo_drops.body o s' ∧ (o = .normal ∨ o = .ret none) ∧
      Buf s'.mem mb mo cb co cap (L ++ dropsC p c) ∧
      Fresh s'.mem (n + 2 * (dropsC p c).length) ∧ Frame m s'.mem mb cb := by
  let s0 : State := ⟨frameLocals Gen.add_pseudo_drops.params
    [posPtr' posBlock, .int IntTy.u32 c.idx, .ptr mb mo, .ptr cb co, .int IntTy.u64 cap], m, false⟩
  let K := Piece.code ⟨c, .pawn⟩
  have hK : K < 256 := pawn_code_lt c
  let sa : State := { s0 with locals := s0.locals.upd 5 (.int IntTy.u32 0) }
  let sb : State := { sa with locals := sa.locals.upd 6 (.int IntTy.u32 0) }
  let sc : State := { sb with locals := sb.locals.upd 8 (u8 K) }
  let sd : State := { sc with locals := sc.locals.upd 7 (u8 K) }
  let se : State := { sd with locals := sd.locals.upd 9 (.int IntTy.u32 0) }
  have z32 : EvE Gen.prog s0 (.cast ⟨32, false⟩ (.const (.int ⟨32, true⟩ 0))) (.int IntTy.u32 0) :=
    EvE_of_eval (n := 3) (by simp [evalExpr, evalCast, IntTy.u32, IntTy.toInt, Res.bind, IntTy.wrap, IntTy.modulus])
  have ea : ExS Gen.prog s0 (.set 5 (.cast ⟨32, false⟩ (.const (.int ⟨32, true⟩ 0)))) .normal sa := ExS.set z32
  have eb : ExS Gen.prog sa (.set 6 (.cast ⟨32, false⟩ (.const (.int ⟨32, true⟩ 0)))) .normal sb :=
    ExS.set (EvE_of_eval (n := 3) (by simp [evalExpr, evalCast, IntTy.u32, IntTy.toInt, Res.bind, IntTy.wrap, IntTy.modulus]))
  have hpawn : run Gen.fid_shogi_piece [u32 c.idx, u32 1] = some (some (u8 K)) := by
    cases c <;> decide +kernel
  have ec : ExS Gen.prog sb (.seq (.call (some 8) 0 [(.var 1), (.cast ⟨32, false⟩ (.const (.int ⟨32, true⟩ 1)))])
      (.set 7 (.var 8))) .normal sd :=
    ExS.seq (call_pure rfl rfl rfl rfl hpawn (EvArgs.cons (EvE.var rfl) (EvArgs.cons
      (EvE_of_eval (n := 3) (by simp [evalExpr, evalCast, IntTy.u32, IntTy.toInt, Res.bind, u32, IntTy.wrap, IntTy.modulus])) EvArgs.nil)))
      (ExS.set (EvE.var (by simp [sc, Locals.upd])))
  have ee : ExS Gen.prog sd (.set 9 (.cast ⟨32, false⟩ (.const (.int ⟨32, true⟩ 0)))) .normal se :=
    ExS.set (EvE_of_eval (n := 3) (by simp [evalExpr, evalCast, IntTy.u32, IntTy.toInt, Res.bind, IntTy.wrap, IntTy.modulus]))
  obtain ⟨sf, ef, hfm, hfro, hf6, hfo⟩ := hand_loop p c 7 0 se rfl rfl rfl (by simp [se, Locals.upd])
    (by simp [se, sd, sc, sb, Locals.upd, actUpTo]) hm
  have hfx : ∀ x, x ≠ 5 → x ≠ 6 → x ≠ 7 → x ≠ 8 → x ≠ 9 → sf.locals x = s0.locals x := fun x a b c d e => by
    rw [hfo x b e]; simp [se, sd, sc, sb, sa, Locals.upd, a, b, c, d, e]
  let act := actUpTo p c 7
  have hact : act < 128 := actUpTo_lt p c 7
  have hcz : EvE Gen.prog sf (.bin .eq (some ⟨32, false⟩) (.var 6) (.cast ⟨32, false⟩ (.const (.int ⟨32, true⟩ 0))))
      (boolVal (decide (act = 0))) := by
    apply EvE_of_eval (n := 4)
    simp [evalExpr, hf6, evalCast, evalBin, isPtr, evalBinInt, binInt, intOf, IntTy.u32, IntTy.toInt, Res.bind, act, IntTy.wrap, IntTy.modulus]
  have pre : ∀ {rest o s'}, ExS Gen.prog sf rest o s' → ExS Gen.prog s0 (.seq (.set 5 (.cast ⟨32, false⟩
      (.const (.int ⟨32, true⟩ 0)))) (.seq (.set 6 (.cast ⟨32, false⟩ (.const (.int ⟨32, true⟩ 0))))
      (.seq (.seq (.call (some 8) 0 [(.var 1), (.cast ⟨32, false⟩ (.const (.int ⟨32, true⟩ 1)))]) (.set 7 (.var 8)))
      (.seq (.seq (.set 9 (.cast ⟨32, false⟩ (.const (.int ⟨32, true⟩ 0)))) Gen.add_pseudo_drops_loop0) rest)))) o s' :=
    fun h => ExS.seq ea (ExS.seq eb (ExS.seq ec (ExS.seq (ExS.seq ee ef) h)))
  by_cases ha0 : act = 0
  · have hd : dropsC p c = [] := by simp [dropsC, ha0, act] at *
    refine ⟨sf, .ret none, pre (ExS.seq_ret (ExS.ite (bc := true) hcz (by simp [truthy_boolVal, ha0])
      ExS.ret_none)), Or.inr rfl, ?_, ?_, ?_⟩
    · rw [hd, hfm]; simpa using hbuf
    · rw [hd, hfm]; simpa using hf
    · rw [hfm]; exact Frame.refl _ _ _
  · let sg : State := { sf with locals := sf.locals.upd 10 (.int IntTy.i32 0) }
    have hg : ∀ x, x ≠ 10 → sg.locals x = sf.locals x := fun x hx => by simp [sg, Locals.upd, hx]
    obtain ⟨sh, eh, hhm, hhro, hh5, hho⟩ := pawn_loop p K hK 81 0 sg rfl
      (by rw [hg 0 (by decide), hfx 0 (by decide) (by decide) (by decide) (by decide) (by decide)]; rfl)
      (by rw [hg 7 (by decide), hfo 7 (by decide) (by decide)]; simp [se, sd, Locals.upd, u8])
      (by simp [sg, Locals.upd])
      (by rw [hg 5 (by decide), hfo 5 (by decide) (by decide)]; simp [se, sd, sc, sb, sa, Locals.upd, pawnUpTo])
      (by simp [sg]; rw [hfm]; exact hm)
    let pfm := pawnUpTo p K 81
    have hpfm : pfm < 2 ^ 32 := Nat.lt_of_lt_of_le (pawnUpTo_lt p K 81) (by decide)
    let si : State := { sh with locals := sh.locals.upd 12 (.int IntTy.i32 0) }
    have hi : ∀ x, x ≠ 5 → x ≠ 6 → x ≠ 7 → x ≠ 8 → x ≠ 9 → x ≠ 10 → x ≠ 11 → x ≠ 12 →
        si.locals x = s0.locals x := fun x a b c d e f g h => by
      simp [si, Locals.upd, h]; rw [hho x a f g, hg x f, hfx x a b c d e]
    have hmi : si.mem = m := by simp [si]; rw [hhm]; simp [sg]; rw [hfm]
    obtain ⟨s', e', hb', hf', hfr', _⟩ := row_loop (p := p) (c := c) (act := act) (pfm := pfm) hact hpfm hpm hpc
      9 0 si L n rfl
      (by rw [hi 0 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; rfl)
      (by rw [hi 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; rfl)
      (by rw [hi 2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; rfl)
      (by rw [hi 3 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; rfl)
      (by rw [hi 4 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; rfl)
      (by simp only [si, Locals.upd]; simp; exact hh5)
      (by simp only [si, Locals.upd]; simp; rw [hho 6 (by decide) (by decide) (by decide), hg 6 (by decide)]; exact hf6)
      (by simp [si, Locals.upd]) (by rw [hmi]; exact hm) (by simp [si]; rw [hhro]; simp [sg]; rw [hfro])
      (by rw [hmi]; exact hbuf) (by rw [hmi]; exact hf) (by omega)
    have hd : dropsC p c = rowsOut p c act pfm 0 9 := by simp [dropsC, act, pfm, K] at ha0 ⊢; simp [ha0]
    refine ⟨s', .normal, pre (ExS.seq (ExS.ite (bc := false) hcz (by simp [truthy_boolVal, ha0]) ExS.skip)
      (ExS.seq (ExS.seq (ExS.set (EvE.const _)) eh) (ExS.seq (ExS.set (EvE.const _)) e'))), Or.inl rfl, ?_, ?_, ?_⟩
    · rw [hd]; exact hb'
    · rw [hd]; exact hf'
    · rw [hmi] at hfr'; exact hfr'
