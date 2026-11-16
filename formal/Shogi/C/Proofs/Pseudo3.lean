/-
  T7 generators, layer 3: `generate_pseudo_for_color`, part 3 — the king's
  nested `dr`/`dc` loops.
-/
import Shogi.C.Proofs.Pseudo2

namespace Shogi.C.Proofs
open MiniC Shogi Shogi.C

def kRow (dr : Int) : Nat → Int → List Op
  | 0, _ => []
  | d + 1, dc => (if dr ≠ 0 ∨ dc ≠ 0 then [Op.step dr dc] else []) ++ kRow dr d (dc + 1)

def kAll : Nat → Int → List Op
  | 0, _ => []
  | d + 1, dr => kRow dr 3 (-1) ++ kAll d (dr + 1)

def kingOps : List Op := kAll 3 (-1)

def kBody : Stmt := (.ite (.bin .le (some ⟨32, true⟩) (.var 20) (.const (.int ⟨32, true⟩ 1))) (.ite (.lor (.bin .ne (some ⟨32, true⟩) (.var 19) (.const (.int ⟨32, true⟩ 0))) (.bin .ne (some ⟨32, true⟩) (.var 20) (.const (.int ⟨32, true⟩ 0)))) (.call none 24 [(.var 0), (.var 16), (.var 19), (.var 20), (.var 2), (.var 3), (.var 4)]) .skip) .brk)
def kStep (j : Nat) : Stmt := (.set j (.cast ⟨32, true⟩ (.bin .add (some ⟨32, true⟩) (.cast ⟨32, true⟩ (.var j)) (.const (.int ⟨32, true⟩ 1)))))

theorem loop0_eq : Gen.generate_pseudo_for_color_loop0 = .loop kBody (kStep 20) := rfl

def kOuter : Stmt := (.ite (.bin .le (some ⟨32, true⟩) (.var 19) (.const (.int ⟨32, true⟩ 1))) (.seq (.set 20 (.un .neg ⟨32, true⟩ (.const (.int ⟨32, true⟩ 1)))) (.loop kBody (kStep 20))) .brk)

theorem loop1_eq : Gen.generate_pseudo_for_color_loop1 = .loop kOuter (kStep 19) := rfl

theorem incr_i32z {s : State} {j : Nat} {k : Int} (h1 : -2147483648 ≤ k) (h2 : k + 1 < 2147483648)
    (hv : s.locals j = some (i32 k)) :
    ExS Gen.prog s (kStep j) .normal { s with locals := s.locals.upd j (i32 (k + 1)) } :=
  ExS.set (EvE.cast (EvE.bin (EvE.cast (EvE.var hv) (cast_i32 k h1 (by omega))) (EvE.const (.int ⟨32, true⟩ 1))
    (add_i32 k 1 (by omega) h2 h1 (by omega) (by omega) (by omega))) (cast_i32 _ (by omega) h2))

theorem ev_le1 {s : State} {j : Nat} {k : Int} (h1 : -2147483648 ≤ k) (h2 : k < 2147483648)
    (hv : s.locals j = some (i32 k)) :
    EvE Gen.prog s (.bin .le (some ⟨32, true⟩) (.var j) (.const (.int ⟨32, true⟩ 1))) (boolVal (decide (k ≤ 1))) := by
  apply EvE_of_eval (n := 4)
  simp [evalExpr, hv, evalBin, isPtr, evalBinInt, binInt, intOf, i32, IntTy.i32, Res.bind, toInt_wrap32 k h1 h2]
  rfl

theorem ev_ne0z {s : State} {j : Nat} {k : Int} (h1 : -2147483648 ≤ k) (h2 : k < 2147483648)
    (hv : s.locals j = some (i32 k)) :
    EvE Gen.prog s (.bin .ne (some ⟨32, true⟩) (.var j) (.const (.int ⟨32, true⟩ 0))) (boolVal (decide (k ≠ 0))) := by
  apply EvE_of_eval (n := 4)
  simp [evalExpr, hv, evalBin, isPtr, evalBinInt, binInt, intOf, i32, IntTy.i32, Res.bind, toInt_wrap32 k h1 h2]
  rfl

theorem ev_lor_ne {s : State} {a b : Int} (ha1 : -2147483648 ≤ a) (ha2 : a < 2147483648)
    (hb1 : -2147483648 ≤ b) (hb2 : b < 2147483648)
    (h19 : s.locals 19 = some (i32 a)) (h20 : s.locals 20 = some (i32 b)) :
    EvE Gen.prog s (.lor (.bin .ne (some ⟨32, true⟩) (.var 19) (.const (.int ⟨32, true⟩ 0)))
      (.bin .ne (some ⟨32, true⟩) (.var 20) (.const (.int ⟨32, true⟩ 0)))) (boolVal (decide (a ≠ 0 ∨ b ≠ 0))) := by
  apply EvE_of_eval (n := 4)
  by_cases h : a = 0 <;> by_cases h' : b = 0 <;>
  simp [evalExpr, h19, h20, evalBin, isPtr, evalBinInt, binInt, intOf, i32, IntTy.i32, Res.bind,
    toInt_wrap32 a ha1 ha2, toInt_wrap32 b hb1 hb2, truthy, boolVal, h, h', pure]
  all_goals simp_all [IntTy.toInt, IntTy.wrap, IntTy.modulus]

section king
variable {p : Position} {sb fr pc mb mo cb co cap row col : Nat} {c : Color}
    {t : PieceType} {cp iz : Bool}

theorem king_inner (hrow : row < 9) (hcol : col < 9) (hfr : fr < 256) (hpc : pc < 256)
    (hsb0 : sb ≠ 0) (hsbm : sb ≠ mb) (hsbc : sb ≠ cb) (hpm : posBlock ≠ mb) (hpc' : posBlock ≠ cb)
    (dr : Int) (hdr : -1 ≤ dr ∧ dr ≤ 1) :
    ∀ (d : Nat) (dc : Int) (s : State) (L : List (List UInt8)) (n : Nat), dc + d = 2 → -1 ≤ dc →
      Buf s.mem mb mo cb co cap L → Fresh s.mem n → n + 36 * d < 2 ^ 64 →
      s.mem sb = some (srcBytes fr pc c t row col cp iz) → s.mem posBlock = some (encode p) → s.ro = false →
      s.locals 0 = some posPtr → s.locals 16 = some (.ptr sb 0) →
      s.locals 2 = some (.ptr mb mo) → s.locals 3 = some (.ptr cb co) →
      s.locals 4 = some (.int IntTy.u64 cap) → s.locals 19 = some (i32 dr) → s.locals 20 = some (i32 dc) →
      ∃ s', ExS Gen.prog s (.loop kBody (kStep 20)) .normal s' ∧ s'.ro = s.ro ∧
        (∀ x, x ≠ 20 → s'.locals x = s.locals x) ∧
        Buf s'.mem mb mo cb co cap (L ++ (kRow dr d dc).flatMap (opOut p c t fr pc row col cp iz)) ∧
        Fresh s'.mem (n + 2 * ((kRow dr d dc).flatMap (opOut p c t fr pc row col cp iz)).length) ∧
        Frame s.mem s'.mem mb cb := by
  intro d
  induction d with
  | zero =>
    intro dc s L n hd _ hb hf _ _ _ _ _ _ _ _ _ _ h20
    have hc := ev_le1 (by omega) (by omega) h20
    refine ⟨s, ExS.loop_brk (ExS.ite (bc := false) hc (by simp [truthy_boolVal]; omega) ExS.brk), rfl,
      fun _ _ => rfl, by simpa [kRow] using hb, by simpa [kRow] using hf, Frame.refl _ _ _⟩
  | succ d ih =>
    intro dc s L n hd hdc hb hf h64 hsb hm hro a0 a16 a2 a3 a4 h19 h20
    have hc := ev_le1 (by omega) (by omega) h20
    have hl := ev_lor_ne (by omega) (by omega) (by omega) (by omega) h19 h20
    -- the body: maybe one add_step call
    obtain ⟨s1, e1, hl1, hro1, hb1, hf1, hfr1⟩ : ∃ s1, ExS Gen.prog s kBody .normal s1 ∧ s1.locals = s.locals ∧
        s1.ro = s.ro ∧
        Buf s1.mem mb mo cb co cap (L ++ (if dr ≠ 0 ∨ dc ≠ 0 then [Op.step dr dc] else []).flatMap
          (opOut p c t fr pc row col cp iz)) ∧
        Fresh s1.mem (n + 2 * ((if dr ≠ 0 ∨ dc ≠ 0 then [Op.step dr dc] else []).flatMap
          (opOut p c t fr pc row col cp iz)).length) ∧ Frame s.mem s1.mem mb cb := by
      by_cases hz : dr ≠ 0 ∨ dc ≠ 0
      · obtain ⟨s1, e, hl1, hro1, hb1, hf1, hfr1⟩ := op_call (p := p) (Op.step dr dc) (edr := .var 19)
          (edc := .var 20) (by simp only [Op.ok]; omega) hrow hcol hb hf (by omega) hsb hfr hpc hm hsb0 hsbm hsbc
          hpm hpc' hro a0 a16 (EvE.var h19) (EvE.var h20) a2 a3 a4
        refine ⟨s1, ExS.ite (bc := true) hc (by simp [truthy_boolVal]; omega)
          (ExS.ite (bc := true) hl (by simp [truthy_boolVal, hz]) e), hl1, hro1, ?_, ?_, hfr1⟩
        · simpa [hz] using hb1
        · simpa [hz] using hf1
      · refine ⟨s, ExS.ite (bc := true) hc (by simp [truthy_boolVal]; omega)
          (ExS.ite (bc := false) hl (by simp [truthy_boolVal, hz]) ExS.skip), rfl, rfl, ?_, ?_, Frame.refl _ _ _⟩
        · simpa [hz] using hb
        · simpa [hz] using hf
    have hlen : ((if dr ≠ 0 ∨ dc ≠ 0 then [Op.step dr dc] else []).flatMap
        (opOut p c t fr pc row col cp iz)).length ≤ 18 := by
      split
      · simpa using opOut_length p c t fr pc row col cp iz (Op.step dr dc)
      · simp
    let s2 : State := { s1 with locals := s1.locals.upd 20 (i32 (dc + 1)) }
    have es : ExS Gen.prog s1 (kStep 20) .normal s2 := incr_i32z (by omega) (by omega) (by rw [hl1]; exact h20)
    have hl2 : ∀ x, x ≠ 20 → s2.locals x = s.locals x := fun x hx => by simp [s2, Locals.upd, hx, hl1]
    obtain ⟨s', e', hro', hl', hb', hf', hfr'⟩ := ih (dc + 1) s2 _ _ (by omega) (by omega) hb1 hf1 (by omega)
      (hfr1.keep hsb0 hsbm hsbc hsb) (hfr1.pos hpm hpc' hm) (by simp [s2]; rw [hro1]; exact hro)
      (by rw [hl2 0 (by decide)]; exact a0) (by rw [hl2 16 (by decide)]; exact a16)
      (by rw [hl2 2 (by decide)]; exact a2) (by rw [hl2 3 (by decide)]; exact a3)
      (by rw [hl2 4 (by decide)]; exact a4) (by rw [hl2 19 (by decide)]; exact h19) (by simp [s2, Locals.upd])
    refine ⟨s', ExS.loop_next e1 (Or.inl rfl) es e', by rw [hro']; simp [s2]; exact hro1,
      fun x hx => by rw [hl' x hx, hl2 x hx], ?_, ?_, Frame.trans hfr1 hfr'⟩
    · simp only [kRow, List.flatMap_append]; rw [← List.append_assoc]; exact hb'
    · simp only [kRow, List.flatMap_append, List.length_append]
      rw [show ∀ a b : Nat, n + 2 * (a + b) = n + 2 * a + 2 * b from fun a b => by omega]; exact hf'

theorem kRow_len (dr : Int) : ∀ d dc, (kRow dr d dc).length ≤ d := by
  intro d; induction d with
  | zero => intro _; simp [kRow]
  | succ d ih => intro dc; have := ih (dc + 1); simp only [kRow, List.length_append]; split <;> simp <;> omega

theorem flatMap_opOut_len (L : List Op) :
    (L.flatMap (opOut p c t fr pc row col cp iz)).length ≤ 18 * L.length := by
  induction L with
  | nil => simp
  | cons o r ih => have := opOut_length p c t fr pc row col cp iz o; simp only [List.flatMap_cons,
      List.length_append, List.length_cons]; omega

theorem king_outer (hrow : row < 9) (hcol : col < 9) (hfr : fr < 256) (hpc : pc < 256)
    (hsb0 : sb ≠ 0) (hsbm : sb ≠ mb) (hsbc : sb ≠ cb) (hpm : posBlock ≠ mb) (hpc' : posBlock ≠ cb) :
    ∀ (d : Nat) (dr : Int) (s : State) (L : List (List UInt8)) (n : Nat), dr + d = 2 → -1 ≤ dr →
      Buf s.mem mb mo cb co cap L → Fresh s.mem n → n + 108 * d < 2 ^ 64 →
      s.mem sb = some (srcBytes fr pc c t row col cp iz) → s.mem posBlock = some (encode p) → s.ro = false →
      s.locals 0 = some posPtr → s.locals 16 = some (.ptr sb 0) →
      s.locals 2 = some (.ptr mb mo) → s.locals 3 = some (.ptr cb co) →
      s.locals 4 = some (.int IntTy.u64 cap) → s.locals 19 = some (i32 dr) →
      ∃ s', ExS Gen.prog s (.loop kOuter (kStep 19)) .normal s' ∧ s'.ro = s.ro ∧
        (∀ x, x ≠ 19 → x ≠ 20 → s'.locals x = s.locals x) ∧
        Buf s'.mem mb mo cb co cap (L ++ (kAll d dr).flatMap (opOut p c t fr pc row col cp iz)) ∧
        Fresh s'.mem (n + 2 * ((kAll d dr).flatMap (opOut p c t fr pc row col cp iz)).length) ∧
        Frame s.mem s'.mem mb cb := by
  intro d
  induction d with
  | zero =>
    intro dr s L n hd _ hb hf _ _ _ _ _ _ _ _ _ h19
    have hc := ev_le1 (by omega) (by omega) h19
    refine ⟨s, ExS.loop_brk (ExS.ite (bc := false) hc (by simp [truthy_boolVal]; omega) ExS.brk), rfl,
      fun _ _ _ => rfl, by simpa [kAll] using hb, by simpa [kAll] using hf, Frame.refl _ _ _⟩
  | succ d ih =>
    intro dr s L n hd hdr hb hf h64 hsb hm hro a0 a16 a2 a3 a4 h19
    have hc := ev_le1 (by omega) (by omega) h19
    let s0 : State := { s with locals := s.locals.upd 20 (i32 (-1)) }
    have e0 : ExS Gen.prog s (.set 20 (.un .neg ⟨32, true⟩ (.const (.int ⟨32, true⟩ 1)))) .normal s0 :=
      ExS.set (EvE_of_eval (n := 3) (by simp [evalExpr, evalUn, intOf, IntTy.toInt, Res.bind, i32, IntTy.wrap,
        IntTy.modulus, arith, IntTy.inRange, IntTy.i32]; decide))
    have h0x : ∀ x, x ≠ 20 → s0.locals x = s.locals x := fun x hx => by simp [s0, Locals.upd, hx]
    obtain ⟨s1, e1, hro1, hl1, hb1, hf1, hfr1⟩ := king_inner (p := p) hrow hcol hfr hpc hsb0 hsbm hsbc hpm hpc'
      dr (by omega) 3 (-1) s0 L n (by omega) (by omega) hb hf (by omega) hsb hm hro
      (by rw [h0x 0 (by decide)]; exact a0) (by rw [h0x 16 (by decide)]; exact a16)
      (by rw [h0x 2 (by decide)]; exact a2) (by rw [h0x 3 (by decide)]; exact a3)
      (by rw [h0x 4 (by decide)]; exact a4) (by rw [h0x 19 (by decide)]; exact h19) (by simp [s0, Locals.upd])
    have hlen : ((kRow dr 3 (-1)).flatMap (opOut p c t fr pc row col cp iz)).length ≤ 54 := by
      have := flatMap_opOut_len (p := p) (c := c) (t := t) (fr := fr) (pc := pc) (row := row) (col := col)
        (cp := cp) (iz := iz) (kRow dr 3 (-1)); have := kRow_len dr 3 (-1); omega
    have hl1' : ∀ x, x ≠ 20 → s1.locals x = s.locals x := fun x hx => by rw [hl1 x hx, h0x x hx]
    let s2 : State := { s1 with locals := s1.locals.upd 19 (i32 (dr + 1)) }
    have es : ExS Gen.prog s1 (kStep 19) .normal s2 :=
      incr_i32z (by omega) (by omega) (by rw [hl1' 19 (by decide)]; exact h19)
    have hl2 : ∀ x, x ≠ 19 → x ≠ 20 → s2.locals x = s.locals x := fun x a b => by
      simp [s2, Locals.upd, a]; exact hl1' x b
    obtain ⟨s', e', hro', hl', hb', hf', hfr'⟩ := ih (dr + 1) s2 _ _ (by omega) (by omega) hb1 hf1 (by omega)
      (hfr1.keep hsb0 hsbm hsbc hsb) (hfr1.pos hpm hpc' hm) (by simp [s2]; rw [hro1]; exact hro)
      (by rw [hl2 0 (by decide) (by decide)]; exact a0) (by rw [hl2 16 (by decide) (by decide)]; exact a16)
      (by rw [hl2 2 (by decide) (by decide)]; exact a2) (by rw [hl2 3 (by decide) (by decide)]; exact a3)
      (by rw [hl2 4 (by decide) (by decide)]; exact a4) (by simp [s2, Locals.upd])
    refine ⟨s', ExS.loop_next (ExS.ite (bc := true) hc (by simp [truthy_boolVal]; omega) (ExS.seq e0 e1))
      (Or.inl rfl) es e', by rw [hro']; simp [s2]; rw [hro1],
      fun x a b => by rw [hl' x a b, hl2 x a b], ?_, ?_, Frame.trans hfr1 hfr'⟩
    · simp only [kAll, List.flatMap_append]; rw [← List.append_assoc]; exact hb'
    · simp only [kAll, List.flatMap_append, List.length_append]
      rw [show ∀ a b : Nat, n + 2 * (a + b) = n + 2 * a + 2 * b from fun a b => by omega]; exact hf'

end king

end Shogi.C.Proofs
