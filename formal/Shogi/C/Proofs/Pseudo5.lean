/-
  T7 generators, layer 3: `generate_pseudo_for_color`, part 5 — one square of
  the board loop, the loop, and the whole function.
-/
import Shogi.C.Proofs.Pseudo4

namespace Shogi.C.Proofs
variable {posBlock : Nat}
open MiniC Shogi Shogi.C

/-- What the board loop appends for square `fr`. -/
def sqOut (p : Position) (c : Color) (fr : Nat) : List (List UInt8) :=
  if h : fr < 81 then
    match p.pieceAt ⟨fr, h⟩ with
    | some q => if q.color = c then
        (cOps c.fwd q.type).flatMap (opOut p c q.type fr q.code (fr / 9) (fr % 9) q.type.canPromote
          (inZone c (fr / 9)))
      else []
    | none => []
  else []

theorem Buf.ne_fresh {m : Mem} {mb mo cb co cap n : Nat} {L : List (List UInt8)} (hb : Buf m mb mo cb co cap L)
    (hf : Fresh m n) : n ≠ mb ∧ n ≠ cb := by
  constructor
  · intro e; obtain ⟨blk, h, _⟩ := hb.buf; rw [← e, hf.2.2 n (Nat.le_refl _)] at h; cases h
  · intro e; obtain ⟨blk, h, _⟩ := hb.cnt; rw [← e, hf.2.2 n (Nat.le_refl _)] at h; cases h

theorem pos_ne_fresh {m : Mem} {n : Nat} {blk : Block} (hf : Fresh m n) (hm : m posBlock = some blk) :
    n ≠ posBlock := by
  intro e; rw [← e, hf.2.2 n (Nat.le_refl _)] at hm; cases hm

theorem fwd_cases (c : Color) : c.fwd = -1 ∨ c.fwd = 1 := by cases c <;> simp [Color.fwd]

theorem sq_body {p : Position} {c : Color} {mb mo cb co cap : Nat} (hpm : posBlock ≠ mb) (hpc : posBlock ≠ cb)
    (fr : Nat) (hfr : fr < 81) (s : State) (L : List (List UInt8)) (n : Nat)
    (hb : Buf s.mem mb mo cb co cap L) (hf : Fresh s.mem n) (h64 : n + 400 < 2 ^ 64)
    (hm : s.mem posBlock = some (encode p)) (hro : s.ro = false)
    (a0 : s.locals 0 = some (posPtr' posBlock)) (a1 : s.locals 1 = some (u32 c.idx))
    (a2 : s.locals 2 = some (.ptr mb mo)) (a3 : s.locals 3 = some (.ptr cb co))
    (a4 : s.locals 4 = some (.int IntTy.u64 cap)) (a5 : s.locals 5 = some (i32 c.fwd))
    (a6 : s.locals 6 = some (u8 fr)) :
    ∃ s' o n', ExS Gen.prog s (sqBody c.fwd) o s' ∧ (o = .normal ∨ o = .cont) ∧ s'.ro = false ∧
      (∀ x, x ≤ 6 → s'.locals x = s.locals x) ∧
      Buf s'.mem mb mo cb co cap (L ++ sqOut p c fr) ∧ Fresh s'.mem n' ∧ n' ≤ n + 400 ∧
      Frame s.mem s'.mem mb cb := by
  have hcond : EvE Gen.prog s sqCond (boolVal true) := by
    apply EvE_of_eval (n := 4)
    simp [sqCond, evalExpr, a6, evalCast, evalBin, isPtr, evalBinInt, binInt, intOf, u8, IntTy.u8, IntTy.toInt,
      IntTy.modulus, Res.bind, Nat.mod_eq_of_lt (show fr < 4294967296 by omega), show ¬ (2147483648 ≤ fr) by omega]
    rw [decide_eq_true (by omega : (fr : Int) < 81)]
  let bt := bb p fr
  have hbt : bt < 256 := bb_lt p fr
  let s1 : State := { s with locals := s.locals.upd 7 (.int IntTy.u8 bt) }
  have e1 : ExS Gen.prog s ldPiece .normal s1 := ExS.set (ev_board_u8 hfr a0 a6 hm)
  have l7 : s1.locals 7 = some (.int IntTy.u8 bt) := by simp [s1, Locals.upd]
  have hz : EvE Gen.prog s1 (.bin .eq (some ⟨32, true⟩) (.cast ⟨32, true⟩ (.var 7)) (.const (.int ⟨32, true⟩ 0)))
      (boolVal (decide (bt = 0))) := by
    apply EvE_of_eval (n := 4)
    simp [evalExpr, l7, evalCast, evalBin, isPtr, evalBinInt, binInt, intOf, IntTy.u8, IntTy.toInt,
      IntTy.modulus, Res.bind, Nat.mod_eq_of_lt (show bt < 4294967296 by omega), show ¬ (2147483648 ≤ bt) by omega]
  cases hq : p.pieceAt ⟨fr, hfr⟩ with
  | none =>
    have hb0 : bt = 0 := by simp [bt, bb, hfr, hq, pieceByte_toNat]
    let s2 : State := { s1 with locals := s1.locals.upd 9 (i32 1) }
    have e2 : ExS Gen.prog s1 skipOther .cont s2 :=
      ExS.seq (ExS.ite (bc := true) hz (by simp [truthy_boolVal, hb0]) (ExS.set (EvE.const _)))
        (ExS.ite (bc := true) (vc := .int ⟨32, true⟩ 1) (EvE.var (by simp [s2, Locals.upd, i32, IntTy.wrap, IntTy.modulus])) (by simp [truthy, i32, IntTy.wrap, IntTy.modulus])
          ExS.cont)
    have hout : sqOut p c fr = [] := by simp [sqOut, hfr, hq]
    refine ⟨s2, .cont, n, ExS.ite (bc := true) hcond rfl (ExS.seq e1 (ExS.seq_cont e2)), Or.inr rfl, hro,
      fun x hx => by simp [s2, s1, Locals.upd, show x ≠ 9 by omega, show x ≠ 7 by omega], by rw [hout]; simpa using hb, hf, by omega,
      Frame.refl _ _ _⟩
  | some q =>
    have hbq : bt = q.code := by simp [bt, bb, hfr, hq, pieceByte_toNat]
    have hcode1 : q.code ≠ 0 := by obtain ⟨qc, qt⟩ := q; cases qc <;> cases qt <;> decide
    have hpcol : run Gen.fid_shogi_piece_color [u8 q.code] = some (some (u32 q.color.idx)) := by
      obtain ⟨qc, qt⟩ := q; cases qc <;> cases qt <;> decide +kernel
    have hptyp : run Gen.fid_shogi_piece_type [u8 q.code] = some (some (u32 q.type.code)) := by
      obtain ⟨qc, qt⟩ := q; cases qc <;> cases qt <;> decide +kernel
    have l7' : s1.locals 7 = some (u8 q.code) := by rw [l7, hbq]; rfl
    let s2a : State := { s1 with locals := s1.locals.upd 8 (u32 q.color.idx) }
    let own := decide (q.color.idx ≠ c.idx)
    let s2 : State := { s2a with locals := s2a.locals.upd 9 (boolVal own) }
    have hci : q.color.idx < 2 := by cases q.color <;> decide
    have hcc : c.idx < 2 := by cases c <;> decide
    have hlor : EvE Gen.prog s2a (.lor (.const (.int ⟨32, true⟩ 0)) (.bin .ne (some ⟨32, false⟩)
        (.cast ⟨32, false⟩ (.var 8)) (.cast ⟨32, false⟩ (.var 1)))) (boolVal own) := by
      have h8 : s2a.locals 8 = some (u32 q.color.idx) := by simp [s2a, Locals.upd]
      have h1' : s2a.locals 1 = some (u32 c.idx) := by simp [s2a, s1, Locals.upd]; exact a1
      apply EvE_of_eval (n := 4)
      simp [evalExpr, h8, h1', evalCast, evalBin, isPtr, evalBinInt, binInt, intOf, u32, IntTy.u32, IntTy.modulus,
        Res.bind, truthy, boolVal, Nat.mod_eq_of_lt (show q.color.idx < 4294967296 by omega),
        Nat.mod_eq_of_lt (show c.idx < 4294967296 by omega), own, pure]
    have e2a : ExS Gen.prog s1 (.ite (.bin .eq (some ⟨32, true⟩) (.cast ⟨32, true⟩ (.var 7)) (.const (.int ⟨32, true⟩ 0)))
        (.set 9 (.const (.int ⟨32, true⟩ 1))) (.seq (.call (some 8) 1 [(.var 7)]) (.set 9 (.lor (.const (.int ⟨32, true⟩ 0))
        (.bin .ne (some ⟨32, false⟩) (.cast ⟨32, false⟩ (.var 8)) (.cast ⟨32, false⟩ (.var 1))))))) .normal s2 :=
      ExS.ite (bc := false) hz (by simp [truthy_boolVal, hbq, hcode1])
        (ExS.seq (call_pure rfl rfl rfl rfl hpcol (EvArgs.cons (EvE.var l7') EvArgs.nil)) (ExS.set hlor))
    have l9 : s2.locals 9 = some (boolVal own) := by simp [s2, Locals.upd]
    have hs2 : ∀ x, x ≠ 7 → x ≠ 8 → x ≠ 9 → s2.locals x = s.locals x := fun x a b d => by
      simp [s2, s2a, s1, Locals.upd, a, b, d]
    by_cases hown : q.color = c
    · have hown' : own = false := by simp [own, hown]
      have e2 : ExS Gen.prog s1 skipOther .normal s2 :=
        ExS.seq e2a (ExS.ite (bc := false) (EvE.var l9) (by simp [truthy_boolVal, hown']) ExS.skip)
      let R := fr / 9
      let C := fr % 9
      have hR : R < 9 := by omega
      have hC : C < 9 := by omega
      have hrowr : run Gen.fid_row_of [u8 fr] = some (some (i32 (R : Int))) := row_of_refines ⟨fr, hfr⟩
      have hcolr : run Gen.fid_col_of [u8 fr] = some (some (i32 (C : Int))) := col_of_refines ⟨fr, hfr⟩
      have l7'' : s2.locals 7 = some (u8 q.code) := by simp [s2, s2a, Locals.upd]; exact l7'
      have l6 : s2.locals 6 = some (u8 fr) := by rw [hs2 6 (by decide) (by decide) (by decide)]; exact a6
      let s3a : State := { s2 with locals := s2.locals.upd 11 (u32 q.type.code) }
      let s3 : State := { s3a with locals := s3a.locals.upd 10 (u32 q.type.code) }
      have e3 : ExS Gen.prog s2 ldType .normal s3 :=
        ExS.seq (call_pure rfl rfl rfl rfl hptyp (EvArgs.cons (EvE.var l7'') EvArgs.nil))
          (ExS.set (EvE.var (by simp [s3a, Locals.upd])))
      let s4a : State := { s3 with locals := s3.locals.upd 13 (i32 (R : Int)) }
      let s4 : State := { s4a with locals := s4a.locals.upd 12 (i32 (R : Int)) }
      have e4 : ExS Gen.prog s3 ldRow .normal s4 :=
        ExS.seq (call_pure rfl rfl rfl rfl hrowr (EvArgs.cons (EvE.var (by simp [s3, s3a, Locals.upd]; exact l6))
          EvArgs.nil)) (ExS.set (EvE.var (by simp [s4a, Locals.upd])))
      let s5a : State := { s4 with locals := s4.locals.upd 15 (i32 (C : Int)) }
      let s5 : State := { s5a with locals := s5a.locals.upd 14 (i32 (C : Int)) }
      have e5 : ExS Gen.prog s4 ldCol .normal s5 :=
        have l6' : s4.locals 6 = some (u8 fr) := by simp [s4, s4a, s3, s3a, Locals.upd]; exact l6
        ExS.seq (call_pure rfl rfl rfl rfl hcolr (EvArgs.cons (EvE.var l6') EvArgs.nil))
          (ExS.set (EvE.var (by simp [s5a, Locals.upd])))
      have hs5 : ∀ x, x ≤ 6 → s5.locals x = s.locals x := fun x hx => by
        simp [s5, s5a, s4, s4a, s3, s3a, Locals.upd, show x ≠ 14 by omega, show x ≠ 15 by omega,
          show x ≠ 12 by omega, show x ≠ 13 by omega, show x ≠ 10 by omega, show x ≠ 11 by omega]
        exact hs2 x (by omega) (by omega) (by omega)
      have hqc : q.code < 256 := piece_code_lt q
      obtain ⟨s6, e6, hro6, hm6n, hf6, hm6o, l16, hl6⟩ := mkSrc_spec (s := s5) (c := c) (t := q.type)
        (fr := fr) (pc := q.code) (row := R) (col := C) hf (by omega) hro (by omega) hqc hR hC
        (by rw [hs5 1 (by omega)]; exact a1)
        (by rw [hs5 6 (by omega)]; exact a6)
        (by simp [s5, s5a, s4, s4a, s3, s3a, Locals.upd]; exact l7'')
        (by simp [s5, s5a, s4, s4a, s3, Locals.upd])
        (by simp [s5, s5a, s4, Locals.upd]) (by simp [s5, Locals.upd])
      have hnb := hb.ne_fresh hf
      have hnp := pos_ne_fresh hf hm
      have hm6p : s6.mem posBlock = some (encode p) := by rw [hm6o posBlock (posBlock_ne_zero hf.1 hm) hnp.symm]; exact hm
      have hb6 : Buf s6.mem mb mo cb co cap L :=
        hb.frame (hm6o mb hb.mb0 hnb.1.symm) (hm6o cb hb.cb0 hnb.2.symm)
      have hs6 : ∀ x, x ≤ 6 → s6.locals x = s.locals x := fun x hx => by
        rw [hl6 x (by omega) (by omega) (by omega), hs5 x hx]
      obtain ⟨s7, e7, hro7, hl7, hb7, hf7, hfr7⟩ := swLoop_spec (p := p) (c := c) (cp := q.type.canPromote)
        (iz := inZone c R) q.type c.fwd (fwd_cases c) hR hC (by omega) hqc hf.2.1 hnb.1 hnb.2 hpm hpc
        s6 L (n + 1) hb6 hf6 (by omega) hm6n hm6p (by rw [hro6]; exact hro)
        (by rw [hs6 0 (by omega)]; exact a0) l16
        (by rw [hs6 2 (by omega)]; exact a2) (by rw [hs6 3 (by omega)]; exact a3)
        (by rw [hs6 4 (by omega)]; exact a4) (by rw [hs6 5 (by omega)]; exact a5)
        (by rw [hl6 10 (by decide) (by decide) (by decide)]; simp [s5, s5a, s4, s4a, s3, Locals.upd])
      have hout : sqOut p c fr = (cOps c.fwd q.type).flatMap (opOut p c q.type fr q.code R C q.type.canPromote
          (inZone c R)) := by simp [sqOut, hfr, hq, hown, R, C]
      have hlen := flatMap_opOut_len (p := p) (c := c) (t := q.type) (fr := fr) (pc := q.code) (row := R)
        (col := C) (cp := q.type.canPromote) (iz := inZone c R) (cOps c.fwd q.type)
      have hcl := cOps_length c.fwd q.type
      refine ⟨s7, .normal, _, ExS.ite (bc := true) hcond rfl (ExS.seq e1 (ExS.seq e2 (ExS.seq e3 (ExS.seq e4
        (ExS.seq e5 (ExS.seq e6 e7)))))), Or.inl rfl, by rw [hro7, hro6]; exact hro,
        fun x hx => by rw [hl7 x (by omega) (by omega), hs6 x hx], by rw [hout]; exact hb7, hf7, by omega, ?_⟩
      intro x a b d e
      have hxn : x ≠ n := fun h => by subst h; exact e (hf.2.2 _ (Nat.le_refl _))
      rw [hfr7 x a b d (by rw [hm6o x a hxn]; exact e), hm6o x a hxn]
    · have hown' : own = true := by
        simp only [own, decide_eq_true_eq]; intro h; apply hown
        cases hqc : q.color <;> cases c <;> simp_all [Color.idx]
      have hout : sqOut p c fr = [] := by simp [sqOut, hfr, hq, hown]
      refine ⟨s2, .cont, n, ExS.ite (bc := true) hcond rfl (ExS.seq e1 (ExS.seq_cont (ExS.seq e2a
        (ExS.ite (bc := true) (EvE.var l9) (by simp [truthy_boolVal, hown']) ExS.cont)))), Or.inr rfl, hro,
        fun x hx => hs2 x (by omega) (by omega) (by omega), by rw [hout]; simpa using hb, hf, by omega,
        Frame.refl _ _ _⟩

theorem sqStep_spec {s : State} {fr : Nat} (hfr : fr < 81) (h6 : s.locals 6 = some (u8 fr)) :
    ExS Gen.prog s sqStep .normal { s with locals := s.locals.upd 6 (u8 (fr + 1)) } := by
  have c1 : evalCast ⟨32, true⟩ (u8 fr) = .ok (i32 (fr : Int)) := by
    rw [i32_nat fr (by omega)]
    simp [evalCast, u8, IntTy.u8, IntTy.toInt, IntTy.i32, IntTy.wrap, IntTy.modulus]; omega
  have c2 : evalCast ⟨8, false⟩ (i32 ((fr : Int) + 1)) = .ok (u8 (fr + 1)) := by
    rw [show ((fr : Int) + 1) = ((fr + 1 : Nat) : Int) by omega, i32_nat (fr + 1) (by omega)]
    simp [evalCast, u8, IntTy.u8, IntTy.toInt, IntTy.i32, IntTy.wrap, IntTy.modulus,
      show ¬ (2147483648 ≤ fr + 1) by omega]; omega
  exact ExS.set (EvE.cast (EvE.bin (EvE.cast (EvE.var h6) c1) (EvE.const (.int ⟨32, true⟩ 1))
    (add_i32 (fr : Int) 1 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega))) c2)

def boardOut (p : Position) (c : Color) (fr d : Nat) : List (List UInt8) := (List.range' fr d).flatMap (sqOut p c)

theorem board_loop {p : Position} {c : Color} {mb mo cb co cap : Nat} (hpm : posBlock ≠ mb) (hpc : posBlock ≠ cb) :
    ∀ (d fr : Nat) (s : State) (L : List (List UInt8)) (n : Nat), fr + d = 81 →
      Buf s.mem mb mo cb co cap L → Fresh s.mem n → n + 400 * d < 2 ^ 64 →
      s.mem posBlock = some (encode p) → s.ro = false →
      s.locals 0 = some (posPtr' posBlock) → s.locals 1 = some (u32 c.idx) →
      s.locals 2 = some (.ptr mb mo) → s.locals 3 = some (.ptr cb co) →
      s.locals 4 = some (.int IntTy.u64 cap) → s.locals 5 = some (i32 c.fwd) →
      s.locals 6 = some (u8 fr) →
      ∃ s' n', ExS Gen.prog s (.loop (sqBody c.fwd) sqStep) .normal s' ∧ s'.ro = false ∧
        (∀ x, x ≤ 5 → s'.locals x = s.locals x) ∧
        Buf s'.mem mb mo cb co cap (L ++ boardOut p c fr d) ∧ Fresh s'.mem n' ∧ n' ≤ n + 400 * d ∧
        Frame s.mem s'.mem mb cb := by
  intro d
  induction d with
  | zero =>
    intro fr s L n hd hb hf _ _ hro _ _ _ _ _ _ a6
    have : fr = 81 := by omega
    subst this
    refine ⟨s, n, ExS.loop_brk (ExS.ite (bc := false) (vc := boolVal false) (EvE_of_eval (n := 4) ?_) rfl ExS.brk),
      hro, fun _ _ => rfl, by simpa [boardOut] using hb, hf, by omega, Frame.refl _ _ _⟩
    simp [sqCond, evalExpr, a6, evalCast, evalBin, isPtr, evalBinInt, binInt, intOf, u8, IntTy.u8, IntTy.toInt,
      IntTy.modulus, Res.bind]
  | succ d ih =>
    intro fr s L n hd hb hf h64 hm hro a0 a1 a2 a3 a4 a5 a6
    have hfr : fr < 81 := by omega
    obtain ⟨s1, o, n1, e1, ho, hro1, hl1, hb1, hf1, hn1, hfr1⟩ := sq_body (p := p) (c := c) hpm hpc fr hfr s L n
      hb hf (Nat.lt_of_le_of_lt (by omega) h64) hm hro a0 a1 a2 a3 a4 a5 a6
    let s2 : State := { s1 with locals := s1.locals.upd 6 (u8 (fr + 1)) }
    have es : ExS Gen.prog s1 sqStep .normal s2 := sqStep_spec hfr (by rw [hl1 6 (by omega)]; exact a6)
    have hl2 : ∀ x, x ≤ 5 → s2.locals x = s.locals x := fun x hx => by
      simp [s2, Locals.upd, show x ≠ 6 by omega]; exact hl1 x (by omega)
    obtain ⟨s', n', e', hro', hl', hb', hf', hn', hfr'⟩ := ih (fr + 1) s2 _ n1 (by omega) hb1 hf1 (by omega)
      (hfr1.pos hpm hpc hm (posBlock_ne_zero hf.1 hm)) hro1
      (by rw [hl2 0 (by omega)]; exact a0) (by rw [hl2 1 (by omega)]; exact a1)
      (by rw [hl2 2 (by omega)]; exact a2) (by rw [hl2 3 (by omega)]; exact a3)
      (by rw [hl2 4 (by omega)]; exact a4) (by rw [hl2 5 (by omega)]; exact a5) (by simp [s2, Locals.upd])
    have hout : boardOut p c fr (d + 1) = sqOut p c fr ++ boardOut p c (fr + 1) d := by
      simp [boardOut, List.range'_succ]
    refine ⟨s', n', ExS.loop_next e1 ho es e', hro', fun x hx => by rw [hl' x hx, hl2 x hx], ?_, hf', by omega,
      Frame.trans hfr1 hfr'⟩
    rw [hout, ← List.append_assoc]; exact hb'

/-- Bytes `generate_pseudo_for_color(position, color, ...)` appends. -/
def pseudoC (p : Position) (c : Color) : List (List UInt8) := boardOut p c 0 81 ++ dropsC p c

theorem generate_pseudo_spec {p : Position} {c : Color} {m : Mem} {mb mo cb co cap n : Nat}
    {L : List (List UInt8)} (hbuf : Buf m mb mo cb co cap L) (hf : Fresh m n) (h64 : n + 40000 < 2 ^ 64)
    (hm : m posBlock = some (encode p)) (hpm : posBlock ≠ mb) (hpc : posBlock ≠ cb) :
    ∃ s' n', ExS Gen.prog ⟨frameLocals Gen.generate_pseudo_for_color.params
        [posPtr' posBlock, u32 c.idx, .ptr mb mo, .ptr cb co, .int IntTy.u64 cap], m, false⟩
      Gen.generate_pseudo_for_color.body .normal s' ∧
      Buf s'.mem mb mo cb co cap (L ++ pseudoC p c) ∧ Fresh s'.mem n' ∧ n' ≤ n + 40000 ∧ Frame m s'.mem mb cb := by
  let s0 : State := ⟨frameLocals Gen.generate_pseudo_for_color.params
    [posPtr' posBlock, u32 c.idx, .ptr mb mo, .ptr cb co, .int IntTy.u64 cap], m, false⟩
  let s1 : State := { s0 with locals := s0.locals.upd 5 (i32 c.fwd) }
  have e1 : ExS Gen.prog s0 (.set 5 (.cond (.bin .eq (some ⟨32, false⟩) (.cast ⟨32, false⟩ (.var 1))
      (.cast ⟨32, false⟩ (.const (.int ⟨32, true⟩ 0)))) (.un .neg ⟨32, true⟩ (.const (.int ⟨32, true⟩ 1)))
      (.const (.int ⟨32, true⟩ 1)))) .normal s1 := by
    apply ExS.set; apply EvE_of_eval (n := 4)
    have h1 : s0.locals 1 = some (u32 c.idx) := rfl
    cases c <;> simp [evalExpr, h1, evalCast, evalBin, evalUn, isPtr, evalBinInt, binInt, intOf, u32, IntTy.u32,
      IntTy.modulus, IntTy.toInt, Res.bind, truthy, boolVal, Color.idx, Color.fwd, i32, IntTy.wrap, arith,
      IntTy.inRange, IntTy.i32] <;> decide
  let s2 : State := { s1 with locals := s1.locals.upd 6 (u8 0) }
  have e2 : ExS Gen.prog s1 (.set 6 (.cast ⟨8, false⟩ (.const (.int ⟨32, true⟩ 0)))) .normal s2 :=
    ExS.set (EvE_of_eval (n := 3) (by simp [evalExpr, evalCast, IntTy.toInt, Res.bind, u8, IntTy.u8, IntTy.wrap,
      IntTy.modulus]))
  have hl2 : ∀ x, x ≤ 4 → s2.locals x = s0.locals x := fun x hx => by
    simp [s2, s1, Locals.upd, show x ≠ 6 by omega, show x ≠ 5 by omega]
  obtain ⟨s3, n3, e3, hro3, hl3, hb3, hf3, hn3, hfr3⟩ := board_loop (p := p) (c := c) hpm hpc 81 0 s2 L n rfl
    hbuf hf (Nat.lt_of_le_of_lt (by omega) h64) hm rfl
    (by rw [hl2 0 (by omega)]; rfl) (by rw [hl2 1 (by omega)]; rfl) (by rw [hl2 2 (by omega)]; rfl)
    (by rw [hl2 3 (by omega)]; rfl) (by rw [hl2 4 (by omega)]; rfl) (by simp [s2, s1, Locals.upd])
    (by simp [s2, Locals.upd])
  obtain ⟨s4, o4, e4, ho4, hb4, hf4, hfr4⟩ := add_pseudo_drops_spec (p := p) (c := c) hb3 hf3
    (Nat.lt_of_le_of_lt (by omega) h64) (hfr3.pos hpm hpc hm (posBlock_ne_zero hf.1 hm)) hpm hpc
  have hl3' : ∀ x, x ≤ 4 → s3.locals x = s0.locals x := fun x hx => by
    rw [hl3 x (by omega), hl2 x hx]
  have hargs : EvArgs Gen.prog s3 [(.var 0), (.var 1), (.var 2), (.var 3), (.var 4)]
      [posPtr' posBlock, .int IntTy.u32 c.idx, .ptr mb mo, .ptr cb co, .int IntTy.u64 cap] :=
    EvArgs.cons (EvE.var (by rw [hl3' 0 (by omega)]; rfl)) (EvArgs.cons (EvE.var (by rw [hl3' 1 (by omega)]; rfl))
      (EvArgs.cons (EvE.var (by rw [hl3' 2 (by omega)]; rfl)) (EvArgs.cons (EvE.var (by rw [hl3' 3 (by omega)]; rfl))
      (EvArgs.cons (EvE.var (by rw [hl3' 4 (by omega)]; rfl)) EvArgs.nil))))
  have hlen := rowsOut_length p c (actUpTo p c 7) (pawnUpTo p (Piece.code ⟨c, .pawn⟩) 81) 0 9
  have hdl : (dropsC p c).length ≤ 567 := by
    unfold dropsC; split
    · simp
    · omega
  refine ⟨{ s3 with mem := s4.mem }, _, ExS.seq e1 (ExS.seq (ExS.seq e2 (by rw [loop2_eq c.fwd]; exact e3))
    (ExS.call hargs rfl rfl (by rw [hro3]; exact e4) ho4)), ?_, hf4, by omega, Frame.trans hfr3 hfr4⟩
  rw [pseudoC, ← List.append_assoc]; exact hb4

end Shogi.C.Proofs
