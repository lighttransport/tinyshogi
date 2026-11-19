/-
  T8: `make_legal_probe`, part 7 — the common tail: put the moving piece on
  the destination, move the king square, flip the side.
-/
import Shogi.C.Proofs.Probe6

namespace Shogi.C.Proofs
variable {posBlock : Nat}
open MiniC Shogi Shogi.C

def kbAfter (c : Color) (M : Piece) (d : Square) (kb : UInt8) (me : Color) : UInt8 :=
  if M.type = .king ∧ c = me then d.val.toUInt8 else kb

theorem probe_tail {s : State} {pa h kb kw} {c : Color} {n ub : Nat} {U MV : List UInt8} {d : Square} {M : Piece}
    (hl0 : s.locals 0 = some (posPtr' posBlock)) (hl1 : s.locals 1 = some (.ptr n 0)) (hl2 : s.locals 2 = some (.ptr ub 0))
    (hl4 : s.locals 4 = some (.int IntTy.u32 c.idx))
    (hmp : s.mem posBlock = some (enc pa h c kb kw)) (hmn : s.mem n = some MV) (hMV : MV.length = 5)
    (hMV1 : MV.getD 1 0 = d.val.toUInt8) (hmu : s.mem ub = some U) (hU : U.length = 20)
    (hU12 : U.getD 12 0 = M.code.toUInt8)
    (hpu : posBlock ≠ ub) (hpn : posBlock ≠ n) (hro : s.ro = false) :
    ∃ s', ExS Gen.prog s (.seq pb11 (.seq pb12 pb13)) .normal s' ∧ s'.ro = s.ro ∧
      s'.mem posBlock = some (enc (fun y => if y = d then some M else pa y) h c.opp
        (kbAfter c M d kb .black) (kbAfter c M d kw .white)) ∧
      (∀ x, x ≠ posBlock → s'.mem x = s.mem x) ∧
      (∀ x, x ≠ 16 → s'.locals x = s.locals x) := by
  let P := enc pa h c kb kw
  have hP : P.length = 114 := enc_length _ _ _ _ _
  have hd81 := d.isLt
  have hMl := piece_code_lt M
  have hto := ev_blk_u8 hl1 hmn (k := 1) (by omega)
  rw [hMV1, toNat_toUInt8_lt _ (by omega)] at hto
  have hmv := ev_blk_u8 hl2 hmu (k := 12) (by omega)
  rw [hU12, toNat_toUInt8_lt _ hMl] at hmv
  -- pb11
  have e11 := st_pos_u (base := 0) hP hl0 hmp (t := IntTy.u8) rfl hto (by omega) hmv hro
  let m1 := s.mem.write posBlock (0 + d.val) (encodeLE 1 M.code)
  let P1 := enc (fun y => if y = d then some M else pa y) h c kb kw
  have hm1p : m1 posBlock = some P1 := by
    show (s.mem.write posBlock (0 + d.val) _) posBlock = _
    rw [Nat.zero_add, write1_set hmp (by rw [hP]; omega)]
    have := enc_set_board pa h c kb kw d (some M)
    simp only [pieceByte] at this; exact congrArg some this
  have hm1o : ∀ x, x ≠ posBlock → m1 x = s.mem x := fun x hx => Mem.write_ne hx
  let s1 : State := { s with mem := m1 }
  -- pb12
  have hmv1 : EvE Gen.prog s1 (.load (.int ⟨8, false⟩) (.field (.var 2) 12)) (u8 M.code) := by
    have hmu1 : s1.mem ub = some U := by show m1 ub = _; rw [hm1o ub (Ne.symm hpu)]; exact hmu
    have := ev_blk_u8 (s := s1) (B := U) hl2 hmu1 (k := 12) (by omega)
    rw [hU12, toNat_toUInt8_lt _ hMl] at this; exact this
  let s2 : State := { s1 with locals := s1.locals.upd 16 (u32 M.type.code) }
  have c16 : ExS Gen.prog s1 (.call (some 16) 2 [(.load (.int ⟨8, false⟩) (.field (.var 2) 12))]) .normal s2 :=
    callS rfl pureS_type rfl (run_type M) (EvArgs.cons hmv1 EvArgs.nil)
  have htk : M.type.code < 2 ^ 32 := by cases M.type <;> decide
  have hk8 : EvE Gen.prog s2 (.bin .eq (some ⟨32, false⟩) (.cast ⟨32, false⟩ (.var 16))
      (.cast ⟨32, false⟩ (.const (.int ⟨32, true⟩ 8)))) (boolVal (decide (M.type = .king))) := by
    apply EvE_of_eval (n := 4)
    have h16 : s2.locals 16 = some (u32 M.type.code) := by simp [s2, Locals.upd]
    have : (M.type.code = 8) ↔ (M.type = .king) := by cases M.type <;> decide
    simp [evalExpr, h16, evalCast, evalBin, isPtr, evalBinInt, binInt, intOf, u32, IntTy.u32, IntTy.modulus,
      IntTy.toInt, IntTy.wrap, Res.bind, Nat.mod_eq_of_lt htk, this]
  have hl4' : s2.locals 4 = some (.int IntTy.u32 c.idx) := by simp [s2, s1, Locals.upd]; exact hl4
  have hl0' : s2.locals 0 = some (posPtr' posBlock) := by simp [s2, s1, Locals.upd]; exact hl0
  have hl1' : s2.locals 1 = some (.ptr n 0) := by simp [s2, s1, Locals.upd]; exact hl1
  have hmn' : s2.mem n = some MV := by show m1 n = _; rw [hm1o n (Ne.symm hpn)]; exact hmn
  have hc2 : c.idx < 2 := by cases c <;> decide
  obtain ⟨s3, e12b, hro3, hm3p, hm3o, hl3⟩ : ∃ s3, ExS Gen.prog s2 (.ite (.bin .eq (some ⟨32, false⟩)
      (.cast ⟨32, false⟩ (.var 16)) (.cast ⟨32, false⟩ (.const (.int ⟨32, true⟩ 8))))
      (.store (.int ⟨8, false⟩) (.index (.field (.var 0) 112) (.var 4) 1) (.load (.int ⟨8, false⟩) (.field (.var 1) 1)))
      .skip) .normal s3 ∧ s3.ro = s.ro ∧
      s3.mem posBlock = some (enc (fun y => if y = d then some M else pa y) h c
        (kbAfter c M d kb .black) (kbAfter c M d kw .white)) ∧
      (∀ x, x ≠ posBlock → s3.mem x = s.mem x) ∧ s3.locals = s2.locals := by
    by_cases hk : M.type = .king
    · have hto2 := ev_blk_u8 (s := s2) hl1' hmn' (k := 1) (by omega)
      rw [hMV1, toNat_toUInt8_lt _ (by omega)] at hto2
      have st := st_pos_u (s := s2) (base := 112) (e := .var 4) (x := c.idx) (t := IntTy.u32) (P := P1) (enc_length _ _ _ _ _) hl0' hm1p rfl
        (EvE.var hl4') (by omega) hto2 hro
      refine ⟨_, ExS.ite (bc := true) hk8 (by simp [truthy_boolVal, hk]) st, rfl, ?_, ?_, rfl⟩
      · show (m1.write posBlock (112 + c.idx) _) posBlock = _
        rw [write1_set hm1p (by rw [enc_length]; omega), enc_set_king]
        cases c <;> simp [kbAfter, hk]
      · intro x hx; show (m1.write posBlock _ _) x = _; rw [Mem.write_ne hx, hm1o x hx]
    · refine ⟨s2, ExS.ite (bc := false) hk8 (by simp [truthy_boolVal, hk]) ExS.skip, rfl, ?_, hm1o, rfl⟩
      show m1 posBlock = _; rw [hm1p]; simp [kbAfter, hk, P1]
  have hxor : EvE Gen.prog s3 (.cast ⟨32, false⟩ (.bin .bxor (some ⟨32, false⟩) (.cast ⟨32, false⟩ (.var 4))
      (.cast ⟨32, false⟩ (.const (.int ⟨32, true⟩ 1))))) (.int IntTy.u32 c.opp.idx) := by
    apply EvE_of_eval (n := 5)
    have h4 : s3.locals 4 = some (.int IntTy.u32 c.idx) := by rw [hl3]; exact hl4'
    cases c <;> simp [evalExpr, h4, evalCast, evalBin, isPtr, evalBinInt, binInt, intOf, IntTy.u32,
      IntTy.modulus, IntTy.toInt, IntTy.wrap, Res.bind, Color.idx, Color.opp] <;> rfl
  have hl0'' : s3.locals 0 = some (posPtr' posBlock) := by rw [hl3]; exact hl0'
  have st := store_int_field (s := s3) (o := 0) (b := posBlock) (j := 0) (t := ⟨32, false⟩) (i := 96)
    (v := c.opp.idx) (blk := enc (fun y => if y = d then some M else pa y) h c
        (kbAfter c M d kb .black) (kbAfter c M d kw .white)) hl0'' hm3p (by rw [enc_length]; decide) hxor
    (by rw [hro3]; exact hro) (encodeLE_length _ _)
  refine ⟨_, ExS.seq e11 (ExS.seq (ExS.seq c16 e12b) st), by rw [hro3], ?_, ?_, ?_⟩
  · show (s3.mem.write posBlock (0 + 96) _) posBlock = _
    rw [write_some hm3p]; congr 1
    simp only [wrb, encodeLE_length, IntTy.bytes, Nat.zero_add]
    exact enc_set_side _ _ _ _ _ c.opp
  · intro x hx; show (s3.mem.write posBlock _ _) x = _; rw [Mem.write_ne hx, hm3o x hx]
  · intro x hx; show s3.locals x = _; rw [hl3]; simp [s2, s1, Locals.upd, hx]

end Shogi.C.Proofs
