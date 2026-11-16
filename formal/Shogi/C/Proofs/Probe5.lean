/-
  T8: `make_legal_probe`, part 5 — a capture adds the piece to the hand.
-/
import Shogi.C.Proofs.Probe4

namespace Shogi.C.Proofs
open MiniC Shogi Shogi.C

theorem toUInt8_mod (n : Nat) : (n % 256).toUInt8 = n.toUInt8 := by
  apply UInt8.toNat_inj.mp; simp [Nat.toUInt8, UInt8.toNat_ofNat]

theorem write1_set {m : Mem} {b o : Nat} {B : List UInt8} (hb : m b = some B) (ho : o < B.length) (v : Nat) :
    (m.write b o (encodeLE 1 v)) b = some (B.set o v.toUInt8) := by
  rw [write_some hb]; congr 1
  rw [← wr1_eq_set _ _ _ ho]; simp [wrb, wr1, encodeLE, toUInt8_mod]

def capStmt : Stmt := (.seq (.seq (.call (some 10) 2 [(.var 8)]) (.seq (.call (some 11) 4 [(.var 10)]) (.seq (.call (some 12) 13 [(.var 11)]) (.set 9 (.var 12))))) (.seq (.store (.int ⟨8, false⟩) (.field (.var 2) 15) (.cast ⟨8, false⟩ (.var 9))) (.seq (.store (.int ⟨8, false⟩) (.field (.var 2) 16) (.load (.int ⟨8, false⟩) (.index (.index (.field (.var 0) 81) (.var 4) 7) (.var 9) 1))) (.store (.int ⟨8, false⟩) (.index (.index (.field (.var 0) 81) (.var 4) 7) (.var 9) 1) (.cast ⟨8, false⟩ (.bin .add (some ⟨32, true⟩) (.cast ⟨32, true⟩ (.load (.int ⟨8, false⟩) (.index (.index (.field (.var 0) 81) (.var 4) 7) (.var 9) 1))) (.const (.int ⟨32, true⟩ 1))))))))

theorem pn5_eq : pn5 = .ite (.bin .ne (some ⟨32, true⟩) (.cast ⟨32, true⟩ (.var 8)) (.const (.int ⟨32, true⟩ 0))) capStmt .skip := rfl

theorem cap_spec {s : State} {pa h kb kw} {c : Color} {ub : Nat} {U : List UInt8} {q : Piece} {i : Fin 7}
    (hl0 : s.locals 0 = some posPtr) (hl2 : s.locals 2 = some (.ptr ub 0))
    (hl4 : s.locals 4 = some (.int IntTy.u32 c.idx)) (hl8 : s.locals 8 = some (u8 q.code))
    (hmp : s.mem posBlock = some (enc pa h c kb kw)) (hmu : s.mem ub = some U) (hU : U.length = 20)
    (hpu : posBlock ≠ ub) (hro : s.ro = false) (hi : q.type.unpromote.handIndex = some i) :
    ∃ s', ExS Gen.prog s capStmt .normal s' ∧ s'.ro = s.ro ∧
      s'.mem posBlock = some (enc pa (hupd h c i (h c i + 1)) c kb kw) ∧
      s'.mem ub = some ((U.set 15 i.val.toUInt8).set 16 (h c i).toUInt8) ∧
      (∀ x, x ≠ posBlock → x ≠ ub → s'.mem x = s.mem x) ∧
      (∀ x, x ≠ 9 → x ≠ 10 → x ≠ 11 → x ≠ 12 → s'.locals x = s.locals x) := by
  let P := enc pa h c kb kw
  have hP : P.length = 114 := enc_length _ _ _ _ _
  have hi7 := i.isLt
  -- the three helper calls
  let s1 : State := { s with locals := s.locals.upd 10 (u32 q.type.code) }
  have e1 : ExS Gen.prog s (.call (some 10) 2 [(.var 8)]) .normal s1 :=
    callS rfl pureS_type rfl (run_type q) (EvArgs.cons (EvE.var hl8) EvArgs.nil)
  let s2 : State := { s1 with locals := s1.locals.upd 11 (u32 q.type.unpromote.code) }
  have e2 : ExS Gen.prog s1 (.call (some 11) 4 [(.var 10)]) .normal s2 :=
    callS rfl pureS_unpromote rfl (run_unpromote q.type) (EvArgs.cons (EvE.var (by simp [s1, Locals.upd])) EvArgs.nil)
  let s3 : State := { s2 with locals := s2.locals.upd 12 (i32 (i.val : Int)) }
  have hrun := run_hand_index q.type.unpromote
  rw [hi] at hrun
  have e3 : ExS Gen.prog s2 (.call (some 12) 13 [(.var 11)]) .normal s3 :=
    callS rfl pureS_hand_index rfl hrun (EvArgs.cons (EvE.var (by simp [s2, Locals.upd])) EvArgs.nil)
  let s4 : State := { s3 with locals := s3.locals.upd 9 (i32 (i.val : Int)) }
  have e4 : ExS Gen.prog s3 (.set 9 (.var 12)) .normal s4 := ExS.set (EvE.var (by simp [s3, Locals.upd]))
  have l4 : ∀ x, x ≠ 9 → x ≠ 10 → x ≠ 11 → x ≠ 12 → s4.locals x = s.locals x := fun x a b d e => by
    simp [s4, s3, s2, s1, Locals.upd, a, b, d, e]
  have l9 : s4.locals 9 = some (i32 (i.val : Int)) := by simp [s4, Locals.upd]
  -- undo->hand_index = hand
  have ec : EvE Gen.prog s4 (.cast ⟨8, false⟩ (.var 9)) (.int IntTy.u8 i.val) := by
    refine EvE.cast (EvE.var l9) ?_
    rw [i32_nat i.val (by omega)]
    simp [evalCast, IntTy.i32, IntTy.toInt, IntTy.wrap, IntTy.modulus, IntTy.u8, show ¬ (2147483648 ≤ i.val) by omega]
    omega
  have e5 := store_int_field (s := s4) (o := 0) (b := ub) (j := 2) (t := ⟨8, false⟩) (i := 15) (v := i.val)
    (blk := U) (by rw [l4 2 (by decide) (by decide) (by decide) (by decide)]; exact hl2) hmu (by rw [hU]; decide)
    ec hro (encodeLE_length _ _)
  let m5 := s.mem.write ub (0 + 15) (encodeLE 1 i.val)
  have hm5u : m5 ub = some (U.set 15 i.val.toUInt8) := write1_set hmu (by omega) _
  have hm5p : m5 posBlock = some P := by simp only [m5]; rw [Mem.write_ne hpu]; exact hmp
  let t5 : State := { s4 with mem := m5 }
  have l0' : t5.locals 0 = some posPtr := by
    show s4.locals 0 = _; rw [l4 0 (by decide) (by decide) (by decide) (by decide)]; exact hl0
  have l4' : t5.locals 4 = some (.int IntTy.u32 c.idx) := by
    show s4.locals 4 = _; rw [l4 4 (by decide) (by decide) (by decide) (by decide)]; exact hl4
  have hv := ev_hand_slot (s := t5) hP l0' hm5p l4' hi7 (show t5.locals 9 = _ from l9)
  rw [enc_getD_hand] at hv
  have e6 := store_int_field (s := t5) (o := 0) (b := ub) (j := 2) (t := ⟨8, false⟩) (i := 16)
    (v := (h c i).toUInt8.toNat) (blk := U.set 15 i.val.toUInt8)
    (by show s4.locals 2 = _; rw [l4 2 (by decide) (by decide) (by decide) (by decide)]; exact hl2) hm5u
    (by simp [hU, IntTy.bytes]) hv hro (encodeLE_length _ _)
  let m6 := m5.write ub (0 + 16) (encodeLE 1 (h c i).toUInt8.toNat)
  have hm6u : m6 ub = some ((U.set 15 i.val.toUInt8).set 16 (h c i).toUInt8) := by
    have key : ((h c i).toUInt8.toNat).toUInt8 = (h c i).toUInt8 := by
      apply UInt8.toNat_inj.mp; simp [Nat.toUInt8, UInt8.toNat_ofNat]
    show (m5.write ub (0 + 16) _) ub = _
    rw [write1_set hm5u (by simp [hU]), key]
  have hm6p : m6 posBlock = some P := by simp only [m6]; rw [Mem.write_ne hpu]; exact hm5p
  let t6 : State := { s4 with mem := m6 }
  have hv' := ev_hand_slot (s := t6) hP (show t6.locals 0 = _ from l0') hm6p (show t6.locals 4 = _ from l4') hi7 (show t6.locals 9 = _ from l9)
  rw [enc_getD_hand] at hv'
  have hb := UInt8.toNat_lt (h c i).toUInt8
  have hadd : EvE Gen.prog t6 (.cast ⟨8, false⟩ (.bin .add (some ⟨32, true⟩) (.cast ⟨32, true⟩
      (.load (.int ⟨8, false⟩) (.index (.index (.field (.var 0) 81) (.var 4) 7) (.var 9) 1)))
      (.const (.int ⟨32, true⟩ 1)))) (.int IntTy.u8 (((h c i).toUInt8.toNat + 1) % 256)) := by
    have c1 : evalCast ⟨32, true⟩ (.int IntTy.u8 (h c i).toUInt8.toNat) = .ok (i32 ((h c i).toUInt8.toNat : Int)) := by
      rw [i32_nat _ (by omega)]
      simp [evalCast, IntTy.u8, IntTy.i32, IntTy.toInt, IntTy.wrap, IntTy.modulus]; omega
    refine EvE.cast (EvE.bin (EvE.cast hv' c1) (EvE.const (.int ⟨32, true⟩ 1))
      (add_i32 _ 1 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega))) ?_
    rw [show (((h c i).toUInt8.toNat : Nat) : Int) + 1 = (((h c i).toUInt8.toNat + 1 : Nat) : Int) by omega,
      i32_nat _ (by omega)]
    simp [evalCast, IntTy.u8, IntTy.i32, IntTy.toInt, IntTy.wrap, IntTy.modulus,
      show ¬ (2147483648 ≤ (h c i).toUInt8.toNat + 1) by omega]
    have : h c i % 256 < 256 := Nat.mod_lt _ (by decide)
    rw [if_neg (by omega)]; omega
  have e7 := st_hand_slot (s := t6) hP (show t6.locals 0 = _ from l0') hm6p (show t6.locals 4 = _ from l4') hi7 (show t6.locals 9 = _ from l9) hadd hro
  have hval : (((h c i).toUInt8.toNat + 1) % 256).toUInt8 = (h c i + 1).toUInt8 := by
    rw [toUInt8_mod]; apply UInt8.toNat_inj.mp; simp [Nat.toUInt8, UInt8.toNat_ofNat]
  let m7 := m6.write posBlock (81 + 7 * c.idx + i.val) (encodeLE 1 (((h c i).toUInt8.toNat + 1) % 256))
  have hm7p : m7 posBlock = some (enc pa (hupd h c i (h c i + 1)) c kb kw) := by
    have hc : c.idx < 2 := by cases c <;> decide
    show (m6.write posBlock _ _) posBlock = _
    rw [write1_set hm6p (by rw [hP]; omega), hval, enc_set_hand]
  refine ⟨{ s4 with mem := m7 }, ExS.seq (ExS.seq e1 (ExS.seq e2 (ExS.seq e3 e4))) (ExS.seq e5 (ExS.seq e6 e7)),
    rfl, hm7p, ?_, ?_, l4⟩
  · show m7 ub = _; simp only [m7]; rw [Mem.write_ne (Ne.symm hpu)]; exact hm6u
  · intro x a b; show m7 x = _
    simp only [m7, m6, m5]; rw [Mem.write_ne a, Mem.write_ne b, Mem.write_ne b]

end Shogi.C.Proofs
