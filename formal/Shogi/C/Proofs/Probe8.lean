/-
  T8: `make_legal_probe`, part 8 — the drop branch.
-/
import Shogi.C.Proofs.Probe7

namespace Shogi.C.Proofs
open MiniC Shogi Shogi.C

theorem code_handIndex {t : PieceType} {i : Fin 7} (h : t.handIndex = some i) : t.code = i.val + 1 := by
  cases t <;> simp [PieceType.handIndex] at h <;> subst h <;> rfl

theorem sub_i32 (a b : Int) (h1 : -2147483648 ≤ a - b) (h2 : a - b < 2147483648)
    (ha1 : -2147483648 ≤ a) (ha2 : a < 2147483648) (hb1 : -2147483648 ≤ b) (hb2 : b < 2147483648) :
    evalBin .sub (some ⟨32, true⟩) (i32 a) (i32 b) = .ok (i32 (a - b)) := by
  simp [evalBin, isPtr, evalBinInt, binInt, intOf, i32, IntTy.i32, Res.bind, arith,
    toInt_wrap32 a ha1 ha2, toInt_wrap32 b hb1 hb2, IntTy.inRange, IntTy.minVal, IntTy.maxVal]
  omega

theorem probe_drop {s : State} {pa h kb kw} {c : Color} {n ub : Nat} {U : List UInt8} {d : Square}
    {t : PieceType} {i : Fin 7}
    (hl0 : s.locals 0 = some posPtr) (hl1 : s.locals 1 = some (.ptr n 0)) (hl2 : s.locals 2 = some (.ptr ub 0))
    (hl4 : s.locals 4 = some (.int IntTy.u32 c.idx))
    (hmp : s.mem posBlock = some (enc pa h c kb kw))
    (hmn : s.mem n = some [255, d.val.toUInt8, 0, 0, t.code.toUInt8])
    (hmu : s.mem ub = some U) (hU : U.length = 20)
    (hpu : posBlock ≠ ub) (hpn : posBlock ≠ n) (hnu : n ≠ ub) (hro : s.ro = false)
    (hi : t.handIndex = some i) (hh : 1 ≤ h c i) :
    ∃ s' U', ExS Gen.prog s pbDrop .normal s' ∧ s'.ro = s.ro ∧
      s'.mem posBlock = some (enc pa (hupd h c i (h c i - 1)) c kb kw) ∧
      s'.mem ub = some U' ∧ U'.length = 20 ∧ U'.getD 12 0 = (Piece.code ⟨c, t⟩).toUInt8 ∧
      (∀ x, x ≠ posBlock → x ≠ ub → s'.mem x = s.mem x) ∧
      (∀ x, x ≤ 4 → s'.locals x = s.locals x) := by
  let P := enc pa h c kb kw
  have hP : P.length = 114 := enc_length _ _ _ _ _
  have hcode := code_handIndex hi
  have hi7 := i.isLt
  let MV : List UInt8 := [255, d.val.toUInt8, 0, 0, t.code.toUInt8]
  have hdrop := ev_blk_u8 hl1 hmn (k := 4) (by simp)
  have hdv : (MV.getD 4 0).toNat = t.code := by simp [MV, toNat_toUInt8_lt _ (show t.code < 256 by omega)]
  rw [show ([255, d.val.toUInt8, 0, 0, t.code.toUInt8] : List UInt8) = MV from rfl, hdv] at hdrop
  -- pd0 : hand = drop - 1
  let s1 : State := { s with locals := s.locals.upd 5 (.int IntTy.u32 i.val) }
  have hcu : EvE Gen.prog s (.cast ⟨32, false⟩ (.load (.int ⟨8, false⟩) (.field (.var 1) 4)))
      (.int IntTy.u32 t.code) :=
    EvE.cast hdrop (by simp [evalCast, IntTy.u8, IntTy.u32, IntTy.toInt, IntTy.wrap, IntTy.modulus]; omega)
  have e0 : ExS Gen.prog s pd0 .normal s1 := by
    apply ExS.set
    refine EvE.bin hcu (EvE.const _) ?_
    rw [hcode]
    simp only [evalBin, isPtr, evalBinInt, binInt, intOf, IntTy.u32, Bool.false_eq_true, ite_false, Res.bind_eq,
      Res.bind_ok, arith, IntTy.wrap, IntTy.modulus]
    simp only [Bool.and_false, Bool.false_eq_true, ite_false, ite_true, Res.bind, pure]
    rw [if_pos (by omega), Nat.add_sub_cancel]
  have l5 : s1.locals 5 = some (.int IntTy.u32 i.val) := by simp [s1, Locals.upd]
  -- pd1 : undo->moving_piece = shogi_piece(color, drop)
  let s2 : State := { s1 with locals := s1.locals.upd 6 (u8 (Piece.code ⟨c, t⟩)) }
  have hcu1 : EvE Gen.prog s1 (.cast ⟨32, false⟩ (.load (.int ⟨8, false⟩) (.field (.var 1) 4))) (u32 t.code) := by
    have := ev_blk_u8 (s := s1) (j := 1) (b := n) (B := MV)
      (show s1.locals 1 = some (.ptr n 0) by simp [s1, Locals.upd]; exact hl1) hmn (k := 4) (by simp [MV])
    rw [hdv] at this
    have h256 : t.code < 4294967296 := by omega
    exact EvE.cast this (by simp [evalCast, IntTy.u8, IntTy.u32, u32, IntTy.toInt, IntTy.wrap, IntTy.modulus,
      Nat.mod_eq_of_lt h256])
  have c1 : ExS Gen.prog s1 (.call (some 6) 0 [(.var 4), (.cast ⟨32, false⟩ (.load (.int ⟨8, false⟩) (.field (.var 1) 4)))])
      .normal s2 :=
    callS rfl pureS_piece rfl (run_piece c t)
      (EvArgs.cons (EvE.var (by simp [s1, Locals.upd]; exact hl4)) (EvArgs.cons hcu1 EvArgs.nil))
  have l2s2 : s2.locals 2 = some (.ptr ub 0) := by simp [s2, s1, Locals.upd]; exact hl2
  have hpcl := piece_code_lt ⟨c, t⟩
  have st1 := store_int_field (s := s2) (o := 0) (b := ub) (j := 2) (t := ⟨8, false⟩) (i := 12)
    (v := Piece.code ⟨c, t⟩) (e := .var 6) (blk := U) l2s2 hmu (by rw [hU]; decide)
    (EvE.var (by simp [s2, Locals.upd]; rfl)) hro (encodeLE_length _ _)
  let m3 := s.mem.write ub (0 + 12) (encodeLE 1 (Piece.code ⟨c, t⟩))
  let U2 := U.set 12 (Piece.code ⟨c, t⟩).toUInt8
  have hm3u : m3 ub = some U2 := by show (s.mem.write ub (0 + 12) _) ub = _; rw [write1_set hmu (by omega)]
  -- pd2 : undo->hand_index = hand
  have ec : EvE Gen.prog { s2 with mem := m3 } (.cast ⟨8, false⟩ (.var 5)) (.int IntTy.u8 i.val) :=
    EvE.cast (EvE.var (v := .int IntTy.u32 i.val) (show s2.locals 5 = _ by simp [s2, s1, Locals.upd])) (by
      simp [evalCast, IntTy.u8, IntTy.u32, IntTy.toInt, IntTy.wrap, IntTy.modulus]; omega)
  have st2 := store_int_field (s := { s2 with mem := m3 }) (o := 0) (b := ub) (j := 2) (t := ⟨8, false⟩) (i := 15)
    (v := i.val) (e := .cast ⟨8, false⟩ (.var 5)) (blk := U2) l2s2 hm3u (by simp [U2, hU, IntTy.bytes]) ec hro
    (encodeLE_length _ _)
  let m4 := m3.write ub (0 + 15) (encodeLE 1 i.val)
  let U3 := U2.set 15 i.val.toUInt8
  have hm4u : m4 ub = some U3 := by
    show (m3.write ub (0 + 15) _) ub = _; rw [write1_set hm3u (by simp [U2, hU])]
  have hm4p : m4 posBlock = some P := by
    show (m3.write ub _ _) posBlock = _; rw [Mem.write_ne hpu]; show (s.mem.write ub _ _) posBlock = _
    rw [Mem.write_ne hpu]; exact hmp
  -- pd3 : undo->hand_before = hand[c][hand]
  let t4 : State := { s2 with mem := m4 }
  have l0t : t4.locals 0 = some posPtr := by simp [t4, s2, s1, Locals.upd]; exact hl0
  have l4t : t4.locals 4 = some (.int IntTy.u32 c.idx) := by simp [t4, s2, s1, Locals.upd]; exact hl4
  have l5t : t4.locals 5 = some (.int IntTy.u32 i.val) := by simp [t4, s2, s1, Locals.upd]
  have hv := ev_hand_slot_u (s := t4) hP l0t hm4p l4t hi7 l5t
  rw [enc_getD_hand] at hv
  have st3 := store_int_field (s := t4) (o := 0) (b := ub) (j := 2) (t := ⟨8, false⟩) (i := 16)
    (v := (h c i).toUInt8.toNat) (blk := U3) l2s2 hm4u (by simp [U3, U2, hU, IntTy.bytes]) hv hro
    (encodeLE_length _ _)
  let m5 := m4.write ub (0 + 16) (encodeLE 1 (h c i).toUInt8.toNat)
  have hm5p : m5 posBlock = some P := by show (m4.write ub _ _) posBlock = _; rw [Mem.write_ne hpu]; exact hm4p
  have hm5u : m5 ub = some (U3.set 16 (h c i).toUInt8) := by
    have key : ((h c i).toUInt8.toNat).toUInt8 = (h c i).toUInt8 := by
      apply UInt8.toNat_inj.mp; simp [Nat.toUInt8, UInt8.toNat_ofNat]
    show (m4.write ub (0 + 16) _) ub = _
    rw [write1_set hm4u (by simp [U3, U2, hU]), key]
  -- pd4 : --hand[c][hand]
  let t5 : State := { s2 with mem := m5 }
  have hv' := ev_hand_slot_u (s := t5) hP l0t hm5p l4t hi7 l5t
  rw [enc_getD_hand] at hv'
  have hb := UInt8.toNat_lt (h c i).toUInt8
  have hbv : (h c i).toUInt8.toNat = h c i % 256 := by simp [Nat.toUInt8, UInt8.toNat_ofNat]
  have hsub : EvE Gen.prog t5 (.cast ⟨8, false⟩ (.bin .sub (some ⟨32, true⟩) (.cast ⟨32, true⟩
      (.load (.int ⟨8, false⟩) (.index (.index (.field (.var 0) 81) (.var 4) 7) (.var 5) 1)))
      (.const (.int ⟨32, true⟩ 1)))) (.int IntTy.u8 ((h c i - 1) % 256)) := by
    have c1 : evalCast ⟨32, true⟩ (.int IntTy.u8 (h c i).toUInt8.toNat) = .ok (i32 ((h c i % 256 : Nat) : Int)) := by
      rw [hbv, i32_nat _ (by omega)]
      simp [evalCast, IntTy.u8, IntTy.i32, IntTy.toInt, IntTy.wrap, IntTy.modulus]; omega
    have hlt : h c i % 256 < 256 := Nat.mod_lt _ (by decide)
    refine EvE.cast (EvE.bin (EvE.cast hv' c1) (EvE.const (.int ⟨32, true⟩ 1))
      (sub_i32 _ 1 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega))) ?_
    simp only [evalCast, i32, IntTy.i32, if_true]
    rw [toInt_wrap32 _ (by omega) (by omega)]
    simp only [IntTy.wrap, IntTy.modulus, IntTy.u8, Res.ok.injEq, Val.int.injEq, true_and]
    rw [show ((2 ^ 8 : Nat) : Int) = 256 by rfl]
    omega
  have st4 := st_hand_slot_u (s := t5) hP l0t hm5p l4t hi7 l5t hsub hro
  let m6 := m5.write posBlock (81 + 7 * c.idx + i.val) (encodeLE 1 ((h c i - 1) % 256))
  have hm6p : m6 posBlock = some (enc pa (hupd h c i (h c i - 1)) c kb kw) := by
    have hc : c.idx < 2 := by cases c <;> decide
    show (m5.write posBlock _ _) posBlock = _
    rw [write1_set hm5p (by rw [hP]; omega), toUInt8_mod, enc_set_hand]
  refine ⟨{ s2 with mem := m6 }, U3.set 16 (h c i).toUInt8,
    ExS.seq e0 (ExS.seq (ExS.seq c1 st1) (ExS.seq st2 (ExS.seq st3 st4))), rfl, hm6p, ?_, by simp [U3, U2, hU],
    ?_, ?_, ?_⟩
  · show (m5.write posBlock _ _) ub = _; rw [Mem.write_ne (Ne.symm hpu)]; exact hm5u
  · simp [U3, U2, List.getD_eq_getElem?_getD, List.getElem?_set, hU]
  · intro x a b; show (m5.write posBlock _ _) x = _
    simp only [m5, m4, m3]; rw [Mem.write_ne a, Mem.write_ne b, Mem.write_ne b, Mem.write_ne b]
  · intro x hx; simp [s2, s1, Locals.upd, show x ≠ 5 by omega, show x ≠ 6 by omega]

end Shogi.C.Proofs
