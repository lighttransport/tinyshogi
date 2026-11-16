/-
  T8: `make_legal_probe`, part 3 — the prefix (copy the move, start the undo
  record).
-/
import Shogi.C.Proofs.Probe2

namespace Shogi.C.Proofs
open MiniC Shogi Shogi.C

def wrb (blk : List UInt8) (o : Nat) (bs : List UInt8) : List UInt8 := blk.take o ++ bs ++ blk.drop (o + bs.length)

theorem wrb_length (blk : List UInt8) (o : Nat) (bs : List UInt8) (h : o + bs.length ≤ blk.length) :
    (wrb blk o bs).length = blk.length := by simp [wrb]; omega

theorem write_some {m : Mem} {b o : Nat} {bs : List UInt8} {blk : Block} (hb : m b = some blk) :
    (m.write b o bs) b = some (wrb blk o bs) := by rw [write_map, hb]; rfl

def ub1 (UB MV : List UInt8) (c : Nat) (kbc : UInt8) : List UInt8 :=
  wrb (wrb (wrb (wrb (wrb (wrb UB 0 MV) 8 (encodeLE 4 c)) 13 [0]) 14 [kbc]) 15 [255]) 16 [0]

theorem ub1_length (UB MV : List UInt8) (c : Nat) (kbc : UInt8) (hU : UB.length = 20) (hM : MV.length = 5) :
    (ub1 UB MV c kbc).length = 20 := by
  simp [ub1, wrb, hU, hM, encodeLE_length]

theorem load_u8_at {s : State} {e : Expr} {b o : Nat} {blk : Block} (he : EvE Gen.prog s e (.ptr b o))
    (hb : s.mem b = some blk) (ho : o < blk.length) :
    EvE Gen.prog s (.load (.int ⟨8, false⟩) e) (.int IntTy.u8 (blk.getD o 0).toNat) := by
  refine EvE.load he ?_
  simp only [load, Ty.size, IntTy.bytes, show (8 : Nat) / 8 = 1 by rfl]
  rw [readByte hb o ho]; simp [Res.bind, decodeLE, IntTy.u8, pure]

def pbPre : Stmt := .seq pb0 (.seq pb1 (.seq pb2 (.seq pb3 (.seq pb4 (.seq pb5 (.seq pb6 (.seq pb7 (.seq pb8 pb9))))))))

/-- After the prefix: locals and the three blocks the probe touches. -/
structure PreOut (s : State) (m : Mem) (mvb ub n : Nat) (sd : Color) (P MV U : List UInt8) : Prop where
  l0 : s.locals 0 = some posPtr
  l1 : s.locals 1 = some (.ptr n 0)
  l2 : s.locals 2 = some (.ptr ub 0)
  l4 : s.locals 4 = some (.int IntTy.u32 sd.idx)
  ro : s.ro = false
  mp : s.mem posBlock = some P
  mn : s.mem n = some MV
  mu : s.mem ub = some U
  other : ∀ x, x ≠ 0 → x ≠ n → x ≠ ub → s.mem x = m x
  fresh : Fresh s.mem (n + 1)

theorem probe_pre {m : Mem} {mvb ub n : Nat} {pa h sd kb kw} {MV UB : List UInt8}
    (hp : m posBlock = some (enc pa h sd kb kw)) (hmv : m mvb = some MV) (hub : m ub = some UB)
    (hMV : MV.length = 5) (hUB : UB.length = 20) (hf : Fresh m n) (h64 : n + 1 < 2 ^ 64)
    (hmvb0 : mvb ≠ 0) (hub0 : ub ≠ 0) (hpu : posBlock ≠ ub) :
    ∃ s, ExS Gen.prog ⟨frameLocals Gen.make_legal_probe.params [posPtr, .ptr mvb 0, .ptr ub 0], m, false⟩
        pbPre .normal s ∧
      PreOut s m mvb ub n sd (enc pa h sd kb kw) MV
        (ub1 UB MV sd.idx ((enc pa h sd kb kw).getD (112 + sd.idx) 0)) := by
  have hnmv : n ≠ mvb := fun e => by rw [← e, hf.2.2 n (Nat.le_refl _)] at hmv; cases hmv
  have hnub : n ≠ ub := fun e => by rw [← e, hf.2.2 n (Nat.le_refl _)] at hub; cases hub
  have hnp : n ≠ posBlock := fun e => by rw [← e, hf.2.2 n (Nat.le_refl _)] at hp; cases hp
  have hn0 := hf.2.1
  let P := enc pa h sd kb kw
  have hPl : P.length = 114 := enc_length _ _ _ _ _
  let s0 : State := ⟨frameLocals Gen.make_legal_probe.params [posPtr, .ptr mvb 0, .ptr ub 0], m, false⟩
  -- pb0
  let sA : State := { s0 with locals := s0.locals.upd 3 (.ptr mvb 0) }
  have e0 : ExS Gen.prog s0 pb0 .normal sA := ExS.set (EvE.var rfl)
  -- pb1
  let m1 := (m.upd 0 (encodeLE 8 (n + 1))).upd n (List.replicate 5 0)
  let sB : State := { sA with mem := m1, locals := sA.locals.upd 1 (.ptr n 0) }
  have e1 : ExS Gen.prog sA pb1 .normal sB := exec_alloc (s := sA) (hf.allocAt (by omega)) 1 5
  have hm1 : ∀ x, x ≠ 0 → x ≠ n → m1 x = m x := fun x a b => by simp only [m1]; rw [Mem.upd_ne b, Mem.upd_ne a]
  have hm1n : m1 n = some (List.replicate 5 0) := Mem.upd_eq
  -- pb2 : copy the move
  let m2 := m1.write n 0 MV
  let sC : State := { sB with mem := m2 }
  have e2 : ExS Gen.prog sB pb2 .normal sC := by
    refine ExS.memcpy (bd := n) (od := 0) (bs := mvb) (os := 0) (t := ⟨64, false⟩) (k := 5) (bytes := MV) (EvE.var (by simp [sB, Locals.upd]))
      (EvE.var (by simp [sB, sA, Locals.upd])) (EvE.const _) rfl (by simp [hnmv]) ?_ ?_
    · simp [readBytes, sB, hm1 mvb hmvb0 hnmv.symm, hmv, hMV, List.take_of_length_le]
    · exact writeBytes_ok hm1n (by simp [hMV])
  have hm2 : ∀ x, x ≠ n → m2 x = m1 x := fun x hx => Mem.write_ne hx
  have hm2n : m2 n = some MV := by
    show (m1.write n 0 MV) n = _
    rw [write_some hm1n]; simp [wrb, hMV, List.take_of_length_le]
  -- pb3 : color
  let c := sd
  let sD : State := { sC with locals := sC.locals.upd 4 (.int IntTy.u32 c.idx) }
  have hmp2 : m2 posBlock = some P := by rw [hm2 _ hnp.symm, hm1 _ (by decide) hnp.symm]; exact hp
  have e3 : ExS Gen.prog sC pb3 .normal sD := by
    apply ExS.set
    refine EvE.load (pa := .ptr posBlock 96) (EvE.field (EvE.var rfl) (by simp [ptrAddN, posPtr, sC, hmp2, hPl])) ?_
    simp only [load, readBytes, sC, hmp2, hPl, Ty.size, IntTy.bytes]
    rw [if_pos (by omega), enc_side]
    simp only [Res.bind_eq, Res.bind_ok, pure]
    rw [decode_le32 sd.idx (by cases sd <;> decide)]; rfl
  -- pb4 : undo.move = move
  let m3 := m2.write ub 0 MV
  let sE : State := { sD with mem := m3 }
  have hmub2 : m2 ub = some UB := by rw [hm2 _ hnub.symm, hm1 _ hub0 hnub.symm]; exact hub
  have e4 : ExS Gen.prog sD pb4 .normal sE := by
    refine ExS.memcpy (bd := ub) (od := 0 + 0) (bs := n) (os := 0) (t := ⟨64, false⟩) (k := 5) (bytes := MV)
      (EvE.field (EvE.var (by simp [sD, sC, sB, sA, Locals.upd]; rfl)) (by simp [ptrAddN, sD, sC, hmub2, hUB]))
      (EvE.var (by simp [sD, sC, sB, Locals.upd])) (EvE.const _) rfl (by simp; exact fun h => hnub h.symm) ?_ ?_
    · simp [readBytes, sD, sC, hm2n, hMV, List.take_of_length_le]
    · exact writeBytes_ok hmub2 (by simp [hMV, hUB])
  have l2 : ∀ (st : State), st.locals = sD.locals → st.locals 2 = some (.ptr ub 0) := fun st e => by
    rw [e]; simp [sD, sC, sB, sA, Locals.upd]; rfl
  -- pb5..pb9 : stores into the undo record
  have hc2 : c.idx < 2 := by cases c <;> decide
  let U1 := wrb UB 0 MV
  have hU1 : m3 ub = some U1 := write_some hmub2
  have hU1l : U1.length = 20 := by rw [wrb_length _ _ _ (by rw [hMV, hUB]; decide)]; exact hUB
  have e5 := store_int_field (s := sE) (o := 0) (b := ub) (j := 2) (t := ⟨32, false⟩) (i := 8) (v := c.idx)
    (e := .var 4) (blk := U1) (l2 sE rfl) hU1 (by rw [hU1l]; decide) (EvE.var (by simp [sE, sD, Locals.upd]; rfl)) rfl
    (encodeLE_length _ _)
  let m4 := m3.write ub (0 + 8) (encodeLE 4 c.idx)
  let U2 := wrb U1 8 (encodeLE 4 c.idx)
  have hU2 : m4 ub = some U2 := write_some hU1
  have hU2l : U2.length = 20 := by rw [wrb_length _ _ _ (by simp [hU1l, encodeLE_length])]; exact hU1l
  have e6 := store_int_field (s := { sE with mem := m4 }) (o := 0) (b := ub) (j := 2) (t := ⟨8, false⟩) (i := 13)
    (v := 0) (e := .cast ⟨8, false⟩ (.const (.int ⟨32, true⟩ 0))) (blk := U2) (l2 _ rfl) hU2 (by rw [hU2l]; decide) (EvE_of_eval (n := 3) (by rfl)) rfl (encodeLE_length _ _)
  let m5 := m4.write ub (0 + 13) (encodeLE 1 0)
  let U3 := wrb U2 13 [0]
  have hU3 : m5 ub = some U3 := write_some hU2
  have hU3l : U3.length = 20 := by rw [wrb_length _ _ _ (by simp [hU2l])]; exact hU2l
  have hmp5 : m5 posBlock = some P := by
    simp only [m5, m4, m3]; rw [Mem.write_ne hpu, Mem.write_ne hpu, Mem.write_ne hpu]; exact hmp2
  let kbc := P.getD (112 + c.idx) 0
  have ev7 : EvE Gen.prog { sE with mem := m5 }
      (.load (.int ⟨8, false⟩) (.index (.field (.var 0) 112) (.var 4) 1)) (.int IntTy.u8 (P.getD (0 + 112 + c.idx * 1) 0).toNat) :=
    load_u8_at (b := posBlock) (o := 0 + 112 + c.idx * 1)
      (EvE.index (pb := .ptr posBlock (0 + 112))
        (EvE.field (EvE.var (show ({ sE with mem := m5 } : State).locals 0 = some posPtr from rfl))
          (by simp [ptrAddN, posPtr, hmp5, hPl]))
        (EvE.var (show ({ sE with mem := m5 } : State).locals 4 = some (.int IntTy.u32 c.idx) by
          simp [sE, sD, Locals.upd]))
        (by simp [ptrAdd, IntTy.u32, hmp5, hPl, ptrAddN]; omega))
      hmp5 (by rw [hPl]; omega)
  have hk0 : (0 + 112 + c.idx * 1) = 112 + c.idx := by omega
  rw [hk0] at ev7
  have e7 := store_int_field (s := { sE with mem := m5 }) (o := 0) (b := ub) (j := 2) (t := ⟨8, false⟩) (i := 14)
    (v := kbc.toNat) (blk := U3) (l2 _ rfl) hU3 (by rw [hU3l]; decide) ev7 rfl (encodeLE_length _ _)
  have hkb1 : encodeLE 1 kbc.toNat = [kbc] := by simp [encodeLE]
  let m6 := m5.write ub (0 + 14) (encodeLE 1 kbc.toNat)
  let U4 := wrb U3 14 [kbc]
  have hU4 : m6 ub = some U4 := by simp only [m6, hkb1]; exact write_some hU3
  have hU4l : U4.length = 20 := by rw [wrb_length _ _ _ (by simp [hU3l])]; exact hU3l
  have e8 := store_int_field (s := { sE with mem := m6 }) (o := 0) (b := ub) (j := 2) (t := ⟨8, false⟩) (i := 15)
    (v := 255) (e := .cast ⟨8, false⟩ (.const (.int ⟨32, true⟩ 255))) (blk := U4) (l2 _ rfl) hU4
    (by rw [hU4l]; decide) (EvE_of_eval (n := 3) (by rfl)) rfl (encodeLE_length _ _)
  let m7 := m6.write ub (0 + 15) (encodeLE 1 255)
  let U5 := wrb U4 15 [255]
  have hU5 : m7 ub = some U5 := write_some hU4
  have hU5l : U5.length = 20 := by rw [wrb_length _ _ _ (by simp [hU4l])]; exact hU4l
  have e9 := store_int_field (s := { sE with mem := m7 }) (o := 0) (b := ub) (j := 2) (t := ⟨8, false⟩) (i := 16)
    (v := 0) (e := .cast ⟨8, false⟩ (.const (.int ⟨32, true⟩ 0))) (blk := U5) (l2 _ rfl) hU5
    (by rw [hU5l]; decide) (EvE_of_eval (n := 3) (by rfl)) rfl (encodeLE_length _ _)
  let m8 := m7.write ub (0 + 16) (encodeLE 1 0)
  have hU6 : m8 ub = some (ub1 UB MV sd.idx kbc) := write_some hU5
  have hne : ∀ x, x ≠ ub → m8 x = m2 x := fun x hx => by
    simp only [m8, m7, m6, m5, m4, m3]
    rw [Mem.write_ne hx, Mem.write_ne hx, Mem.write_ne hx, Mem.write_ne hx, Mem.write_ne hx, Mem.write_ne hx]
  refine ⟨{ sE with mem := m8 }, ExS.seq e0 (ExS.seq e1 (ExS.seq e2 (ExS.seq e3 (ExS.seq e4 (ExS.seq e5
    (ExS.seq e6 (ExS.seq e7 (ExS.seq e8 e9)))))))), ?_⟩
  refine ⟨rfl, by simp [sE, sD, sC, sB, Locals.upd], by simp [sE, sD, sC, sB, sA, Locals.upd]; rfl,
    by simp [sE, sD, Locals.upd]; rfl, rfl, ?_, ?_, hU6, ?_, ?_⟩
  · show m8 posBlock = _; rw [hne _ hpu]; exact hmp2
  · show m8 n = _; rw [hne _ hnub]; exact hm2n
  · intro x a b d; show m8 x = _; rw [hne _ d, hm2 _ b, hm1 _ a b]
  · have hf1 : Fresh m2 (n + 1) := (hf.after_alloc _).write hn0
    exact (((((hf1.write hub0).write hub0).write hub0).write hub0).write hub0).write hub0

end Shogi.C.Proofs
