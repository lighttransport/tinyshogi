/-
  T8: `unmake_legal_probe` undoes `make_legal_probe`: the position block goes
  back to `encode p`.
-/
import Shogi.C.Proofs.Probe9

namespace Shogi.C.Proofs
open MiniC Shogi Shogi.C

def um0 : Stmt := (.seq (.alloc 2 5) (.memcpy (.var 2) (.field (.var 1) 0) (.const (.int ⟨64, false⟩ 5))))
def um1 : Stmt := (.set 3 (.load (.int ⟨32, false⟩) (.field (.var 1) 8)))
def um2 : Stmt := (.store (.int ⟨32, false⟩) (.field (.var 0) 96) (.var 3))
def um3 : Stmt := (.store (.int ⟨8, false⟩) (.index (.field (.var 0) 112) (.var 3) 1) (.load (.int ⟨8, false⟩) (.field (.var 1) 14)))
def um4 : Stmt := (.ite (.bin .eq (some ⟨32, true⟩) (.cast ⟨32, true⟩ (.load (.int ⟨8, false⟩) (.field (.var 2) 0))) (.const (.int ⟨32, true⟩ 255))) (.store (.int ⟨8, false⟩) (.index (.field (.var 0) 0) (.load (.int ⟨8, false⟩) (.field (.var 2) 1)) 1) (.cast ⟨8, false⟩ (.const (.int ⟨32, true⟩ 0)))) (.seq (.store (.int ⟨8, false⟩) (.index (.field (.var 0) 0) (.load (.int ⟨8, false⟩) (.field (.var 2) 0)) 1) (.load (.int ⟨8, false⟩) (.field (.var 2) 2))) (.store (.int ⟨8, false⟩) (.index (.field (.var 0) 0) (.load (.int ⟨8, false⟩) (.field (.var 2) 1)) 1) (.load (.int ⟨8, false⟩) (.field (.var 1) 13)))))
def um5 : Stmt := (.ite (.bin .ne (some ⟨32, true⟩) (.cast ⟨32, true⟩ (.load (.int ⟨8, false⟩) (.field (.var 1) 15))) (.const (.int ⟨32, true⟩ 255))) (.store (.int ⟨8, false⟩) (.index (.index (.field (.var 0) 81) (.var 3) 7) (.load (.int ⟨8, false⟩) (.field (.var 1) 15)) 1) (.load (.int ⟨8, false⟩) (.field (.var 1) 16))) .skip)
theorem unmake_body_eq : Gen.unmake_legal_probe.body = (.seq um0 (.seq um1 (.seq um2 (.seq um3 (.seq um4 um5))))) := rfl

theorem enc_congr {pa1 pa2 : Square → Option Piece} {h1 h2 : Color → Fin 7 → Nat} {sd : Color} {kb1 kw1 kb2 kw2 : UInt8}
    (hp : ∀ y, pa1 y = pa2 y) (hh : ∀ c i, (h1 c i).toUInt8 = (h2 c i).toUInt8) (hb : kb1 = kb2) (hw : kw1 = kw2) :
    enc pa1 h1 sd kb1 kw1 = enc pa2 h2 sd kb2 kw2 := by
  unfold enc
  have e1 : (fun s => pieceByte (pa1 s)) = (fun s => pieceByte (pa2 s)) := funext fun y => by rw [hp y]
  have e2 : (fun i => (h1 .black i).toUInt8) = (fun i => (h2 .black i).toUInt8) := funext fun i => hh _ _
  have e3 : (fun i => (h1 .white i).toUInt8) = (fun i => (h2 .white i).toUInt8) := funext fun i => hh _ _
  rw [e1, e2, e3, hb, hw]

section handx
variable {s : State} {P : List UInt8} (hP : P.length = 114) (hl0 : s.locals 0 = some posPtr)
  (hmp : s.mem posBlock = some P) {c : Color} (hl3 : s.locals 3 = some (.int IntTy.u32 c.idx))
  {e : Expr} {i : Nat} (hi : i < 7) (he : EvE Gen.prog s e (.int IntTy.u8 i))

include hP hl0 hmp hl3 hi he in
theorem st_hand_e {ev : Expr} {v : Nat} (hv : EvE Gen.prog s ev (.int IntTy.u8 v)) (hro : s.ro = false) :
    ExS Gen.prog s (.store (.int ⟨8, false⟩) (.index (.index (.field (.var 0) 81) (.var 3) 7) e 1) ev) .normal
      { s with mem := s.mem.write posBlock (81 + 7 * c.idx + i) (encodeLE 1 v) } := by
  have hc : c.idx < 2 := by cases c <;> decide
  have hptr : EvE Gen.prog s (.index (.index (.field (.var 0) 81) (.var 3) 7) e 1)
      (.ptr posBlock (81 + 7 * c.idx + i)) := by
    refine EvE.index (pb := .ptr posBlock (0 + 81 + c.idx * 7))
      (EvE.index (pb := .ptr posBlock (0 + 81)) (EvE.field (EvE.var hl0) (by simp [ptrAddN, posPtr, hmp, hP]))
        (EvE.var hl3) (by simp [IntTy.u32, ptrAddN, hmp, hP]; omega)) he ?_
    simp [IntTy.u8, ptrAddN, hmp, hP]
    rw [if_pos (by omega)]; congr 2; omega
  have := ExS.store (p := Gen.prog) (s := s) (ty := .int ⟨8, false⟩) hptr hv hro
    (by simp only [store, ite_true, show IntTy.u8 = (⟨8, false⟩ : IntTy) from rfl, IntTy.bytes]
        exact writeBytes_ok hmp (by simp [encodeLE_length, hP]; omega))
  simpa [IntTy.bytes] using this

end handx

def setKb (c : Color) (kbc kb kw : UInt8) : UInt8 × UInt8 :=
  match c with | .black => (kbc, kw) | .white => (kb, kbc)

theorem um_pre {M : Mem} {ub n : Nat} {pa h sd kb kw} {c : Color} {kbc : UInt8} {U MV : List UInt8}
    (hp : M posBlock = some (enc pa h sd kb kw)) (hub : M ub = some U) (hU : U.length = 20)
    (hMV : (U.drop 0).take 5 = MV) (hc : (U.drop 8).take 4 = le32 c.idx) (hk : U.getD 14 0 = kbc)
    (hf : Fresh M n) (h64 : n + 1 < 2 ^ 64) (hub0 : ub ≠ 0) (hpu : posBlock ≠ ub) :
    ∃ s, ExS Gen.prog ⟨frameLocals Gen.unmake_legal_probe.params [posPtr, .ptr ub 0], M, false⟩
        (.seq um0 (.seq um1 (.seq um2 um3))) .normal s ∧
      s.locals 0 = some posPtr ∧ s.locals 1 = some (.ptr ub 0) ∧ s.locals 2 = some (.ptr n 0) ∧
      s.locals 3 = some (.int IntTy.u32 c.idx) ∧ s.ro = false ∧
      s.mem posBlock = some (enc pa h c (setKb c kbc kb kw).1 (setKb c kbc kb kw).2) ∧
      s.mem n = some MV ∧ s.mem ub = some U ∧ Fresh s.mem (n + 1) ∧
      (∀ x, x ≠ 0 → x ≠ n → x ≠ posBlock → s.mem x = M x) := by
  have hnu : n ≠ ub := fun e => by rw [← e, hf.2.2 n (Nat.le_refl _)] at hub; cases hub
  have hnp : n ≠ posBlock := fun e => by rw [← e, hf.2.2 n (Nat.le_refl _)] at hp; cases hp
  have hn0 := hf.2.1
  let P := enc pa h sd kb kw
  have hP : P.length = 114 := enc_length _ _ _ _ _
  let s0 : State := ⟨frameLocals Gen.unmake_legal_probe.params [posPtr, .ptr ub 0], M, false⟩
  let m1 := (M.upd 0 (encodeLE 8 (n + 1))).upd n (List.replicate 5 0)
  let s1 : State := { s0 with mem := m1, locals := s0.locals.upd 2 (.ptr n 0) }
  have ea : ExS Gen.prog s0 (.alloc 2 5) .normal s1 := exec_alloc (s := s0) (hf.allocAt (by omega)) 2 5
  have hm1 : ∀ x, x ≠ 0 → x ≠ n → m1 x = M x := fun x a b => by simp only [m1]; rw [Mem.upd_ne b, Mem.upd_ne a]
  have hm1n : m1 n = some (List.replicate 5 0) := Mem.upd_eq
  have hMVl : MV.length = 5 := by rw [← hMV]; simp; omega
  let m2 := m1.write n 0 MV
  have eb : ExS Gen.prog s1 (.memcpy (.var 2) (.field (.var 1) 0) (.const (.int ⟨64, false⟩ 5))) .normal
      { s1 with mem := m2 } := by
    refine ExS.memcpy (bd := n) (od := 0) (bs := ub) (os := 0 + 0) (t := ⟨64, false⟩) (k := 5) (bytes := MV)
      (EvE.var (by simp [s1, Locals.upd])) (EvE.field (EvE.var (by simp [s1, s0, Locals.upd]; rfl))
        (by simp [ptrAddN, s1, hm1 ub hub0 (Ne.symm hnu), hub, hU])) (EvE.const _) rfl (by simp [hnu]) ?_ ?_
    · simp only [readBytes, s1, hm1 ub hub0 (Ne.symm hnu), hub, hU]; rw [if_pos (by omega)]; rw [hMV]
    · exact writeBytes_ok hm1n (by simp [hMVl])
  have hm2n : m2 n = some MV := by
    show (m1.write n 0 MV) n = _; rw [write_some hm1n]; simp [wrb, hMVl]
  have hm2 : ∀ x, x ≠ n → m2 x = m1 x := fun x hx => Mem.write_ne hx
  have hm2u : m2 ub = some U := by rw [hm2 _ (Ne.symm hnu), hm1 _ hub0 (Ne.symm hnu)]; exact hub
  have hm2p : m2 posBlock = some P := by rw [hm2 _ (Ne.symm hnp), hm1 _ (by decide) (Ne.symm hnp)]; exact hp
  let t2 : State := { s1 with mem := m2 }
  -- um1 : color
  have hc2 : c.idx < 2 := by cases c <;> decide
  let t3 : State := { t2 with locals := t2.locals.upd 3 (.int IntTy.u32 c.idx) }
  have e1 : ExS Gen.prog t2 um1 .normal t3 := by
    apply ExS.set
    refine EvE.load (pa := .ptr ub 8) (EvE.field (EvE.var (by simp [t2, s1, s0, Locals.upd]; rfl))
      (by simp [ptrAddN, t2, hm2u, hU])) ?_
    simp only [load, readBytes, t2, hm2u, hU, Ty.size, IntTy.bytes]
    rw [if_pos (by omega), hc]
    simp only [Res.bind_eq, Res.bind_ok, pure]
    rw [decode_le32 c.idx (by omega)]; rfl
  have l0 : t3.locals 0 = some posPtr := by simp [t3, t2, s1, s0, Locals.upd]; rfl
  have l3 : t3.locals 3 = some (.int IntTy.u32 c.idx) := by simp [t3, Locals.upd]
  -- um2 : side
  have e2 := store_int_field (s := t3) (o := 0) (b := posBlock) (j := 0) (t := ⟨32, false⟩) (i := 96)
    (v := c.idx) (e := .var 3) (blk := P) l0 hm2p (by rw [hP]; decide) (EvE.var l3) rfl (encodeLE_length _ _)
  let m3 := m2.write posBlock (0 + 96) (encodeLE 4 c.idx)
  let P3 := enc pa h c kb kw
  have hm3p : m3 posBlock = some P3 := by
    show (m2.write posBlock (0 + 96) _) posBlock = _
    rw [write_some hm2p]; congr 1
    simp only [wrb, encodeLE_length, Nat.zero_add]
    exact enc_set_side _ _ _ _ _ c
  have hm3o : ∀ x, x ≠ posBlock → m3 x = m2 x := fun x hx => Mem.write_ne hx
  -- um3 : king square
  let t4 : State := { t3 with mem := m3 }
  have hk1 := ev_blk_u8 (s := t4) (j := 1) (b := ub) (B := U) (by simp [t4, t3, t2, s1, s0, Locals.upd]; rfl)
    (by show m3 ub = _; rw [hm3o ub (Ne.symm hpu)]; exact hm2u) (k := 14) (by omega)
  rw [hk] at hk1
  have e3 := st_pos_u (s := t4) (base := 112) (e := .var 3) (x := c.idx) (t := IntTy.u32) (P := P3)
    (enc_length _ _ _ _ _) l0 hm3p rfl (EvE.var l3) (by omega) hk1 rfl
  let m4 := m3.write posBlock (112 + c.idx) (encodeLE 1 kbc.toNat)
  have hm4p : m4 posBlock = some (enc pa h c (setKb c kbc kb kw).1 (setKb c kbc kb kw).2) := by
    show (m3.write posBlock _ _) posBlock = _
    rw [write1_set hm3p (by rw [enc_length]; omega), enc_set_king]
    have : kbc.toNat.toUInt8 = kbc := by apply UInt8.toNat_inj.mp; simp [Nat.toUInt8, UInt8.toNat_ofNat]
    rw [this]; cases c <;> rfl
  have hm4o : ∀ x, x ≠ posBlock → m4 x = m2 x := fun x hx => by
    show (m3.write posBlock _ _) x = _; rw [Mem.write_ne hx, hm3o x hx]
  refine ⟨{ t4 with mem := m4 }, ExS.seq (ExS.seq ea eb) (ExS.seq e1 (ExS.seq e2 e3)), l0,
    by simp [t3, t2, s1, s0, Locals.upd]; rfl, by simp [t4, t3, t2, s1, Locals.upd], l3, rfl, hm4p,
    by show m4 n = _; rw [hm4o n hnp]; exact hm2n, by show m4 ub = _; rw [hm4o ub (Ne.symm hpu)]; exact hm2u, ?_, ?_⟩
  · have hpb : posBlock < n := Nat.lt_of_not_le (fun hc => by have := hf.2.2 posBlock hc; rw [this] at hp; cases hp)
    have hf2 : Fresh m2 (n + 1) := (hf.after_alloc _).write hn0
    exact hf2.congr (by show m4 0 = _; rw [hm4o 0 (by decide)]) (fun x hx => by
      show m4 x = _; rw [hm4o x (by omega)])
  · intro x a b d; show m4 x = _; rw [hm4o x d, hm2 x b, hm1 x a b]

end Shogi.C.Proofs
