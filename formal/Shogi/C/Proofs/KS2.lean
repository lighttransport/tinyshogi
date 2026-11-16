/-
  T8: `king_safety_prepare`, part 2 — one ray: check and pin detection.
-/
import Shogi.C.Proofs.KS1

namespace Shogi.C.Proofs
open MiniC Shogi Shogi.C Shogi.Tables

def kc0 : Stmt := (.set 10 (.load (.int ⟨8, false⟩) (.index (.index (.index (.const (.ptr 8194 0)) (.load (.int ⟨8, false⟩) (.field (.var 3) 0)) 64) (.var 7) 8) (.var 9) 1)))
def kc1 : Stmt := (.set 11 (.load (.int ⟨8, false⟩) (.index (.field (.var 1) 0) (.var 10) 1)))
def kc2 : Stmt := (.ite (.bin .eq (some ⟨32, true⟩) (.cast ⟨32, true⟩ (.var 11)) (.const (.int ⟨32, true⟩ 0))) .cont .skip)
def kc3 : Stmt := (.seq (.call (some 12) 1 [(.var 11)]) (.ite (.bin .eq (some ⟨32, false⟩) (.cast ⟨32, false⟩ (.var 12)) (.cast ⟨32, false⟩ (.var 2))) (.seq (.ite (.bin .ne (some ⟨32, true⟩) (.cast ⟨32, true⟩ (.var 8)) (.const (.int ⟨32, true⟩ 255))) .brk .skip) (.seq (.set 8 (.var 10)) .cont)) .skip))
def kc4 : Stmt := (.seq (.call (some 14) 2 [(.var 11)]) (.set 13 (.cast ⟨8, false⟩ (.bin .ne (some ⟨32, true⟩) (.bin .ne (some ⟨32, true⟩) (.bin .band (some ⟨32, true⟩) (.cast ⟨32, true⟩ (.load (.int ⟨16, false⟩) (.index (.index (.index (.const (.ptr 8196 0)) (.var 5) 1296) (.load (.int ⟨8, false⟩) (.field (.var 3) 0)) 16) (.var 7) 2))) (.bin .shl (some ⟨32, true⟩) (.cast ⟨32, true⟩ (.cast ⟨16, false⟩ (.const (.int ⟨32, false⟩ 1)))) (.cast ⟨32, false⟩ (.var 14)))) (.const (.int ⟨32, true⟩ 0))) (.const (.int ⟨32, true⟩ 0))))))
def kc5 : Stmt := (.ite (.bin .eq (some ⟨32, true⟩) (.cast ⟨32, true⟩ (.var 8)) (.const (.int ⟨32, true⟩ 255))) (.ite (.var 13) (.store (.int ⟨8, false⟩) (.field (.var 3) 2) (.cast ⟨8, false⟩ (.bin .ne (some ⟨32, true⟩) (.const (.int ⟨32, true⟩ 1)) (.const (.int ⟨32, true⟩ 0))))) .skip) (.ite (.var 13) (.store (.int ⟨8, false⟩) (.index (.field (.var 3) 3) (.var 8) 1) (.cast ⟨8, false⟩ (.bin .ne (some ⟨32, true⟩) (.const (.int ⟨32, true⟩ 1)) (.const (.int ⟨32, true⟩ 0))))) .skip))
def kc6 : Stmt := .brk
def kCond : Expr := (.bin .lt (some ⟨32, true⟩) (.cast ⟨32, true⟩ (.var 9)) (.cast ⟨32, true⟩ (.load (.int ⟨8, false⟩) (.index (.index (.const (.ptr 8195 0)) (.load (.int ⟨8, false⟩) (.field (.var 3) 0)) 8) (.var 7) 1))))
def kStep9 : Stmt := (.set 9 (.cast ⟨8, false⟩ (.bin .add (some ⟨32, true⟩) (.cast ⟨32, true⟩ (.var 9)) (.const (.int ⟨32, true⟩ 1)))))
def kBody0 : Stmt := .ite kCond (.seq kc0 (.seq kc1 (.seq kc2 (.seq kc3 (.seq kc4 (.seq kc5 kc6)))))) .brk
theorem ks_loop0_eq : Gen.king_safety_prepare_loop0 = .loop kBody0 kStep9 := rfl

/-- The C scan of one ray from the king (`mk` the ray mask of the attacker):
    whether it gives check, and which own piece (if any) it pins. -/
def kres (p : Position) (c : Color) (mk : Nat) : List Square → Option Square → Bool × Option Square
  | [], _ => (false, none)
  | sq :: rest, own =>
    match p.pieceAt sq with
    | none => kres p c mk rest own
    | some q =>
      if q.color = c then
        match own with
        | some _ => (false, none)
        | none => kres p c mk rest (some sq)
      else
        let a := decide (mk &&& 2 ^ q.type.code ≠ 0)
        match own with
        | none => (a, none)
        | some o => (false, if a then some o else none)

/-- What the scan writes into the 84-byte record. -/
def applyK (S : List UInt8) : Bool × Option Square → List UInt8
  | (chk, pin) =>
    let S1 := if chk then S.set 2 1 else S
    match pin with
    | some o => S1.set (3 + o.val) 1
    | none => S1

def ownByte : Option Square → Nat
  | some o => o.val
  | none => 255

theorem evBoard1 {s : State} {p : Position} {j k : Nat} (hk : k < 81)
    (h1 : s.locals 1 = some posPtr) (hj : s.locals j = some (.int IntTy.u8 k))
    (hm : s.mem posBlock = some (encode p)) :
    EvE Gen.prog s (.load (.int ⟨8, false⟩) (.index (.field (.var 1) 0) (.var j) 1)) (.int IntTy.u8 (bb p k)) := by
  have hlen := encode_length p
  refine EvE.load (pa := .ptr posBlock k) (EvE.index (pb := .ptr posBlock (0 + 0))
    (EvE.field (EvE.var h1) (by simp [ptrAddN, posPtr, hm, hlen])) (EvE.var hj) ?_) ?_
  · simp [IntTy.u8, ptrAddN, hm, hlen]; omega
  · simp only [load, Ty.size, IntTy.bytes, show (8 : Nat) / 8 = 1 by rfl, readBoard hm k hk]
    simp [Res.bind, decodeLE, bb, hk]; rfl

/-- The loop invariant of one ray scan. -/
structure KInv (p : Position) (c a : Color) (t : Square) (r : Nat) (Sb : Nat) (S : List UInt8) (v0 : Val)
    (s : State) (k : Nat) (own : Option Square) : Prop where
  l0 : s.locals 0 = some v0
  l1 : s.locals 1 = some posPtr
  l2 : s.locals 2 = some (.int IntTy.u32 c.idx)
  l3 : s.locals 3 = some (.ptr Sb 0)
  l5 : s.locals 5 = some (.int IntTy.u32 a.idx)
  l7 : s.locals 7 = some (.int IntTy.u32 r)
  l8 : s.locals 8 = some (.int IntTy.u8 (ownByte own))
  l9 : s.locals 9 = some (.int IntTy.u8 k)
  mp : s.mem posBlock = some (encode p)
  mS : s.mem Sb = some S
  g3 : s.mem 8194 = some Gen.global_attack_rays
  g4 : s.mem 8195 = some Gen.global_attack_ray_length
  g5 : s.mem 8196 = some Gen.global_attack_ray_masks
  Sl : S.length = 84
  S0 : S.getD 0 0 = t.val.toUInt8
  ro : s.ro = false
  Sbp : Sb ≠ posBlock
  Sbg : Sb ≠ 8194 ∧ Sb ≠ 8195 ∧ Sb ≠ 8196

theorem ownByte_lt (o : Option Square) : ownByte o < 256 := by
  cases o with
  | none => decide
  | some x => have := x.isLt; simp [ownByte]; omega

theorem kbody_spec {p : Position} {c a : Color} {t : Square} {r Sb : Nat} {S : List UInt8} {v0 : Val} (hr : r < 8)
    (ha : a = c.opp) {s : State} {k : Nat} {own : Option Square} (hk : k < (ray t (rdir r)).length)
    (hI : KInv p c a t r Sb S v0 s k own) :
    ∃ o s1, ExS Gen.prog s kBody0 o s1 ∧
      ((o = .cont ∧ s1.mem = s.mem ∧ ∃ own', KInv p c a t r Sb S v0 s1 k own' ∧
          kres p c (rayMask a (rdir r)) ((ray t (rdir r)).drop k) own =
          kres p c (rayMask a (rdir r)) ((ray t (rdir r)).drop (k + 1)) own') ∨
       (o = .brk ∧ s1.mem Sb = some (applyK S (kres p c (rayMask a (rdir r)) ((ray t (rdir r)).drop k) own)) ∧
          (∀ x, x ≠ Sb → s1.mem x = s.mem x) ∧ s1.ro = s.ro ∧
          ∀ i, i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 5 ∨ i = 7 → s1.locals i = s.locals i)) := by
  have hl8 := ray_length_le t (rdir r)
  let sq := (ray t (rdir r))[k]
  have hsq := sq.isLt
  have hlen := evRayLen (s := s) hI.l3 hI.mS hI.Sl hI.S0 hr hI.l7 hI.g4
  have hcond : EvE Gen.prog s kCond (boolVal true) := by
    refine EvE.bin (EvE.cast (EvE.var hI.l9) rfl) (EvE.cast hlen rfl) ?_
    simp [evalBin, isPtr, evalBinInt, binInt, intOf, IntTy.u8, evalCast, IntTy.modulus, IntTy.toInt, Res.bind,
      Nat.mod_eq_of_lt (show k < 4294967296 by omega),
      Nat.mod_eq_of_lt (show (ray t (rdir r)).length < 4294967296 by omega),
      show ¬ (2147483648 ≤ k) by omega, show ¬ (2147483648 ≤ (ray t (rdir r)).length) by omega]
    rw [decide_eq_true hk]
  -- kc0, kc1
  have hrs := evRaySq (s := s) hI.l3 hI.mS hI.Sl hI.S0 hr hk hI.l7 hI.l9 hI.g3
  let s1 : State := { s with locals := s.locals.upd 10 (.int IntTy.u8 sq.val) }
  have e0 : ExS Gen.prog s kc0 .normal s1 := ExS.set hrs
  have hbd := evBoard1 (s := s1) (j := 10) hsq (by simp [s1, Locals.upd]; exact hI.l1) (by simp [s1, Locals.upd])
    hI.mp
  let b := bb p sq.val
  have hb := bb_lt p sq.val
  let s2 : State := { s1 with locals := s1.locals.upd 11 (.int IntTy.u8 b) }
  have e1 : ExS Gen.prog s1 kc1 .normal s2 := ExS.set hbd
  have l11 : s2.locals 11 = some (.int IntTy.u8 b) := by simp [s2, Locals.upd]
  have hz : EvE Gen.prog s2 (.bin .eq (some ⟨32, true⟩) (.cast ⟨32, true⟩ (.var 11)) (.const (.int ⟨32, true⟩ 0)))
      (boolVal (decide (b = 0))) := EvE_of_eval (evEq0 s2 hb l11)
  have hs2 : ∀ x, x ≠ 10 → x ≠ 11 → s2.locals x = s.locals x := fun x a b => by simp [s2, s1, Locals.upd, a, b]
  have hdrop : (ray t (rdir r)).drop k = sq :: (ray t (rdir r)).drop (k + 1) := List.drop_eq_getElem_cons hk
  have hpre : ∀ {rest o s'}, ExS Gen.prog s2 rest o s' → ExS Gen.prog s (.seq kc0 (.seq kc1 rest)) o s' :=
    fun h => ExS.seq e0 (ExS.seq e1 h)
  have hite : ∀ {body o s'}, ExS Gen.prog s body o s' → ExS Gen.prog s (.ite kCond body .brk) o s' :=
    fun h => ExS.ite (bc := true) hcond rfl h
  have hI2 : ∀ (st : State) (o : Option Square), st.mem = s.mem → st.ro = s.ro →
      (∀ x, x ≠ 8 → x ≠ 10 → x ≠ 11 → x ≠ 12 → x ≠ 13 → x ≠ 14 → st.locals x = s.locals x) →
      st.locals 8 = some (.int IntTy.u8 (ownByte o)) → KInv p c a t r Sb S v0 st k o := by
    intro st o hm hro hl h8
    exact ⟨by rw [hl 0 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hI.l0,
      by rw [hl 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hI.l1,
      by rw [hl 2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hI.l2,
      by rw [hl 3 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hI.l3,
      by rw [hl 5 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hI.l5,
      by rw [hl 7 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hI.l7,
      h8, by rw [hl 9 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hI.l9,
      by rw [hm]; exact hI.mp, by rw [hm]; exact hI.mS, by rw [hm]; exact hI.g3, by rw [hm]; exact hI.g4,
      by rw [hm]; exact hI.g5, hI.Sl, hI.S0, by rw [hro]; exact hI.ro, hI.Sbp, hI.Sbg⟩
  by_cases hb0 : b = 0
  · -- empty: continue
    have hpn : p.pieceAt sq = none := by
      have := isEmpty_bb p sq; simp only [b] at hb0; rw [hb0] at this; simpa [Position.isEmpty] using this
    refine ⟨.cont, s2, hite (hpre (ExS.seq_cont (ExS.ite (bc := true) hz (by simp [truthy_boolVal, hb0]) ExS.cont))),
      Or.inl ⟨rfl, rfl, own, hI2 s2 own rfl rfl (fun x _ a b _ _ _ => hs2 x a b)
        (by rw [hs2 8 (by decide) (by decide)]; exact hI.l8), ?_⟩⟩
    rw [hdrop]; simp only [kres, hpn]
  · obtain ⟨q, hq⟩ : ∃ q, p.pieceAt sq = some q := by
      cases h : p.pieceAt sq with
      | none => exfalso; apply hb0; simp [b, bb, hsq, h, pieceByte]
      | some q => exact ⟨q, rfl⟩
    have hbq : b = q.code := by simp [b, bb, hsq, hq, pieceByte_toNat]
    have hpcol : run Gen.fid_shogi_piece_color [u8 q.code] = some (some (u32 q.color.idx)) := by
      obtain ⟨qc, qt⟩ := q; cases qc <;> cases qt <;> decide +kernel
    have l11' : s2.locals 11 = some (u8 q.code) := by rw [l11, hbq]; rfl
    let s3 : State := { s2 with locals := s2.locals.upd 12 (u32 q.color.idx) }
    have ec : ExS Gen.prog s2 (.call (some 12) 1 [(.var 11)]) .normal s3 :=
      call_pure rfl rfl rfl rfl hpcol (EvArgs.cons (EvE.var l11') EvArgs.nil)
    have hci : q.color.idx < 2 := by cases q.color <;> decide
    have hcc : c.idx < 2 := by cases c <;> decide
    have hceq : EvE Gen.prog s3 (.bin .eq (some ⟨32, false⟩) (.cast ⟨32, false⟩ (.var 12)) (.cast ⟨32, false⟩ (.var 2)))
        (boolVal (decide (q.color = c))) := by
      apply EvE_of_eval (n := 4)
      have h12 : s3.locals 12 = some (u32 q.color.idx) := by simp [s3, Locals.upd]
      have h2 : s3.locals 2 = some (.int IntTy.u32 c.idx) := by
        simp [s3, s2, s1, Locals.upd]; exact hI.l2
      have : (q.color.idx = c.idx) ↔ (q.color = c) := by cases q.color <;> cases c <;> decide
      simp [evalExpr, h12, h2, evalCast, evalBin, isPtr, evalBinInt, binInt, intOf, u32, IntTy.u32, IntTy.modulus,
        Res.bind, Nat.mod_eq_of_lt (show q.color.idx < 4294967296 by omega),
        Nat.mod_eq_of_lt (show c.idx < 4294967296 by omega), this]
    have hs3 : ∀ x, x ≠ 10 → x ≠ 11 → x ≠ 12 → s3.locals x = s.locals x := fun x a b d => by
      simp [s3, Locals.upd, d]; exact hs2 x a b
    have l8_3 : s3.locals 8 = some (.int IntTy.u8 (ownByte own)) := by
      rw [hs3 8 (by decide) (by decide) (by decide)]; exact hI.l8
    have hown := ownByte_lt own
    have hne255 : EvE Gen.prog s3 (.bin .ne (some ⟨32, true⟩) (.cast ⟨32, true⟩ (.var 8)) (.const (.int ⟨32, true⟩ 255)))
        (boolVal (decide (ownByte own ≠ 255))) := by
      apply EvE_of_eval (n := 4)
      simp [evalExpr, l8_3, evalCast, evalBin, isPtr, evalBinInt, binInt, intOf, IntTy.u8, IntTy.modulus, IntTy.toInt,
        Res.bind, Nat.mod_eq_of_lt (show ownByte own < 4294967296 by omega),
        show ¬ (2147483648 ≤ ownByte own) by omega]
      have e : ((ownByte own : Int) = 255) = (ownByte own = 255) := propext (by omega)
      simp only [e]
    have hpre2 : ∀ {rest o s'}, ExS Gen.prog s2 rest o s' →
        ExS Gen.prog s (.seq kc0 (.seq kc1 (.seq kc2 rest))) o s' := fun h =>
      hpre (ExS.seq (ExS.ite (bc := false) hz (by simp [truthy_boolVal, hb0]) ExS.skip) h)
    by_cases hcol : q.color = c
    · cases own with
      | some o =>
        have ho : ownByte (some o) ≠ 255 := by have := o.isLt; simp [ownByte]; omega
        refine ⟨.brk, s3, hite (hpre2 (ExS.seq_brk (ExS.seq ec (ExS.ite (bc := true) hceq (by simp [truthy_boolVal, hcol])
          (ExS.seq_brk (ExS.ite (bc := true) hne255 (by simp [truthy_boolVal, ho]) ExS.brk)))))),
          Or.inr ⟨rfl, ?_, fun _ _ => rfl, rfl, fun i hi => hs3 i (by omega) (by omega) (by omega)⟩⟩
        rw [hdrop]; simp only [kres, hq, hcol, if_true, applyK, Bool.false_eq_true, ite_false]; exact hI.mS
      | none =>
        have ho : ¬ (ownByte none ≠ 255) := by simp [ownByte]
        let s4 : State := { s3 with locals := s3.locals.upd 8 (.int IntTy.u8 sq.val) }
        have es : ExS Gen.prog s3 (.set 8 (.var 10)) .normal s4 :=
          ExS.set (EvE.var (by simp [s3, s2, s1, Locals.upd]))
        refine ⟨.cont, s4, hite (hpre2 (ExS.seq_cont (ExS.seq ec (ExS.ite (bc := true) hceq
          (by simp [truthy_boolVal, hcol]) (ExS.seq (ExS.ite (bc := false) hne255 (by simp [truthy_boolVal, ownByte])
            ExS.skip) (ExS.seq es ExS.cont)))))),
          Or.inl ⟨rfl, rfl, some sq, hI2 s4 (some sq) rfl rfl (fun x a b d e _ _ => ?_) (by simp [s4, Locals.upd, ownByte]), ?_⟩⟩
        · simp [s4, Locals.upd, a]; exact hs3 x b d e
        · rw [hdrop]; simp only [kres, hq, hcol, if_true]
    · -- an enemy piece: test the mask, then record check or pin
      let s5a : State := { s3 with locals := s3.locals.upd 14 (u32 q.type.code) }
      have e5a : ExS Gen.prog s3 (.call (some 14) 2 [(.var 11)]) .normal s5a :=
        callS rfl pureS_type rfl (run_type q) (EvArgs.cons (EvE.var (by simp [s3, Locals.upd]; exact l11')) EvArgs.nil)
      have l3_5 : s5a.locals 3 = some (.ptr Sb 0) := by
        simp [s5a, s3, s2, s1, Locals.upd]; exact hI.l3
      have l5_5 : s5a.locals 5 = some (.int IntTy.u32 a.idx) := by
        simp [s5a, s3, s2, s1, Locals.upd]; exact hI.l5
      have l7_5 : s5a.locals 7 = some (.int IntTy.u32 r) := by
        simp [s5a, s3, s2, s1, Locals.upd]; exact hI.l7
      have hcode : q.type.code ≤ 14 := by cases q.type <;> decide
      let mk := rayMask a (rdir r)
      have hmk : mk < 65536 := rayMask_lt a r hr
      have hatt := evAttacks (s := s5a) (mk := mk) (code := q.type.code) hmk hcode
        (evMaskAddrK (s := s5a) l3_5 hI.mS hI.Sl hI.S0 hr l5_5 l7_5 hI.g5) (readMask a t s5a r hr hI.g5)
        (by simp [s5a, Locals.upd]; rfl)
      let A := decide (mk &&& 2 ^ q.type.code ≠ 0)
      let s5 : State := { s5a with locals := s5a.locals.upd 13 (.int IntTy.u8 (if mk &&& 2 ^ q.type.code ≠ 0 then 1 else 0)) }
      have e5 : ExS Gen.prog s3 kc4 .normal s5 := ExS.seq e5a (ExS.set hatt)
      have l8_5 : s5.locals 8 = some (.int IntTy.u8 (ownByte own)) := by
        simp [s5, s5a, Locals.upd]; exact l8_3
      have l13 : s5.locals 13 = some (.int IntTy.u8 (if mk &&& 2 ^ q.type.code ≠ 0 then 1 else 0)) := by
        simp [s5, Locals.upd]
      have hhs5 : ∀ x, x ≠ 10 → x ≠ 11 → x ≠ 12 → x ≠ 13 → x ≠ 14 → s5.locals x = s.locals x := fun x a b d e f => by
        simp [s5, s5a, Locals.upd, e, f]; exact hs3 x a b d
      have heq255 : EvE Gen.prog s5 (.bin .eq (some ⟨32, true⟩) (.cast ⟨32, true⟩ (.var 8)) (.const (.int ⟨32, true⟩ 255)))
          (boolVal (decide (ownByte own = 255))) := by
        apply EvE_of_eval (n := 4)
        simp [evalExpr, l8_5, evalCast, evalBin, isPtr, evalBinInt, binInt, intOf, IntTy.u8, IntTy.modulus, IntTy.toInt,
          Res.bind, Nat.mod_eq_of_lt (show ownByte own < 4294967296 by omega),
          show ¬ (2147483648 ≤ ownByte own) by omega]
        have e : ((ownByte own : Int) = 255) = (ownByte own = 255) := propext (by omega)
        simp only [e]
      have htv : truthy (.int IntTy.u8 (if mk &&& 2 ^ q.type.code ≠ 0 then 1 else 0)) = .ok A := by
        by_cases h : mk &&& 2 ^ q.type.code = 0 <;> simp [truthy, A, h]
      have true8 : EvE Gen.prog s5 (.cast ⟨8, false⟩ (.bin .ne (some ⟨32, true⟩) (.const (.int ⟨32, true⟩ 1))
          (.const (.int ⟨32, true⟩ 0)))) (.int IntTy.u8 1) := EvE_of_eval (n := 3) (by rfl)
      have l3s5 : s5.locals 3 = some (.ptr Sb 0) := by simp [s5, Locals.upd]; exact l3_5
      have hmS5 : s5.mem Sb = some S := hI.mS
      have hpost : ∀ {rest o s'}, ExS Gen.prog s5 rest o s' →
          ExS Gen.prog s (.seq kc0 (.seq kc1 (.seq kc2 (.seq kc3 (.seq kc4 rest))))) o s' := fun h =>
        hpre2 (ExS.seq (ExS.seq ec (ExS.ite (bc := false) hceq (by simp [truthy_boolVal, hcol]) ExS.skip))
          (ExS.seq e5 h))
      have hk0 : kres p c mk ((ray t (rdir r)).drop k) own = kres p c mk (sq :: (ray t (rdir r)).drop (k + 1)) own := by
        rw [hdrop]
      have hS2 : 2 < S.length := by rw [hI.Sl]; decide
      cases own with
      | none =>
        have hres : kres p c mk ((ray t (rdir r)).drop k) none = (A, none) := by
          rw [hk0]; simp only [kres, hq, hcol, if_false]; rfl
        by_cases hA : A = true
        · have st := store_int_field (s := s5) (o := 0) (b := Sb) (j := 3) (t := ⟨8, false⟩) (i := 2) (v := 1)
            (blk := S) l3s5 hmS5 (by rw [hI.Sl]; decide) true8 (by simp [s5, s5a, s3, s2, s1]; exact hI.ro)
            (encodeLE_length _ _)
          refine ⟨.brk, _, hite (hpost (ExS.seq (ExS.ite (bc := true) heq255 (by simp [truthy_boolVal, ownByte])
            (ExS.ite (bc := true) (EvE.var l13) (by rw [htv, hA]) st)) ExS.brk)),
            Or.inr ⟨rfl, ?_, fun x hx => Mem.write_ne hx, rfl, fun i hi => hhs5 i (by omega) (by omega) (by omega)
              (by omega) (by omega)⟩⟩
          show (s5.mem.write Sb (0 + 2) (encodeLE 1 1)) Sb = _
          rw [Nat.zero_add, write1_set hmS5 hS2, hres, hA]; rfl
        · have hAf : A = false := by simpa using hA
          refine ⟨.brk, s5, hite (hpost (ExS.seq (ExS.ite (bc := true) heq255 (by simp [truthy_boolVal, ownByte])
            (ExS.ite (bc := false) (EvE.var l13) (by rw [htv, hAf]) ExS.skip)) ExS.brk)),
            Or.inr ⟨rfl, ?_, fun _ _ => rfl, rfl, fun i hi => hhs5 i (by omega) (by omega) (by omega)
              (by omega) (by omega)⟩⟩
          rw [hres, hAf]; exact hmS5
      | some o =>
        have ho81 := o.isLt
        have hres : kres p c mk ((ray t (rdir r)).drop k) (some o) = (false, if A then some o else none) := by
          rw [hk0]; simp only [kres, hq, hcol, if_false]; rfl
        have ho255 : ¬ (ownByte (some o) = 255) := by simp [ownByte]; omega
        by_cases hA : A = true
        · have hptr : EvE Gen.prog s5 (.index (.field (.var 3) 3) (.var 8) 1) (.ptr Sb (0 + 3 + o.val * 1)) :=
            EvE.index (pb := .ptr Sb (0 + 3)) (EvE.field (EvE.var l3s5) (by simp [ptrAddN, hmS5, hI.Sl]))
              (EvE.var l8_5) (by simp [ptrAddN, hmS5, hI.Sl, IntTy.u8, ownByte]; omega)
          have st := ExS.store (p := Gen.prog) (s := s5) (ty := .int ⟨8, false⟩) hptr true8
            (by simp [s5, s5a, s3, s2, s1]; exact hI.ro)
            (by simp only [store, ite_true, show IntTy.u8 = (⟨8, false⟩ : IntTy) from rfl, IntTy.bytes]
                exact writeBytes_ok hmS5 (by simp [encodeLE_length, hI.Sl]; omega))
          refine ⟨.brk, _, hite (hpost (ExS.seq (ExS.ite (bc := false) heq255 (by simp [truthy_boolVal, ho255])
            (ExS.ite (bc := true) (EvE.var l13) (by rw [htv, hA]) st)) ExS.brk)),
            Or.inr ⟨rfl, ?_, fun x hx => Mem.write_ne hx, rfl, fun i hi => hhs5 i (by omega) (by omega) (by omega)
              (by omega) (by omega)⟩⟩
          show (s5.mem.write Sb (0 + 3 + o.val * 1) (encodeLE 1 1)) Sb = _
          rw [write1_set hmS5 (by rw [hI.Sl]; omega), hres, hA]
          simp [applyK, IntTy.bytes]
        · have hAf : A = false := by simpa using hA
          refine ⟨.brk, s5, hite (hpost (ExS.seq (ExS.ite (bc := false) heq255 (by simp [truthy_boolVal, ho255])
            (ExS.ite (bc := false) (EvE.var l13) (by rw [htv, hAf]) ExS.skip)) ExS.brk)),
            Or.inr ⟨rfl, ?_, fun _ _ => rfl, rfl, fun i hi => hhs5 i (by omega) (by omega) (by omega)
              (by omega) (by omega)⟩⟩
          rw [hres, hAf]; exact hmS5

theorem kStep9_spec {s : State} {k : Nat} (hk : k < 81) (h9 : s.locals 9 = some (.int IntTy.u8 k)) :
    ExS Gen.prog s kStep9 .normal { s with locals := s.locals.upd 9 (.int IntTy.u8 (k + 1)) } := by
  have := sqStep_spec (s := { s with locals := s.locals.upd 6 (.int IntTy.u8 k) }) hk (by simp [Locals.upd, u8])
  have c1 : evalCast ⟨32, true⟩ (u8 k) = .ok (i32 (k : Int)) := by
    rw [i32_nat k (by omega)]
    simp [evalCast, u8, IntTy.u8, IntTy.toInt, IntTy.i32, IntTy.wrap, IntTy.modulus]; omega
  have c2 : evalCast ⟨8, false⟩ (i32 ((k : Int) + 1)) = .ok (u8 (k + 1)) := by
    rw [show ((k : Int) + 1) = ((k + 1 : Nat) : Int) by omega, i32_nat (k + 1) (by omega)]
    simp [evalCast, u8, IntTy.u8, IntTy.toInt, IntTy.i32, IntTy.wrap, IntTy.modulus,
      show ¬ (2147483648 ≤ k + 1) by omega]; omega
  exact ExS.set (EvE.cast (EvE.bin (EvE.cast (EvE.var (v := u8 k) h9) c1) (EvE.const (.int ⟨32, true⟩ 1))
    (add_i32 (k : Int) 1 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega))) c2)

theorem kres_nil (p : Position) (c : Color) (mk : Nat) (own : Option Square) : kres p c mk [] own = (false, none) := by
  cases own <;> rfl

/-- The scan of one ray. -/
theorem kray_loop {p : Position} {c a : Color} {t : Square} {r Sb : Nat} {S : List UInt8} {v0 : Val} (hr : r < 8)
    (ha : a = c.opp) :
    ∀ (d k : Nat) (s : State) (own : Option Square), k + d = (ray t (rdir r)).length →
      KInv p c a t r Sb S v0 s k own →
      ∃ s', ExS Gen.prog s (.loop kBody0 kStep9) .normal s' ∧
        s'.mem Sb = some (applyK S (kres p c (rayMask a (rdir r)) ((ray t (rdir r)).drop k) own)) ∧
        (∀ x, x ≠ Sb → s'.mem x = s.mem x) ∧ s'.ro = s.ro ∧
        ∀ i, i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 5 ∨ i = 7 → s'.locals i = s.locals i := by
  have hl8 := ray_length_le t (rdir r)
  intro d
  induction d with
  | zero =>
    intro k s own hd hI
    have hk : k = (ray t (rdir r)).length := by omega
    subst hk
    have hlen := evRayLen (s := s) hI.l3 hI.mS hI.Sl hI.S0 hr hI.l7 hI.g4
    have hcond : EvE Gen.prog s kCond (boolVal false) := by
      refine EvE.bin (EvE.cast (EvE.var hI.l9) rfl) (EvE.cast hlen rfl) ?_
      simp [evalBin, isPtr, evalBinInt, binInt, intOf, evalCast, IntTy.modulus, IntTy.toInt, Res.bind,
        Nat.mod_eq_of_lt (show (ray t (rdir r)).length < 4294967296 by omega),
        show ¬ (2147483648 ≤ (ray t (rdir r)).length) by omega]
    refine ⟨s, ExS.loop_brk (ExS.ite (bc := false) hcond rfl ExS.brk), ?_, fun _ _ => rfl, rfl, fun _ _ => rfl⟩
    rw [List.drop_eq_nil_of_le (by omega), kres_nil]; exact hI.mS
  | succ d ih =>
    intro k s own hd hI
    have hk : k < (ray t (rdir r)).length := by omega
    obtain ⟨o, s1, e1, h⟩ := kbody_spec hr ha hk hI
    rcases h with ⟨ho, hm1, own', hI1, hres⟩ | ⟨ho, hS1, hm1, hro1, hl1⟩
    · subst ho
      let s2 : State := { s1 with locals := s1.locals.upd 9 (.int IntTy.u8 (k + 1)) }
      have es := kStep9_spec (s := s1) (by omega) hI1.l9
      have hI2 : KInv p c a t r Sb S v0 s2 (k + 1) own' :=
        ⟨by simp [s2, Locals.upd]; exact hI1.l0, by simp [s2, Locals.upd]; exact hI1.l1, by simp [s2, Locals.upd]; exact hI1.l2,
         by simp [s2, Locals.upd]; exact hI1.l3, by simp [s2, Locals.upd]; exact hI1.l5,
         by simp [s2, Locals.upd]; exact hI1.l7, by simp [s2, Locals.upd]; exact hI1.l8,
         by simp [s2, Locals.upd], hI1.mp, hI1.mS, hI1.g3, hI1.g4, hI1.g5, hI1.Sl, hI1.S0, hI1.ro, hI1.Sbp, hI1.Sbg⟩
      obtain ⟨s', e', hS', hm', hro', hl'⟩ := ih (k + 1) s2 own' (by omega) hI2
      refine ⟨s', ExS.loop_next e1 (Or.inr rfl) es e', by rw [hres]; exact hS', fun x hx => by
        rw [hm' x hx]; show s1.mem x = _; rw [hm1], by rw [hro']; show s1.ro = _; rw [hI1.ro, hI.ro], fun i hi => ?_⟩
      rw [hl' i hi]; show s1.locals.upd 9 _ i = _
      rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;> simp [Locals.upd] <;>
        first | (rw [hI1.l0, hI.l0]) | (rw [hI1.l1, hI.l1]) | (rw [hI1.l2, hI.l2]) | (rw [hI1.l3, hI.l3]) | (rw [hI1.l5, hI.l5]) | (rw [hI1.l7, hI.l7])
    · subst ho
      exact ⟨s1, ExS.loop_brk e1, hS1, hm1, hro1, hl1⟩

theorem applyK_len (S : List UInt8) (x : Bool × Option Square) : (applyK S x).length = S.length := by
  obtain ⟨chk, pin⟩ := x; cases pin <;> cases chk <;> simp [applyK]

theorem applyK_0 (S : List UInt8) (x : Bool × Option Square) : (applyK S x).getD 0 0 = S.getD 0 0 := by
  obtain ⟨chk, pin⟩ := x
  cases pin <;> cases chk <;> simp [applyK, List.getD_eq_getElem?_getD, List.getElem?_set]

/-- The record after the first `r` rays. -/
def ksAll (p : Position) (c a : Color) (t : Square) (S : List UInt8) : Nat → List UInt8
  | 0 => S
  | r + 1 => applyK (ksAll p c a t S r) (kres p c (rayMask a (rdir r)) (ray t (rdir r)) none)

theorem kAll_len (p : Position) (c a : Color) (t : Square) (S : List UInt8) :
    ∀ r, (ksAll p c a t S r).length = S.length := by
  intro r; induction r with
  | zero => rfl
  | succ r ih => simp only [ksAll]; rw [applyK_len, ih]

theorem kAll_0 (p : Position) (c a : Color) (t : Square) (S : List UInt8) :
    ∀ r, (ksAll p c a t S r).getD 0 0 = S.getD 0 0 := by
  intro r; induction r with
  | zero => rfl
  | succ r ih => simp only [ksAll]; rw [applyK_0, ih]

def kOuter1 : Stmt := (.ite (.bin .lt (some ⟨32, false⟩) (.var 7) (.cast ⟨32, false⟩ (.const (.int ⟨32, true⟩ 8)))) (.seq (.set 8 (.cast ⟨8, false⟩ (.const (.int ⟨32, true⟩ 255)))) (.seq (.set 9 (.cast ⟨8, false⟩ (.const (.int ⟨32, true⟩ 0)))) Gen.king_safety_prepare_loop0)) .brk)
def kStep7 : Stmt := (.set 7 (.cast ⟨32, false⟩ (.bin .add (some ⟨32, false⟩) (.cast ⟨32, false⟩ (.var 7)) (.const (.int ⟨32, false⟩ 1)))))

theorem ks_loop1_eq : Gen.king_safety_prepare_loop1 = .loop kOuter1 kStep7 := rfl

theorem kouter_loop {p : Position} {c a : Color} {t : Square} {Sb : Nat} {S : List UInt8} {v0 : Val} (ha : a = c.opp) :
    ∀ (d r : Nat) (s : State), r + d = 8 →
      s.locals 0 = some v0 → s.locals 1 = some posPtr → s.locals 2 = some (.int IntTy.u32 c.idx) → s.locals 3 = some (.ptr Sb 0) →
      s.locals 5 = some (.int IntTy.u32 a.idx) → s.locals 7 = some (.int IntTy.u32 r) →
      s.mem posBlock = some (encode p) → s.mem Sb = some (ksAll p c a t S r) →
      s.mem 8194 = some Gen.global_attack_rays → s.mem 8195 = some Gen.global_attack_ray_length →
      s.mem 8196 = some Gen.global_attack_ray_masks → S.length = 84 → S.getD 0 0 = t.val.toUInt8 → s.ro = false →
      Sb ≠ posBlock → (Sb ≠ 8194 ∧ Sb ≠ 8195 ∧ Sb ≠ 8196) →
      ∃ s', ExS Gen.prog s (.loop kOuter1 kStep7) .normal s' ∧ s'.mem Sb = some (ksAll p c a t S 8) ∧
        (∀ x, x ≠ Sb → s'.mem x = s.mem x) ∧ s'.ro = s.ro ∧ s'.locals 0 = some v0 ∧
        s'.locals 3 = some (.ptr Sb 0) := by
  intro d
  induction d with
  | zero =>
    intro r s hd h0 _ _ h3 _ h7 _ hS _ _ _ _ _ _ _ _
    have : r = 8 := by omega
    subst this
    refine ⟨s, ExS.loop_brk (ExS.ite (bc := false) (vc := boolVal false) (EvE_of_eval (n := 4) ?_) rfl ExS.brk), hS,
      fun _ _ => rfl, rfl, h0, h3⟩
    simp [evalExpr, h7, evalCast, evalBin, isPtr, evalBinInt, binInt, intOf, IntTy.u32, IntTy.toInt, IntTy.wrap,
      IntTy.modulus, Res.bind]
  | succ d ih =>
    intro r s hd h0 h1 h2 h3 h5 h7 hp hS g3 g4 g5 hSl hS0 hro hSbp hSbg
    have hr : r < 8 := by omega
    have hcond : EvE Gen.prog s (.bin .lt (some ⟨32, false⟩) (.var 7) (.cast ⟨32, false⟩ (.const (.int ⟨32, true⟩ 8))))
        (boolVal true) := by
      apply EvE_of_eval (n := 4)
      simp [evalExpr, h7, evalCast, evalBin, isPtr, evalBinInt, binInt, intOf, IntTy.u32, IntTy.toInt, IntTy.wrap,
        IntTy.modulus, Res.bind, hr]
    let s0 : State := { s with locals := s.locals.upd 8 (.int IntTy.u8 255) }
    let s1 : State := { s0 with locals := s0.locals.upd 9 (.int IntTy.u8 0) }
    have e8 : ExS Gen.prog s (.set 8 (.cast ⟨8, false⟩ (.const (.int ⟨32, true⟩ 255)))) .normal s0 :=
      ExS.set (EvE_of_eval (n := 3) (by rfl))
    have e9 : ExS Gen.prog s0 (.set 9 (.cast ⟨8, false⟩ (.const (.int ⟨32, true⟩ 0)))) .normal s1 :=
      ExS.set (EvE_of_eval (n := 3) (by rfl))
    have hs1 : ∀ x, x ≠ 8 → x ≠ 9 → s1.locals x = s.locals x := fun x a b => by simp [s1, s0, Locals.upd, a, b]
    have hI : KInv p c a t r Sb (ksAll p c a t S r) v0 s1 0 none :=
      ⟨by rw [hs1 0 (by decide) (by decide)]; exact h0, by rw [hs1 1 (by decide) (by decide)]; exact h1, by rw [hs1 2 (by decide) (by decide)]; exact h2,
       by rw [hs1 3 (by decide) (by decide)]; exact h3, by rw [hs1 5 (by decide) (by decide)]; exact h5,
       by rw [hs1 7 (by decide) (by decide)]; exact h7, by simp [s1, s0, Locals.upd, ownByte],
       by simp [s1, Locals.upd], hp, hS, g3, g4, g5, by rw [kAll_len]; exact hSl, by rw [kAll_0]; exact hS0, hro,
       hSbp, hSbg⟩
    obtain ⟨s2, e2, hS2, hm2, hro2, hl2⟩ := kray_loop hr ha (ray t (rdir r)).length 0 s1 none (by omega) hI
    have hdec : ∀ x, x ∈ [0, 1, 2, 3, 5] → s2.locals x = s.locals x := by
      intro x hx; simp at hx
      rw [hl2 x (by omega)]; exact hs1 x (by omega) (by omega)
    have l7 : s2.locals 7 = some (.int IntTy.u32 r) := by rw [hl2 7 (by omega), hs1 7 (by decide) (by decide)]; exact h7
    let s3 : State := { s2 with locals := s2.locals.upd 7 (.int IntTy.u32 (r + 1)) }
    have es : ExS Gen.prog s2 kStep7 .normal s3 := by
      apply ExS.set; apply EvE_of_eval (n := 4)
      simp [evalExpr, l7, evalCast, evalBin, isPtr, evalBinInt, binInt, intOf, IntTy.u32, IntTy.modulus, Res.bind,
        IntTy.toInt, Nat.mod_eq_of_lt (show r < 4294967296 by omega),
        Nat.mod_eq_of_lt (show r + 1 < 4294967296 by omega)]
    have hl3 : ∀ x, x ∈ [0, 1, 2, 3, 5] → s3.locals x = s.locals x := fun x hx => by
      have : x ≠ 7 := by simp at hx; omega
      simp [s3, Locals.upd, this]; exact hdec x hx
    have hm2p : s2.mem posBlock = s.mem posBlock := hm2 _ (Ne.symm hSbp)
    obtain ⟨s', e', hS', hm', hro', hl0', hl3'⟩ := ih (r + 1) s3 (by omega) (by rw [hl3 0 (by simp)]; exact h0)
      (by rw [hl3 1 (by simp)]; exact h1) (by rw [hl3 2 (by simp)]; exact h2) (by rw [hl3 3 (by simp)]; exact h3)
      (by rw [hl3 5 (by simp)]; exact h5) (by simp [s3, Locals.upd])
      (by show s2.mem posBlock = _; rw [hm2p]; exact hp)
      (by show s2.mem Sb = _; rw [hS2]; rfl)
      (by show s2.mem 8194 = _; rw [hm2 _ (Ne.symm hSbg.1)]; exact g3)
      (by show s2.mem 8195 = _; rw [hm2 _ (Ne.symm hSbg.2.1)]; exact g4)
      (by show s2.mem 8196 = _; rw [hm2 _ (Ne.symm hSbg.2.2)]; exact g5) hSl hS0
      (by show s2.ro = _; rw [hro2]; exact hro) hSbp hSbg
    refine ⟨s', ExS.loop_next (ExS.ite (bc := true) hcond rfl (ExS.seq e8 (ExS.seq e9 (by rw [ks_loop0_eq]; exact e2))))
      (Or.inl rfl) es e', hS', fun x hx => by rw [hm' x hx]; show s2.mem x = _; rw [hm2 x hx], ?_, hl0', hl3'⟩
    rw [hro']; show s2.ro = _; rw [hro2]

theorem ExS_memset {s : State} {d c n : Expr} {bd od : Nat} {t1 t2 : IntTy} {x k : Nat} {m' : Mem}
    (hd : EvE Gen.prog s d (.ptr bd od)) (hc : EvE Gen.prog s c (.int t1 x)) (hn : EvE Gen.prog s n (.int t2 k))
    (hro : s.ro = false) (hw : writeBytes s.mem bd od (List.replicate k (x % 256).toUInt8) = .ok m') :
    ExS Gen.prog s (.memset d c n) .normal { s with mem := m' } := by
  obtain ⟨K1, h1⟩ := hd
  obtain ⟨K2, h2⟩ := hc
  obtain ⟨K3, h3⟩ := hn
  refine ⟨max K1 (max K2 K3) + 1, fun n hn => ?_⟩
  obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
  simp only [execStmt, h1 n' (by omega), h2 n' (by omega), h3 n' (by omega), Res.bind_eq, Res.bind_ok, hro,
    MiniC.guard, Bool.not_false, ite_true, hw]
  rfl

/-- The 84-byte `KingSafety` record the C returns. -/
def ksInit (p : Position) (c : Color) (k : Square) : List UInt8 :=
  (((List.replicate 84 (0 : UInt8)).set 0 k.val.toUInt8).set 1 1).set 2
    (if stepAttacked p k c.opp then 1 else 0)

def ksRec (p : Position) (c : Color) : List UInt8 :=
  match p.kingSquare c with
  | none => List.replicate 84 0
  | some k => ksAll p c c.opp k (ksInit p c k) 8

theorem king_safety_spec (p : Position) (c : Color) {m : Mem} {ob n : Nat} {OB : List UInt8}
    (hm : m posBlock = some (encode p)) (hob : m ob = some OB) (hOB : OB.length = 84)
    (g1 : m 8192 = some Gen.global_step_attack_probes) (g2 : m 8193 = some Gen.global_step_attack_probe_count)
    (g3 : m 8194 = some Gen.global_attack_rays) (g4 : m 8195 = some Gen.global_attack_ray_length)
    (g5 : m 8196 = some Gen.global_attack_ray_masks)
    (hf : Fresh m n) (h64 : n + 1 < 2 ^ 64) (hob0 : ob ≠ 0) (hobp : ob ≠ posBlock) :
    ∃ s', ExS Gen.prog ⟨frameLocals Gen.king_safety_prepare.params [.ptr ob 0, posPtr, .int IntTy.u32 c.idx], m, false⟩
        Gen.king_safety_prepare.body (.ret none) s' ∧ s'.mem ob = some (ksRec p c) ∧
      (∀ x, x ≠ 0 → x ≠ n → x ≠ ob → s'.mem x = m x) ∧ s'.mem 0 = some (encodeLE 8 (n + 1)) := by
  have hn0 := hf.2.1
  have hnob : n ≠ ob := fun e => by rw [← e, hf.2.2 n (Nat.le_refl _)] at hob; cases hob
  have hnp : n ≠ posBlock := fun e => by rw [← e, hf.2.2 n (Nat.le_refl _)] at hm; cases hm
  have hng : ∀ g, m g ≠ none → n ≠ g := fun g hg e => by rw [← e, hf.2.2 n (Nat.le_refl _)] at hg; exact hg rfl
  let s0 : State := ⟨frameLocals Gen.king_safety_prepare.params [.ptr ob 0, posPtr, .int IntTy.u32 c.idx], m, false⟩
  let Z : List UInt8 := List.replicate 84 0
  let m1 := (m.upd 0 (encodeLE 8 (n + 1))).upd n Z
  let s1 : State := { s0 with mem := m1, locals := s0.locals.upd 3 (.ptr n 0) }
  have ea : ExS Gen.prog s0 (.alloc 3 84) .normal s1 := exec_alloc (s := s0) (hf.allocAt (by omega)) 3 84
  have hm1 : ∀ x, x ≠ 0 → x ≠ n → m1 x = m x := fun x a b => by simp only [m1]; rw [Mem.upd_ne b, Mem.upd_ne a]
  have hm1n : m1 n = some Z := Mem.upd_eq
  have l3 : s1.locals 3 = some (.ptr n 0) := by simp [s1, Locals.upd]
  have ems : ExS Gen.prog s1 (.memset (.var 3) (.const (.int ⟨32, true⟩ 0)) (.const (.int ⟨64, false⟩ 84))) .normal
      { s1 with mem := m1.write n 0 Z } :=
    ExS_memset (EvE.var l3) (EvE.const _) (EvE.const _) rfl (writeBytes_ok hm1n (by simp [Z]))
  let m2 := m1.write n 0 Z
  have hm2n : m2 n = some Z := by show (m1.write n 0 Z) n = _; rw [write_some hm1n]; simp [wrb, Z]
  have hm2 : ∀ x, x ≠ 0 → x ≠ n → m2 x = m x := fun x a b => by
    show (m1.write n 0 Z) x = _; rw [Mem.write_ne b, hm1 x a b]
  have hm20 : m2 0 = some (encodeLE 8 (n + 1)) := by
    show (m1.write n 0 Z) 0 = _; rw [Mem.write_ne hn0.symm]; simp only [m1]; rw [Mem.upd_ne hn0.symm, Mem.upd_eq]
  let s2 : State := { s1 with mem := m2 }
  have hm2p : m2 posBlock = some (encode p) := by rw [hm2 _ (by decide) (Ne.symm hnp)]; exact hm
  have hfk := find_king_refines p c m2 n Z hm2p hm2n (by simp [Z])
  have hargs : EvArgs Gen.prog s2 [(.var 1), (.var 2), (.field (.var 3) 0)] [posPtr, .int IntTy.u32 c.idx, .ptr n 0] :=
    EvArgs.cons (EvE.var (v := posPtr) (by simp [s2, s1, s0, Locals.upd]; rfl))
      (EvArgs.cons (EvE.var (v := .int IntTy.u32 c.idx) (by simp [s2, s1, s0, Locals.upd]; rfl))
      (EvArgs.cons (EvE.field (pb := .ptr n 0) (EvE.var (by simp [s2, l3])) (by simp [ptrAddN, s2, hm2n, Z]))
        EvArgs.nil))
  have hob2 : m2 ob = some OB := by rw [hm2 _ hob0 (Ne.symm hnob)]; exact hob
  have hmcpy : ∀ (st : State) (B : List UInt8), st.locals 0 = some (.ptr ob 0) → st.locals 3 = some (.ptr n 0) →
      st.mem n = some B → B.length = 84 → st.mem ob = some OB → st.ro = false →
      ExS Gen.prog st (.memcpy (.var 0) (.var 3) (.const (.int ⟨64, false⟩ 84))) .normal
        { st with mem := st.mem.write ob 0 B } := by
    intro st B h0 h3 hB hBl hO hro
    refine ExS.memcpy (bd := ob) (od := 0) (bs := n) (os := 0) (t := ⟨64, false⟩) (k := 84) (bytes := B)
      (EvE.var h0) (EvE.var h3) (EvE.const _) hro (by simp [Ne.symm hnob]) ?_ (writeBytes_ok hO (by simp [hBl, hOB]))
    simp [readBytes, hB, hBl, List.take_of_length_le]
  have hwob : ∀ (mm : Mem) (B : List UInt8), mm ob = some OB → B.length = 84 → (mm.write ob 0 B) ob = some B := by
    intro mm B h hl; rw [write_some h]; simp [wrb, hl, hOB]
  cases hk : p.kingSquare c with
  | none =>
    rw [hk] at hfk
    obtain ⟨sf, ef, hsf⟩ := hfk
    let s3 : State := { s2 with mem := sf.mem, locals := s2.locals.upd 4 false8 }
    have ec : ExS Gen.prog s2 (.call (some 4) 19 [(.var 1), (.var 2), (.field (.var 3) 0)]) .normal s3 :=
      ExS.call_dst hargs rfl rfl ef
    have hlnot : EvE Gen.prog s3 (.un .lnot ⟨32, true⟩ (.var 4)) (boolVal true) := by
      apply EvE_of_eval (n := 3); simp [evalExpr, s3, Locals.upd, false8, evalUn, truthy, boolVal, Res.bind, pure]
    have hcp := hmcpy s3 Z (by simp [s3, s2, s1, s0, Locals.upd]; rfl) (by simp [s3, s2, Locals.upd]; exact l3)
      (by show sf.mem n = _; rw [hsf]; exact hm2n) (by simp [Z]) (by show sf.mem ob = _; rw [hsf]; exact hob2) rfl
    refine ⟨_, ExS.seq ea (ExS.seq ems (ExS.seq_ret (ExS.seq ec (ExS.ite (bc := true) hlnot (by simp [truthy_boolVal])
      (ExS.seq hcp ExS.ret_none))))), ?_, ?_, ?_⟩
    · show (s3.mem.write ob 0 Z) ob = _; simp only [ksRec, hk]
      exact hwob _ Z (by show sf.mem ob = _; rw [hsf]; exact hob2) (by simp [Z])
    · intro x a b d; show (s3.mem.write ob 0 Z) x = _
      rw [Mem.write_ne d]; show sf.mem x = _; rw [hsf, hm2 x a b]
    · show (s3.mem.write ob 0 Z) 0 = _
      rw [Mem.write_ne hob0.symm]; show sf.mem 0 = _; rw [hsf]; exact hm20
  | some k =>
    rw [hk] at hfk
    obtain ⟨sf, ef, hsf⟩ := hfk
    have hk81 := k.isLt
    have hmf : sf.mem = m2.write n 0 (encodeLE 1 k.val) := by
      have hw := writeBytes_ok (o := 0) (bs := encodeLE 1 k.val) hm2n (by simp [Z, encodeLE_length])
      have h1 : store m2 (.int IntTy.u8) (.ptr n 0) (.int IntTy.u8 k.val) = .ok (m2.write n 0 (encodeLE 1 k.val)) := by
        simp only [store, if_true]; exact hw
      rw [h1] at hsf
      exact (Res.ok.inj hsf).symm
    let s3 : State := { s2 with mem := sf.mem, locals := s2.locals.upd 4 true8 }
    have ec : ExS Gen.prog s2 (.call (some 4) 19 [(.var 1), (.var 2), (.field (.var 3) 0)]) .normal s3 :=
      ExS.call_dst hargs rfl rfl ef
    have hlnot : EvE Gen.prog s3 (.un .lnot ⟨32, true⟩ (.var 4)) (boolVal false) := by
      apply EvE_of_eval (n := 3); simp [evalExpr, s3, Locals.upd, true8, evalUn, truthy, boolVal, Res.bind, pure]
    let S1 := Z.set 0 k.val.toUInt8
    have hm3n : s3.mem n = some S1 := by show sf.mem n = _; rw [hmf, write1_set hm2n (by simp [Z])]
    have hm3o : ∀ x, x ≠ n → s3.mem x = m2 x := fun x hx => by show sf.mem x = _; rw [hmf, Mem.write_ne hx]
    have l3' : s3.locals 3 = some (.ptr n 0) := by simp [s3, s2, Locals.upd]; exact l3
    -- valid = true
    have st1 := store_int_field (s := s3) (o := 0) (b := n) (j := 3) (t := ⟨8, false⟩) (i := 1) (v := 1)
      (e := .cast ⟨8, false⟩ (.bin .ne (some ⟨32, true⟩) (.const (.int ⟨32, true⟩ 1)) (.const (.int ⟨32, true⟩ 0))))
      (blk := S1) l3' hm3n (by simp [S1, Z, IntTy.bytes]) (EvE_of_eval (n := 3) (by rfl)) rfl (encodeLE_length _ _)
    let S2 := S1.set 1 1
    let m4 := s3.mem.write n (0 + 1) (encodeLE 1 1)
    have hm4n : m4 n = some S2 := by show (s3.mem.write n (0 + 1) _) n = _; rw [write1_set hm3n (by simp [S1, Z])]; rfl
    let s4 : State := { s3 with mem := m4 }
    -- attacker = mover ^ 1
    let s5 : State := { s4 with locals := s4.locals.upd 5 (.int IntTy.u32 c.opp.idx) }
    have e5 : ExS Gen.prog s4 (.set 5 (.cast ⟨32, false⟩ (.bin .bxor (some ⟨32, false⟩) (.cast ⟨32, false⟩ (.var 2))
        (.cast ⟨32, false⟩ (.const (.int ⟨32, true⟩ 1)))))) .normal s5 := by
      apply ExS.set; apply EvE_of_eval (n := 5)
      have h2 : s4.locals 2 = some (.int IntTy.u32 c.idx) := by simp [s4, s3, s2, s1, s0, Locals.upd]; rfl
      cases c <;> simp [evalExpr, h2, evalCast, evalBin, isPtr, evalBinInt, binInt, intOf, IntTy.u32,
        IntTy.modulus, IntTy.toInt, IntTy.wrap, Res.bind, Color.idx, Color.opp] <;> rfl
    have hm4o : ∀ x, x ≠ n → m4 x = m2 x := fun x hx => by
      show (s3.mem.write n _ _) x = _; rw [Mem.write_ne hx, hm3o x hx]
    have hmg : ∀ g, g ≠ 0 → m g ≠ none → m4 g = m g := fun g h0 hg => by
      rw [hm4o g (Ne.symm (hng g hg)), hm2 g h0 (Ne.symm (hng g hg))]
    have hm4p : m4 posBlock = some (encode p) := by rw [hmg _ (by decide) (by rw [hm]; simp)]; exact hm
    have l3_5 : s5.locals 3 = some (.ptr n 0) := by simp [s5, s4, Locals.upd]; exact l3'
    have hS20 : S2.getD 0 0 = k.val.toUInt8 := by simp [S2, S1, Z, List.getD_eq_getElem?_getD, List.getElem?_set]
    have hk8 := ev_blk_u8 (s := s5) (j := 3) (b := n) (B := S2) l3_5 hm4n (k := 0) (by simp [S2, S1, Z])
    rw [hS20, toNat_toUInt8_lt _ (by omega)] at hk8
    obtain ⟨ss, es, hss⟩ := step_square_attacked_refines p k c.opp m4 hm4p
      (by rw [hmg _ (by decide) (by rw [g1]; simp)]; exact g1) (by rw [hmg _ (by decide) (by rw [g2]; simp)]; exact g2)
    let v := if stepAttacked p k c.opp then true8 else false8
    let s6 : State := { s5 with mem := ss.mem, locals := s5.locals.upd 6 v }
    have ec6 : ExS Gen.prog s5 (.call (some 6) 16 [(.var 1), (.load (.int ⟨8, false⟩) (.field (.var 3) 0)), (.var 5)])
        .normal s6 :=
      ExS.call_dst (EvArgs.cons (EvE.var (v := posPtr) (by simp [s5, s4, s3, s2, s1, s0, Locals.upd]; rfl))
        (EvArgs.cons hk8 (EvArgs.cons (EvE.var (by simp [s5, Locals.upd])) EvArgs.nil))) rfl rfl es
    have hm6 : s6.mem = m4 := hss
    let bv := if stepAttacked p k c.opp then 1 else 0
    have st2 := store_int_field (s := s6) (o := 0) (b := n) (j := 3) (t := ⟨8, false⟩) (i := 2) (v := bv)
      (e := .var 6) (blk := S2) (by simp [s6, s5, s4, Locals.upd]; exact l3') (by rw [hm6]; exact hm4n)
      (by simp [S2, S1, Z, IntTy.bytes]) (EvE.var (by simp [s6, Locals.upd, v, bv]; split <;> rfl)) rfl
      (encodeLE_length _ _)
    let S3 := S2.set 2 bv.toUInt8
    let m7 := s6.mem.write n (0 + 2) (encodeLE 1 bv)
    have hm7n : m7 n = some S3 := by
      show (s6.mem.write n (0 + 2) _) n = _; rw [hm6, write1_set hm4n (by simp [S2, S1, Z])]
    have hS3 : S3 = ksInit p c k := by
      simp only [S3, S2, S1, Z, ksInit, bv]; congr 1; split <;> rfl
    let s7 : State := { s6 with mem := m7 }
    let s8 : State := { s7 with locals := s7.locals.upd 7 (.int IntTy.u32 0) }
    have e8 : ExS Gen.prog s7 (.set 7 (.cast ⟨32, false⟩ (.const (.int ⟨32, true⟩ 0)))) .normal s8 :=
      ExS.set (EvE_of_eval (n := 3) (by simp [evalExpr, evalCast, IntTy.u32, IntTy.toInt, IntTy.wrap, IntTy.modulus,
        Res.bind]))
    have hm7o : ∀ x, x ≠ n → m7 x = m4 x := fun x hx => by
      show (s6.mem.write n _ _) x = _; rw [Mem.write_ne hx, hm6]
    have hmg7 : ∀ g, g ≠ 0 → m g ≠ none → m7 g = m g := fun g h0 hg => by
      rw [hm7o g (Ne.symm (hng g hg)), hmg g h0 hg]
    have hS3l : (ksInit p c k).length = 84 := by simp [ksInit]
    have hS30 : (ksInit p c k).getD 0 0 = k.val.toUInt8 := by
      simp [ksInit, List.getD_eq_getElem?_getD, List.getElem?_set]
    obtain ⟨s9, e9, hS9, hm9, hro9, l09, l39⟩ := kouter_loop (p := p) (c := c) (a := c.opp) (t := k) (Sb := n)
      (S := ksInit p c k) (v0 := .ptr ob 0)
      rfl 8 0 s8 rfl (by simp [s8, s7, s6, s5, s4, s3, s2, s1, s0, Locals.upd]; rfl)
      (by simp [s8, s7, s6, s5, s4, s3, s2, s1, s0, Locals.upd]; rfl)
      (by simp [s8, s7, s6, s5, s4, s3, s2, s1, s0, Locals.upd]; rfl)
      (by simp [s8, s7, s6, s5, s4, Locals.upd]; exact l3')
      (by simp [s8, s7, s6, s5, Locals.upd]) (by simp [s8, Locals.upd])
      (by show m7 posBlock = _; rw [hmg7 _ (by decide) (by rw [hm]; simp)]; exact hm)
      (by show m7 n = _; rw [hm7n, hS3]; rfl)
      (by show m7 8194 = _; rw [hmg7 _ (by decide) (by rw [g3]; simp)]; exact g3)
      (by show m7 8195 = _; rw [hmg7 _ (by decide) (by rw [g4]; simp)]; exact g4)
      (by show m7 8196 = _; rw [hmg7 _ (by decide) (by rw [g5]; simp)]; exact g5)
      hS3l hS30 rfl hnp ⟨hng _ (by rw [g3]; simp), hng _ (by rw [g4]; simp), hng _ (by rw [g5]; simp)⟩
    have hob9 : s9.mem ob = some OB := by
      rw [hm9 ob (Ne.symm hnob)]; show m7 ob = _; rw [hmg7 _ hob0 (by rw [hob]; simp)]; exact hob
    have hcp := hmcpy s9 (ksAll p c c.opp k (ksInit p c k) 8) l09 l39 hS9
      (by rw [kAll_len]; exact hS3l) hob9 (by rw [hro9])
    let R := ksAll p c c.opp k (ksInit p c k) 8
    refine ⟨_, ExS.seq ea (ExS.seq ems (ExS.seq (ExS.seq ec (ExS.ite (bc := false) hlnot (by simp [truthy_boolVal])
      ExS.skip)) (ExS.seq st1 (ExS.seq e5 (ExS.seq (ExS.seq ec6 st2) (ExS.seq (ExS.seq e8 (by rw [ks_loop1_eq]; exact e9))
        (ExS.seq hcp ExS.ret_none))))))), ?_, ?_, ?_⟩
    · show (s9.mem.write ob 0 R) ob = _; simp only [ksRec, hk]
      exact hwob _ R hob9 (by rw [kAll_len]; exact hS3l)
    · intro x a b d; show (s9.mem.write ob 0 R) x = _
      rw [Mem.write_ne d, hm9 x b]; show m7 x = _
      rw [hm7o x b, hm4o x b, hm2 x a b]
    · show (s9.mem.write ob 0 R) 0 = _
      rw [Mem.write_ne hob0.symm, hm9 0 hn0.symm]; show m7 0 = _
      rw [hm7o 0 hn0.symm, hm4o 0 hn0.symm]; exact hm20

end Shogi.C.Proofs
