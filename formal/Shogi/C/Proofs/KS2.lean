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
structure KInv (p : Position) (c a : Color) (t : Square) (r : Nat) (Sb : Nat) (S : List UInt8)
    (s : State) (k : Nat) (own : Option Square) : Prop where
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

theorem kbody_spec {p : Position} {c a : Color} {t : Square} {r Sb : Nat} {S : List UInt8} (hr : r < 8)
    (ha : a = c.opp) {s : State} {k : Nat} {own : Option Square} (hk : k < (ray t (rdir r)).length)
    (hI : KInv p c a t r Sb S s k own) :
    ∃ o s1, ExS Gen.prog s kBody0 o s1 ∧
      ((o = .cont ∧ s1.mem = s.mem ∧ ∃ own', KInv p c a t r Sb S s1 k own' ∧
          kres p c (rayMask a (rdir r)) ((ray t (rdir r)).drop k) own =
          kres p c (rayMask a (rdir r)) ((ray t (rdir r)).drop (k + 1)) own') ∨
       (o = .brk ∧ s1.mem Sb = some (applyK S (kres p c (rayMask a (rdir r)) ((ray t (rdir r)).drop k) own)) ∧
          (∀ x, x ≠ Sb → s1.mem x = s.mem x) ∧ s1.ro = s.ro ∧
          ∀ i, i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 5 ∨ i = 7 → s1.locals i = s.locals i)) := by
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
      st.locals 8 = some (.int IntTy.u8 (ownByte o)) → KInv p c a t r Sb S st k o := by
    intro st o hm hro hl h8
    exact ⟨by rw [hl 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hI.l1,
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
theorem kray_loop {p : Position} {c a : Color} {t : Square} {r Sb : Nat} {S : List UInt8} (hr : r < 8)
    (ha : a = c.opp) :
    ∀ (d k : Nat) (s : State) (own : Option Square), k + d = (ray t (rdir r)).length →
      KInv p c a t r Sb S s k own →
      ∃ s', ExS Gen.prog s (.loop kBody0 kStep9) .normal s' ∧
        s'.mem Sb = some (applyK S (kres p c (rayMask a (rdir r)) ((ray t (rdir r)).drop k) own)) ∧
        (∀ x, x ≠ Sb → s'.mem x = s.mem x) ∧ s'.ro = s.ro ∧
        ∀ i, i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 5 ∨ i = 7 → s'.locals i = s.locals i := by
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
      have hI2 : KInv p c a t r Sb S s2 (k + 1) own' :=
        ⟨by simp [s2, Locals.upd]; exact hI1.l1, by simp [s2, Locals.upd]; exact hI1.l2,
         by simp [s2, Locals.upd]; exact hI1.l3, by simp [s2, Locals.upd]; exact hI1.l5,
         by simp [s2, Locals.upd]; exact hI1.l7, by simp [s2, Locals.upd]; exact hI1.l8,
         by simp [s2, Locals.upd], hI1.mp, hI1.mS, hI1.g3, hI1.g4, hI1.g5, hI1.Sl, hI1.S0, hI1.ro, hI1.Sbp, hI1.Sbg⟩
      obtain ⟨s', e', hS', hm', hro', hl'⟩ := ih (k + 1) s2 own' (by omega) hI2
      refine ⟨s', ExS.loop_next e1 (Or.inr rfl) es e', by rw [hres]; exact hS', fun x hx => by
        rw [hm' x hx]; show s1.mem x = _; rw [hm1], by rw [hro']; show s1.ro = _; rw [hI1.ro, hI.ro], fun i hi => ?_⟩
      rw [hl' i hi]; show s1.locals.upd 9 _ i = _
      rcases hi with rfl | rfl | rfl | rfl | rfl <;> simp [Locals.upd] <;>
        first | (rw [hI1.l1, hI.l1]) | (rw [hI1.l2, hI.l2]) | (rw [hI1.l3, hI.l3]) | (rw [hI1.l5, hI.l5]) | (rw [hI1.l7, hI.l7])
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

theorem kouter_loop {p : Position} {c a : Color} {t : Square} {Sb : Nat} {S : List UInt8} (ha : a = c.opp) :
    ∀ (d r : Nat) (s : State), r + d = 8 →
      s.locals 1 = some posPtr → s.locals 2 = some (.int IntTy.u32 c.idx) → s.locals 3 = some (.ptr Sb 0) →
      s.locals 5 = some (.int IntTy.u32 a.idx) → s.locals 7 = some (.int IntTy.u32 r) →
      s.mem posBlock = some (encode p) → s.mem Sb = some (ksAll p c a t S r) →
      s.mem 8194 = some Gen.global_attack_rays → s.mem 8195 = some Gen.global_attack_ray_length →
      s.mem 8196 = some Gen.global_attack_ray_masks → S.length = 84 → S.getD 0 0 = t.val.toUInt8 → s.ro = false →
      Sb ≠ posBlock → (Sb ≠ 8194 ∧ Sb ≠ 8195 ∧ Sb ≠ 8196) →
      ∃ s', ExS Gen.prog s (.loop kOuter1 kStep7) .normal s' ∧ s'.mem Sb = some (ksAll p c a t S 8) ∧
        (∀ x, x ≠ Sb → s'.mem x = s.mem x) ∧ s'.ro = s.ro := by
  intro d
  induction d with
  | zero =>
    intro r s hd _ _ _ _ h7 _ hS _ _ _ _ _ _ _ _
    have : r = 8 := by omega
    subst this
    refine ⟨s, ExS.loop_brk (ExS.ite (bc := false) (vc := boolVal false) (EvE_of_eval (n := 4) ?_) rfl ExS.brk), hS,
      fun _ _ => rfl, rfl⟩
    simp [evalExpr, h7, evalCast, evalBin, isPtr, evalBinInt, binInt, intOf, IntTy.u32, IntTy.toInt, IntTy.wrap,
      IntTy.modulus, Res.bind]
  | succ d ih =>
    intro r s hd h1 h2 h3 h5 h7 hp hS g3 g4 g5 hSl hS0 hro hSbp hSbg
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
    have hI : KInv p c a t r Sb (ksAll p c a t S r) s1 0 none :=
      ⟨by rw [hs1 1 (by decide) (by decide)]; exact h1, by rw [hs1 2 (by decide) (by decide)]; exact h2,
       by rw [hs1 3 (by decide) (by decide)]; exact h3, by rw [hs1 5 (by decide) (by decide)]; exact h5,
       by rw [hs1 7 (by decide) (by decide)]; exact h7, by simp [s1, s0, Locals.upd, ownByte],
       by simp [s1, Locals.upd], hp, hS, g3, g4, g5, by rw [kAll_len]; exact hSl, by rw [kAll_0]; exact hS0, hro,
       hSbp, hSbg⟩
    obtain ⟨s2, e2, hS2, hm2, hro2, hl2⟩ := kray_loop hr ha (ray t (rdir r)).length 0 s1 none (by omega) hI
    have hdec : ∀ x, x ∈ [1, 2, 3, 5] → s2.locals x = s.locals x := by
      intro x hx; simp at hx
      rw [hl2 x (by omega)]; exact hs1 x (by omega) (by omega)
    have l7 : s2.locals 7 = some (.int IntTy.u32 r) := by rw [hl2 7 (by omega), hs1 7 (by decide) (by decide)]; exact h7
    let s3 : State := { s2 with locals := s2.locals.upd 7 (.int IntTy.u32 (r + 1)) }
    have es : ExS Gen.prog s2 kStep7 .normal s3 := by
      apply ExS.set; apply EvE_of_eval (n := 4)
      simp [evalExpr, l7, evalCast, evalBin, isPtr, evalBinInt, binInt, intOf, IntTy.u32, IntTy.modulus, Res.bind,
        IntTy.toInt, Nat.mod_eq_of_lt (show r < 4294967296 by omega),
        Nat.mod_eq_of_lt (show r + 1 < 4294967296 by omega)]
    have hl3 : ∀ x, x ∈ [1, 2, 3, 5] → s3.locals x = s.locals x := fun x hx => by
      have : x ≠ 7 := by simp at hx; omega
      simp [s3, Locals.upd, this]; exact hdec x hx
    have hm2p : s2.mem posBlock = s.mem posBlock := hm2 _ (Ne.symm hSbp)
    obtain ⟨s', e', hS', hm', hro'⟩ := ih (r + 1) s3 (by omega)
      (by rw [hl3 1 (by simp)]; exact h1) (by rw [hl3 2 (by simp)]; exact h2) (by rw [hl3 3 (by simp)]; exact h3)
      (by rw [hl3 5 (by simp)]; exact h5) (by simp [s3, Locals.upd])
      (by show s2.mem posBlock = _; rw [hm2p]; exact hp)
      (by show s2.mem Sb = _; rw [hS2]; rfl)
      (by show s2.mem 8194 = _; rw [hm2 _ (Ne.symm hSbg.1)]; exact g3)
      (by show s2.mem 8195 = _; rw [hm2 _ (Ne.symm hSbg.2.1)]; exact g4)
      (by show s2.mem 8196 = _; rw [hm2 _ (Ne.symm hSbg.2.2)]; exact g5) hSl hS0
      (by show s2.ro = _; rw [hro2]; exact hro) hSbp hSbg
    refine ⟨s', ExS.loop_next (ExS.ite (bc := true) hcond rfl (ExS.seq e8 (ExS.seq e9 (by rw [ks_loop0_eq]; exact e2))))
      (Or.inl rfl) es e', hS', fun x hx => by rw [hm' x hx]; show s2.mem x = _; rw [hm2 x hx], ?_⟩
    rw [hro']; show s2.ro = _; rw [hro2]

end Shogi.C.Proofs
