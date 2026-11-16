/-
  `shogi_is_in_check` refines `Position.inCheck` (composition of the
  `find_king` and `square_attacked` refinements, with the local `king`
  allocated in memory).
-/
import Shogi.C.Proofs.SquareAttack

namespace Shogi.C.Proofs
open MiniC Shogi Shogi.C Shogi.Tables Shogi.Position

theorem Mem.upd_ne {m : Mem} {b x : Nat} {blk : Block} (h : x ≠ b) : (m.upd b blk) x = m x := by
  simp [Mem.upd, h]

theorem Mem.upd_eq {m : Mem} {b : Nat} {blk : Block} : (m.upd b blk) b = some blk := by
  simp [Mem.upd]

/-- The memory blocks the attack code reads. -/
structure TablesIn (m : Mem) : Prop where
  g1 : m 8192 = some Gen.global_step_attack_probes
  g2 : m 8193 = some Gen.global_step_attack_probe_count
  g3 : m 8194 = some Gen.global_attack_rays
  g4 : m 8195 = some Gen.global_attack_ray_length
  g5 : m 8196 = some Gen.global_attack_ray_masks

theorem TablesIn.upd {m : Mem} (h : TablesIn m) {b : Nat} (blk : Block) (hb : m b = none) :
    TablesIn (m.upd b blk) := by
  have ne : ∀ x, m x ≠ none → x ≠ b := fun x hx e => hx (e ▸ hb)
  exact ⟨by rw [Mem.upd_ne (ne _ (by rw [h.g1]; simp))]; exact h.g1,
    by rw [Mem.upd_ne (ne _ (by rw [h.g2]; simp))]; exact h.g2,
    by rw [Mem.upd_ne (ne _ (by rw [h.g3]; simp))]; exact h.g3,
    by rw [Mem.upd_ne (ne _ (by rw [h.g4]; simp))]; exact h.g4,
    by rw [Mem.upd_ne (ne _ (by rw [h.g5]; simp))]; exact h.g5⟩

theorem TablesIn.upd_not {m : Mem} (h : TablesIn m) {b : Nat} (blk : Block)
    (hb : b ≠ 8192 ∧ b ≠ 8193 ∧ b ≠ 8194 ∧ b ≠ 8195 ∧ b ≠ 8196) : TablesIn (m.upd b blk) := by
  obtain ⟨a1, a2, a3, a4, a5⟩ := hb
  exact ⟨by rw [Mem.upd_ne (Ne.symm a1)]; exact h.g1, by rw [Mem.upd_ne (Ne.symm a2)]; exact h.g2,
    by rw [Mem.upd_ne (Ne.symm a3)]; exact h.g3, by rw [Mem.upd_ne (Ne.symm a4)]; exact h.g4,
    by rw [Mem.upd_ne (Ne.symm a5)]; exact h.g5⟩

theorem TablesIn.fresh {m : Mem} (h : TablesIn m) {b : Nat} (hb : m b = none) :
    b ≠ 8192 ∧ b ≠ 8193 ∧ b ≠ 8194 ∧ b ≠ 8195 ∧ b ≠ 8196 := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> intro e <;> subst e
  · rw [h.g1] at hb; cases hb
  · rw [h.g2] at hb; cases hb
  · rw [h.g3] at hb; cases hb
  · rw [h.g4] at hb; cases hb
  · rw [h.g5] at hb; cases hb

theorem TablesIn.upd0 {m : Mem} (h : TablesIn m) (blk : Block) : TablesIn (m.upd 0 blk) :=
  ⟨by rw [Mem.upd_ne (by decide)]; exact h.g1, by rw [Mem.upd_ne (by decide)]; exact h.g2,
   by rw [Mem.upd_ne (by decide)]; exact h.g3, by rw [Mem.upd_ne (by decide)]; exact h.g4,
   by rw [Mem.upd_ne (by decide)]; exact h.g5⟩

/-- The allocator (block 0) is about to hand out the unused block `n`. -/
def AllocAt (m : Mem) (n : Nat) : Prop :=
  m 0 = some (encodeLE 8 n) ∧ n ≠ 0 ∧ n < 2 ^ 64 ∧ m n = none

theorem decode_encode8 (n : Nat) (h : n < 2 ^ 64) : decodeLE (encodeLE 8 n) = n := by
  simp [encodeLE, decodeLE]; omega

theorem exec_alloc {s : State} {n : Nat} (ha : AllocAt s.mem n) (i size : Nat) :
    ExS Gen.prog s (.alloc i size) .normal
      { s with mem := (s.mem.upd 0 (encodeLE 8 (n + 1))).upd n (List.replicate size 0),
               locals := s.locals.upd i (.ptr n 0) } := by
  obtain ⟨h0, hn0, hn64, hfree⟩ := ha
  apply ExS_of_execStmt Gen.prog (n := 2)
  have hr : readBytes s.mem 0 0 8 = .ok (encodeLE 8 n) := by
    simp [readBytes, h0, encodeLE]
  have hw : writeBytes s.mem 0 0 (encodeLE 8 (n + 1)) = .ok (s.mem.upd 0 (encodeLE 8 (n + 1))) := by
    simp [writeBytes, h0, encodeLE]
  simp only [execStmt, hr, Res.bind_eq, Res.bind_ok, decode_encode8 n hn64, hfree, Option.isNone_none,
    MiniC.guard, hn0, decide_false, Bool.not_false, bne_iff_ne, ne_eq, Bool.true_and]
  simp [hw, Res.bind, decide_eq_true hn0]

/-- **`shogi_is_in_check` refines `Position.inCheck`.** For every position
    and colour: no UB, terminates, and returns 1 iff the colour's king is
    attacked by the opponent (0 when it has no king). -/
theorem shogi_is_in_check_refines (p : Position) (c : Color) (m : Mem) (n : Nat)
    (hm : m posBlock = some (encode p)) (ht : TablesIn m) (ha : AllocAt m n) :
    ∃ s', ExS Gen.prog ⟨frameLocals Gen.shogi_is_in_check.params [posPtr, .int IntTy.u32 c.idx], m, false⟩
      Gen.shogi_is_in_check.body (.ret (some (if p.inCheck c then true8 else false8))) s' ∧
      (∀ x, x ≠ 0 → x ≠ n → s'.mem x = m x) ∧ s'.mem 0 = some (encodeLE 8 (n + 1)) ∧ (s'.mem n).isSome := by
  have hci : c.idx < 2 := by cases c <;> decide
  have ⟨_, hn0, _, hfree⟩ := ha
  have hnpos : n ≠ posBlock := fun e => by rw [e, hm] at hfree; cases hfree
  let L0 := frameLocals Gen.shogi_is_in_check.params [posPtr, .int IntTy.u32 c.idx]
  let s0 : State := ⟨L0, m, false⟩
  -- argument guard
  have hguard : ExS Gen.prog s0 (.ite (.lor (.bin .eq none (.var 0) (.const .null)) (.land (.bin .ne
      (some ⟨32, false⟩) (.cast ⟨32, false⟩ (.var 1)) (.cast ⟨32, false⟩ (.const (.int ⟨32, true⟩ 0))))
      (.bin .ne (some ⟨32, false⟩) (.cast ⟨32, false⟩ (.var 1)) (.cast ⟨32, false⟩
      (.const (.int ⟨32, true⟩ 1)))))) (.ret (some (.cast ⟨8, false⟩ (.bin .ne (some ⟨32, true⟩)
      (.const (.int ⟨32, true⟩ 0)) (.const (.int ⟨32, true⟩ 0)))))) .skip) .normal s0 := by
    refine ExS.ite (vc := boolVal false) (bc := false) (EvE_of_eval (n := 6) ?_) rfl ExS.skip
    cases c <;> rfl
  -- the local `king`
  let m1 := (m.upd 0 (encodeLE 8 (n + 1))).upd n (List.replicate 1 0)
  let s1 : State := { s0 with mem := m1, locals := s0.locals.upd 2 (.ptr n 0) }
  have halloc : ExS Gen.prog s0 (.alloc 2 1) .normal s1 := exec_alloc ⟨ha.1, hn0, ha.2.2.1, hfree⟩ 2 1
  have hm1 : m1 posBlock = some (encode p) := by
    simp only [m1]; rw [Mem.upd_ne (Ne.symm hnpos), Mem.upd_ne (by decide)]; exact hm
  have ht1 : TablesIn m1 := (ht.upd0 _).upd _ (by rw [Mem.upd_ne hn0]; exact hfree)
  have hob : m1 n = some (List.replicate 1 0) := Mem.upd_eq
  have hfk := find_king_refines p c m1 n _ hm1 hob (by simp)
  unfold Gen.shogi_is_in_check
  simp only
  unfold Position.inCheck
  revert hfk
  cases hks : p.kingSquare c with
  | some sq =>
    intro ⟨sF, hsF, hst⟩
    have hsq := sq.isLt
    have hmF : sF.mem = m1.upd n (encodeLE 1 sq.val ++ (List.replicate 1 (0 : UInt8)).drop 1) := by
      rw [store_u8_ok hob (by simp) sq.val] at hst
      simp only [Res.ok.injEq] at hst; exact hst.symm
    let s2 : State := { s1 with mem := sF.mem, locals := s1.locals.upd 3 true8 }
    have hcall1 : ExS Gen.prog s1 (.call (some 3) 19 [(.var 0), (.var 1), (.var 2)]) .normal s2 :=
      ExS.call_dst (EvArgs_of_eval (n := 4) rfl) rfl rfl hsF
    have hmF' : sF.mem posBlock = some (encode p) := by rw [hmF, Mem.upd_ne (Ne.symm hnpos)]; exact hm1
    have htF : TablesIn sF.mem := by rw [hmF]; exact ht1.upd_not _ (ht.fresh hfree)
    have hnF : sF.mem n = some [sq.val.toUInt8] := by
      rw [hmF, Mem.upd_eq]; simp [encodeLE, Nat.mod_eq_of_lt (show sq.val < 256 by omega)]
    obtain ⟨sA, hsA, hsAm⟩ := square_attacked_refines p sq c.opp sF.mem hmF' htF.g1 htF.g2 htF.g3 htF.g4 htF.g5
    show ∃ s', ExS Gen.prog _ _ (.ret (some (if p.attacked sq c.opp then true8 else false8))) s' ∧ _
    generalize p.attacked sq c.opp = att at hsA ⊢
    let v4 := if att then true8 else false8
    let s3 : State := { s2 with mem := sA.mem, locals := s2.locals.upd 4 v4 }
    have hargs : evalArgs Gen.prog 10 s2 [(.var 0), (.load (.int ⟨8, false⟩) (.var 2)),
        (.cast ⟨32, false⟩ (.bin .bxor (some ⟨32, false⟩) (.cast ⟨32, false⟩ (.var 1))
          (.cast ⟨32, false⟩ (.const (.int ⟨32, true⟩ 1)))))] =
        .ok [posPtr, .int IntTy.u8 sq.val, .int IntTy.u32 c.opp.idx] := by
      have hr : readBytes sF.mem n 0 1 = .ok [sq.val.toUInt8] := by simp [readBytes, hnF]
      simp only [evalArgs, evalExpr, s2, s1, s0, L0, Locals.upd, Res.bind_eq, Res.bind_ok, load,
        Ty.size, IntTy.bytes, hr]
      cases c <;> simp [frameLocals, Gen.shogi_is_in_check, decodeLE, evalCast, evalBin, isPtr, evalBinInt,
        binInt, intOf, IntTy.u8, IntTy.u32, IntTy.modulus, IntTy.wrap, IntTy.toInt, Res.bind, Color.opp,
        Color.idx, Nat.mod_eq_of_lt (show sq.val < 256 by omega), hr] <;> rfl
    have hcall2 : ExS Gen.prog s2 (.call (some 4) 17 [(.var 0), (.load (.int ⟨8, false⟩) (.var 2)),
        (.cast ⟨32, false⟩ (.bin .bxor (some ⟨32, false⟩) (.cast ⟨32, false⟩ (.var 1))
          (.cast ⟨32, false⟩ (.const (.int ⟨32, true⟩ 1)))))]) .normal s3 :=
      ExS.call_dst (EvArgs_of_eval hargs) rfl rfl hsA
    let s4 : State := { s3 with locals := s3.locals.upd 5 (boolVal att) }
    have hset5 : ExS Gen.prog s3 (.set 5 (.land (.const (.int ⟨32, true⟩ 1)) (.cast ⟨32, true⟩ (.var 4))))
        .normal s4 := by
      apply ExS.set
      cases att
      · exact EvE.land_true (EvE.const _) rfl (EvE_of_eval (n := 2) (by simp [evalExpr, s3, Locals.upd, v4]; rfl)) rfl
      · exact EvE.land_true (EvE.const _) rfl (EvE_of_eval (n := 2) (by simp [evalExpr, s3, Locals.upd, v4]; rfl)) rfl
    have hite : ExS Gen.prog s2 (.ite (.cast ⟨32, true⟩ (.var 3)) (.seq (.call (some 4) 17 [(.var 0),
        (.load (.int ⟨8, false⟩) (.var 2)), (.cast ⟨32, false⟩ (.bin .bxor (some ⟨32, false⟩)
        (.cast ⟨32, false⟩ (.var 1)) (.cast ⟨32, false⟩ (.const (.int ⟨32, true⟩ 1)))))])
        (.set 5 (.land (.const (.int ⟨32, true⟩ 1)) (.cast ⟨32, true⟩ (.var 4)))))
        (.set 5 (.const (.int ⟨32, true⟩ 0)))) .normal s4 :=
      ExS.ite (vc := .int IntTy.i32 1) (bc := true) (EvE_of_eval (n := 2) (by
        simp [evalExpr, s2, Locals.upd, true8, evalCast, IntTy.wrap, IntTy.modulus]; rfl)) rfl
        (ExS.seq hcall2 hset5)
    have hm4 : s4.mem = m1.upd n (encodeLE 1 sq.val ++ (List.replicate 1 (0 : UInt8)).drop 1) := by
      show sA.mem = _; rw [hsAm, hmF]
    refine ⟨s4, ExS.seq hguard (ExS.seq halloc (ExS.seq hcall1 (ExS.seq hite (ExS.ret ?_)))), ?_, ?_, ?_⟩
    · apply EvE_of_eval (n := 4)
      cases att <;> rfl
    · intro x a b; rw [hm4, Mem.upd_ne b]; simp only [m1]; rw [Mem.upd_ne b, Mem.upd_ne a]
    · rw [hm4, Mem.upd_ne hn0.symm]; simp only [m1]; rw [Mem.upd_ne hn0.symm, Mem.upd_eq]
    · rw [hm4, Mem.upd_eq]; rfl
  | none =>
    intro ⟨sF, hsF, hmem⟩
    let s2 : State := { s1 with mem := sF.mem, locals := s1.locals.upd 3 false8 }
    have hcall1 : ExS Gen.prog s1 (.call (some 3) 19 [(.var 0), (.var 1), (.var 2)]) .normal s2 :=
      ExS.call_dst (EvArgs_of_eval (n := 4) rfl) rfl rfl hsF
    let s4 : State := { s2 with locals := s2.locals.upd 5 (.int IntTy.i32 0) }
    have hite : ExS Gen.prog s2 (.ite (.cast ⟨32, true⟩ (.var 3)) (.seq (.call (some 4) 17 [(.var 0),
        (.load (.int ⟨8, false⟩) (.var 2)), (.cast ⟨32, false⟩ (.bin .bxor (some ⟨32, false⟩)
        (.cast ⟨32, false⟩ (.var 1)) (.cast ⟨32, false⟩ (.const (.int ⟨32, true⟩ 1)))))])
        (.set 5 (.land (.const (.int ⟨32, true⟩ 1)) (.cast ⟨32, true⟩ (.var 4)))))
        (.set 5 (.const (.int ⟨32, true⟩ 0)))) .normal s4 :=
      ExS.ite (vc := .int IntTy.i32 0) (bc := false) (EvE_of_eval (n := 2) (by
        simp [evalExpr, s2, Locals.upd, false8, evalCast, IntTy.wrap, IntTy.modulus]; rfl)) rfl
        (ExS.set (EvE.const _))
    have hm4 : s4.mem = m1 := hmem
    refine ⟨s4, ExS.seq hguard (ExS.seq halloc (ExS.seq hcall1 (ExS.seq hite
      (ExS.ret (EvE_of_eval (n := 4) rfl))))), ?_, ?_, ?_⟩
    · intro x a b; rw [hm4]; simp only [m1]; rw [Mem.upd_ne b, Mem.upd_ne a]
    · rw [hm4]; simp only [m1]; rw [Mem.upd_ne hn0.symm, Mem.upd_eq]
    · rw [hm4, hob]; rfl

end Shogi.C.Proofs
