/-
  T8: the `needs_probe` / `pawn_drop` computation of the legality loop
  computes `needsProbeC`.
-/
import Shogi.C.Proofs.FastGlue

namespace Shogi.C.Proofs
open MiniC Shogi Shogi.C Shogi.Tables

section bools
variable {s : State} {e1 e2 : Expr} {v1 v2 : Val} {b1 b2 : Bool}

theorem evB_or' (h1 : EvE Gen.prog s e1 v1) (t1 : truthy v1 = .ok b1) (h2 : EvE Gen.prog s e2 v2)
    (t2 : truthy v2 = .ok b2) : EvE Gen.prog s (.lor e1 e2) (boolVal (b1 || b2)) := by
  cases b1
  · simpa using EvE.lor_false h1 t1 h2 t2
  · simpa using EvE.lor_true (b := e2) h1 t1

theorem evB_and' (h1 : EvE Gen.prog s e1 v1) (t1 : truthy v1 = .ok b1) (h2 : EvE Gen.prog s e2 v2)
    (t2 : truthy v2 = .ok b2) : EvE Gen.prog s (.land e1 e2) (boolVal (b1 && b2)) := by
  cases b1
  · simpa using EvE.land_false (b := e2) h1 t1
  · simpa using EvE.land_true h1 t1 h2 t2

theorem evB_not (h1 : EvE Gen.prog s e1 v1) (t1 : truthy v1 = .ok b1) :
    EvE Gen.prog s (.un .lnot ⟨32, true⟩ e1) (boolVal (!b1)) :=
  EvE.un h1 (by simp [evalUn, t1, Res.bind, pure])

theorem truthy_u8 (x : Nat) : truthy (.int IntTy.u8 x) = .ok (x != 0) := rfl

theorem truthy_i32c (x : Nat) (hx : x < 256) :
    evalCast ⟨32, true⟩ (.int IntTy.u8 x) = .ok (.int IntTy.i32 x) := by
  simp [evalCast, IntTy.u8, IntTy.i32, IntTy.toInt, IntTy.wrap, IntTy.modulus]; omega

end bools

def npSeg : Stmt := (.seq (.ite (.lor (.lor (.un .lnot ⟨32, true⟩ (.load (.int ⟨8, false⟩) (.field (.var 8) 1))) (.cast ⟨32, true⟩ (.load (.int ⟨8, false⟩) (.field (.var 8) 2)))) (.bin .eq (some ⟨32, true⟩) (.cast ⟨32, true⟩ (.load (.int ⟨8, false⟩) (.field (.var 10) 0))) (.const (.int ⟨32, true⟩ 255)))) (.set 13 (.const (.int ⟨32, true⟩ 1))) (.seq (.call (some 12) 2 [(.load (.int ⟨8, false⟩) (.index (.field (.var 0) 0) (.load (.int ⟨8, false⟩) (.field (.var 10) 0)) 1))]) (.set 13 (.lor (.const (.int ⟨32, true⟩ 0)) (.bin .eq (some ⟨32, false⟩) (.cast ⟨32, false⟩ (.var 12)) (.cast ⟨32, false⟩ (.const (.int ⟨32, true⟩ 8)))))))) (.seq (.ite (.var 13) (.set 16 (.const (.int ⟨32, true⟩ 1))) (.seq (.ite (.cast ⟨32, true⟩ (.load (.int ⟨8, false⟩) (.index (.field (.var 8) 3) (.load (.int ⟨8, false⟩) (.field (.var 10) 0)) 1))) (.seq (.call (some 14) 20 [(.load (.int ⟨8, false⟩) (.field (.var 8) 0)), (.load (.int ⟨8, false⟩) (.field (.var 10) 0)), (.load (.int ⟨8, false⟩) (.field (.var 10) 1))]) (.set 15 (.land (.const (.int ⟨32, true⟩ 1)) (.un .lnot ⟨32, true⟩ (.var 14))))) (.set 15 (.const (.int ⟨32, true⟩ 0)))) (.set 16 (.lor (.const (.int ⟨32, true⟩ 0)) (.var 15))))) (.set 11 (.cast ⟨8, false⟩ (.bin .ne (some ⟨32, true⟩) (.var 16) (.const (.int ⟨32, true⟩ 0)))))))
def pdSeg : Stmt := (.set 17 (.cast ⟨8, false⟩ (.bin .ne (some ⟨32, true⟩) (.land (.bin .eq (some ⟨32, true⟩) (.cast ⟨32, true⟩ (.load (.int ⟨8, false⟩) (.field (.var 10) 0))) (.const (.int ⟨32, true⟩ 255))) (.bin .eq (some ⟨32, true⟩) (.cast ⟨32, true⟩ (.load (.int ⟨8, false⟩) (.field (.var 10) 4))) (.const (.int ⟨32, true⟩ 1)))) (.const (.int ⟨32, true⟩ 0)))))

theorem ksRec_len (p : Position) (c : Color) : (ksRec p c).length = 84 := by
  unfold ksRec; cases p.kingSquare c
  · simp
  · simp only; rw [kAll_len]; simp [ksInit]

theorem ksRec_pin01 (p : Position) (c : Color) (sq : Square) :
    (ksRec p c).getD (3 + sq.val) 0 = (if (match p.kingSquare c with
      | some k => pinnedSpec p c k sq | none => false) then 1 else 0) := by
  cases hk : p.kingSquare c with
  | some k => simp only; exact ksRec_pinned p c k sq hk
  | none =>
    unfold ksRec; rw [hk]; simp only [Bool.false_eq_true, if_false]
    have := sq.isLt
    simp only [List.getD_eq_getElem?_getD]; rw [List.getElem?_replicate, if_pos (by omega)]; rfl

theorem pd_spec {s : State} {p : Position} {m : Move} {n : Nat}
    (hl10 : s.locals 10 = some (.ptr n 0)) (hn : s.mem n = some (moveBytes p m)) :
    ExS Gen.prog s pdSeg .normal
      { s with locals := s.locals.upd 17 (u8 (if Position.isPawnDrop m then 1 else 0)) } := by
  have hl : (moveBytes p m).length = 5 := by cases m <;> rfl
  have h0 := ev_cmp255 hl10 hn (k := 0) (by omega) .eq (Or.inl rfl)
  have h4v := ev_blk_u8 hl10 hn (k := 4) (by omega)
  have hb4 := UInt8.toNat_lt ((moveBytes p m).getD 4 0)
  have h4 : EvE Gen.prog s (.bin .eq (some ⟨32, true⟩) (.cast ⟨32, true⟩ (.load (.int ⟨8, false⟩) (.field (.var 10) 4)))
      (.const (.int ⟨32, true⟩ 1))) (boolVal (decide (((moveBytes p m).getD 4 0).toNat = 1))) := by
    generalize hx : ((moveBytes p m).getD 4 0).toNat = x at h4v hb4 ⊢
    refine EvE.bin (EvE.cast h4v (truthy_i32c x hb4)) (EvE.const _) ?_
    simp [evalBin, isPtr, evalBinInt, binInt, intOf, IntTy.i32, IntTy.toInt, Res.bind,
      show ¬ (2147483648 ≤ x) by omega]
    have e : ((x : Int) = 1) = (x = 1) := propext (by omega)
    simp only [e]
  have hall := evB_u8 (evB_and h0 h4)
  simp only [show BinOp.eq = BinOp.eq from rfl, if_true] at hall
  have hval : (decide (((moveBytes p m).getD 0 0).toNat = 255) && decide (((moveBytes p m).getD 4 0).toNat = 1)) =
      Position.isPawnDrop m := by
    cases m with
    | drop t d => cases t <;> rfl
    | normal sq d pr =>
      have := sq.isLt
      simp [moveBytes, Position.isPawnDrop, toNat_toUInt8_lt sq.val (by omega)]
  rw [hval] at hall
  exact ExS.set hall

theorem np_spec {s : State} {p : Position} {m : Move} {n Sb : Nat} (hm : m ∈ p.pseudoMoves)
    (hl0 : s.locals 0 = some posPtr) (hl8 : s.locals 8 = some (.ptr Sb 0)) (hSb : s.mem Sb = some (ksRec p p.side))
    (hl10 : s.locals 10 = some (.ptr n 0)) (hn : s.mem n = some (moveBytes p m))
    (hpos : s.mem posBlock = some (encode p)) :
    ∃ s', ExS Gen.prog s npSeg .normal s' ∧ s'.mem = s.mem ∧
      s'.locals 11 = some (u8 (if needsProbeC (ksRec p p.side) p m then 1 else 0)) ∧
      (∀ x, x < 11 → s'.locals x = s.locals x) := by
  let R := ksRec p p.side
  have hRl : R.length = 84 := ksRec_len p p.side
  have hMl : (moveBytes p m).length = 5 := by cases m <;> rfl
  have hv1 := ev_blk_u8 hl8 hSb (k := 1) (by rw [ksRec_len]; decide)
  have hv2 := ev_blk_u8 hl8 hSb (k := 2) (by rw [ksRec_len]; decide)
  have hb2 := UInt8.toNat_lt (R.getD 2 0)
  have o1 := evB_not hv1 (truthy_u8 _)
  have o2 : EvE Gen.prog s (.cast ⟨32, true⟩ (.load (.int ⟨8, false⟩) (.field (.var 8) 2)))
      (.int IntTy.i32 (R.getD 2 0).toNat) := EvE.cast hv2 (truthy_i32c _ hb2)
  have o3 := ev_cmp255 hl10 hn (k := 0) (by omega) .eq (Or.inl rfl)
  simp only [if_true] at o3
  have c1 := evB_or' (evB_or' o1 (truthy_boolVal _) o2 rfl) (truthy_boolVal _) o3 (truthy_boolVal _)
  let C1 := (!((R.getD 1 0).toNat != 0) || (R.getD 2 0).toNat != 0) || decide (((moveBytes p m).getD 0 0).toNat = 255)
  -- tail: from `has13` decide everything after the first `ite`
  have tail1 : ∀ (t : State), t.locals 13 = some (.int ⟨32, true⟩ 1) →
      ExS Gen.prog t (.seq (.ite (.var 13) (.set 16 (.const (.int ⟨32, true⟩ 1))) (.seq (.ite (.cast ⟨32, true⟩ (.load (.int ⟨8, false⟩) (.index (.field (.var 8) 3) (.load (.int ⟨8, false⟩) (.field (.var 10) 0)) 1))) (.seq (.call (some 14) 20 [(.load (.int ⟨8, false⟩) (.field (.var 8) 0)), (.load (.int ⟨8, false⟩) (.field (.var 10) 0)), (.load (.int ⟨8, false⟩) (.field (.var 10) 1))]) (.set 15 (.land (.const (.int ⟨32, true⟩ 1)) (.un .lnot ⟨32, true⟩ (.var 14))))) (.set 15 (.const (.int ⟨32, true⟩ 0)))) (.set 16 (.lor (.const (.int ⟨32, true⟩ 0)) (.var 15))))) (.set 11 (.cast ⟨8, false⟩ (.bin .ne (some ⟨32, true⟩) (.var 16) (.const (.int ⟨32, true⟩ 0))))))
        .normal { t with locals := (t.locals.upd 16 (.int ⟨32, true⟩ 1)).upd 11 (u8 1) } := by
    intro t h13
    refine ExS.seq (ExS.ite (bc := true) (EvE.var h13) rfl (ExS.set (EvE.const _))) (ExS.set ?_)
    have := evB_u8 (s := { t with locals := t.locals.upd 16 (.int ⟨32, true⟩ 1) }) (x := true) (e1 := .var 16)
      (EvE.var (by simp [Locals.upd]; rfl))
    simpa using this
  have u8z : ∀ x : UInt8, (x.toNat != 0) = !(x == 0) := by
    intro x; cases h : (x == 0)
    · have : x ≠ 0 := by simpa using h
      have : x.toNat ≠ 0 := fun e => this (UInt8.toNat_inj.mp (by simpa using e))
      simp [this]
    · have : x = 0 := by simpa using h
      simp [this]
  by_cases hC : C1 = true
  · let t1 : State := { s with locals := s.locals.upd 13 (.int ⟨32, true⟩ 1) }
    have e1 : ExS Gen.prog s (.ite (.lor (.lor (.un .lnot ⟨32, true⟩ (.load (.int ⟨8, false⟩) (.field (.var 8) 1))) (.cast ⟨32, true⟩ (.load (.int ⟨8, false⟩) (.field (.var 8) 2)))) (.bin .eq (some ⟨32, true⟩) (.cast ⟨32, true⟩ (.load (.int ⟨8, false⟩) (.field (.var 10) 0))) (.const (.int ⟨32, true⟩ 255)))) (.set 13 (.const (.int ⟨32, true⟩ 1))) (.seq (.call (some 12) 2 [(.load (.int ⟨8, false⟩) (.index (.field (.var 0) 0) (.load (.int ⟨8, false⟩) (.field (.var 10) 0)) 1))]) (.set 13 (.lor (.const (.int ⟨32, true⟩ 0)) (.bin .eq (some ⟨32, false⟩) (.cast ⟨32, false⟩ (.var 12)) (.cast ⟨32, false⟩ (.const (.int ⟨32, true⟩ 8)))))))) .normal t1 :=
      ExS.ite (bc := true) c1 (by rw [truthy_boolVal]; exact congrArg _ hC) (ExS.set (EvE.const _))
    refine ⟨_, ExS.seq e1 (tail1 t1 (by simp [t1, Locals.upd])), rfl, ?_, fun x hx => ?_⟩
    · simp only [Locals.upd, if_true]
      congr 2
      have : needsProbeC R p m = true := by
        cases m with
        | drop t d => rfl
        | normal sq d pr =>
          have hsq := sq.isLt
          have hm0 : ((moveBytes p (.normal sq d pr)).getD 0 0).toNat = sq.val := by
            simp [moveBytes, toNat_toUInt8_lt sq.val (by omega)]
          simp only [C1, hm0, u8z, Bool.or_eq_true, Bool.not_eq_true', decide_eq_true_eq] at hC
          simp only [needsProbeC, Bool.or_eq_true]
          rcases hC with (h | h) | h
          · left; left; left; simpa using h
          · left; left; right; simpa using h
          · omega
      rw [this]; rfl
    · simp [t1, Locals.upd, show x ≠ 11 by omega, show x ≠ 16 by omega, show x ≠ 13 by omega]
  · have hCf : C1 = false := by simpa using hC
    simp only [C1, Bool.or_eq_false_iff, Bool.not_eq_false', bne_eq_false_iff_eq] at hCf
    obtain ⟨⟨hR1, hR2⟩, hM0⟩ := hCf
    cases m with
    | drop t d => simp [moveBytes] at hM0
    | normal sq d pr =>
      obtain ⟨pc, hpc, hcol, hcap⟩ := pseudo_normal hm
      have hsq := sq.isLt
      have hd81 := d.isLt
      have hm0 : ((moveBytes p (.normal sq d pr)).getD 0 0).toNat = sq.val := by
        simp [moveBytes, toNat_toUInt8_lt sq.val (by omega)]
      have hm1 : ((moveBytes p (.normal sq d pr)).getD 1 0).toNat = d.val := by
        simp [moveBytes, toNat_toUInt8_lt d.val (by omega)]
      obtain ⟨hval, hkb⟩ := ksRec_valid p p.side
      obtain ⟨k, hks⟩ : ∃ k, p.kingSquare p.side = some k := by
        cases h : p.kingSquare p.side with
        | none => rw [hval, h] at hR1; simp at hR1
        | some k => exact ⟨k, rfl⟩
      have hR0 : R.getD 0 0 = k.val.toUInt8 := hkb k hks
      -- the type of the moving piece
      have hfrom := ev_blk_u8 hl10 hn (k := 0) (by omega)
      rw [hm0] at hfrom
      have hle := encode_length p
      have hbd := ev_pos_u (base := 0) (P := encode p) hle hl0 hpos (t := IntTy.u8) rfl hfrom (by omega)
      rw [Nat.zero_add, encode_board p sq.val hsq] at hbd
      simp only [Fin.eta, hpc, pieceByte] at hbd
      rw [toNat_toUInt8_lt _ (piece_code_lt pc)] at hbd
      let t1 : State := { s with locals := s.locals.upd 12 (u32 pc.type.code) }
      have ec : ExS Gen.prog s (.call (some 12) 2 [(.load (.int ⟨8, false⟩) (.index (.field (.var 0) 0)
          (.load (.int ⟨8, false⟩) (.field (.var 10) 0)) 1))]) .normal t1 :=
        callS rfl pureS_type rfl (run_type pc) (EvArgs.cons hbd EvArgs.nil)
      have htc : pc.type.code < 2 ^ 32 := by cases pc.type <;> decide
      have heq8 : EvE Gen.prog t1 (.bin .eq (some ⟨32, false⟩) (.cast ⟨32, false⟩ (.var 12)) (.cast ⟨32, false⟩
          (.const (.int ⟨32, true⟩ 8)))) (boolVal (decide (pc.type = .king))) := by
        apply EvE_of_eval (n := 4)
        have h12 : t1.locals 12 = some (u32 pc.type.code) := by simp [t1, Locals.upd]
        have : (pc.type.code = 8) ↔ (pc.type = .king) := by cases pc.type <;> decide
        simp [evalExpr, h12, evalCast, evalBin, isPtr, evalBinInt, binInt, intOf, u32, IntTy.u32, IntTy.modulus,
          IntTy.toInt, IntTy.wrap, Res.bind, Nat.mod_eq_of_lt htc, this]
      have hk13 := evB_or' (s := t1) (b1 := false) (EvE.const (.int ⟨32, true⟩ 0)) rfl heq8 (truthy_boolVal _)
      simp only [Bool.false_or] at hk13
      let t2 : State := { t1 with locals := t1.locals.upd 13 (boolVal (decide (pc.type = .king))) }
      have e1 : ExS Gen.prog s (.ite (.lor (.lor (.un .lnot ⟨32, true⟩ (.load (.int ⟨8, false⟩) (.field (.var 8) 1))) (.cast ⟨32, true⟩ (.load (.int ⟨8, false⟩) (.field (.var 8) 2)))) (.bin .eq (some ⟨32, true⟩) (.cast ⟨32, true⟩ (.load (.int ⟨8, false⟩) (.field (.var 10) 0))) (.const (.int ⟨32, true⟩ 255)))) (.set 13 (.const (.int ⟨32, true⟩ 1))) (.seq (.call (some 12) 2 [(.load (.int ⟨8, false⟩) (.index (.field (.var 0) 0) (.load (.int ⟨8, false⟩) (.field (.var 10) 0)) 1))]) (.set 13 (.lor (.const (.int ⟨32, true⟩ 0)) (.bin .eq (some ⟨32, false⟩) (.cast ⟨32, false⟩ (.var 12)) (.cast ⟨32, false⟩ (.const (.int ⟨32, true⟩ 8)))))))) .normal t2 :=
        ExS.ite (bc := false) c1 (by rw [truthy_boolVal]; exact congrArg _ (Bool.eq_false_iff.mpr hC)) (ExS.seq ec (ExS.set hk13))
      have hsame : ∀ x, x < 11 → t2.locals x = s.locals x := fun x hx => by
        simp [t2, t1, Locals.upd, show x ≠ 13 by omega, show x ≠ 12 by omega]
      have hR1' : (R.getD 1 0 == 0) = false := by
        have := (u8z (R.getD 1 0)); rw [hR1] at this; simpa using this.symm
      have hR2' : (R.getD 2 0 != 0) = false := by
        have := (u8z (R.getD 2 0)); rw [hR2] at this; simp at this; simp [this]
      by_cases hkg : pc.type = .king
      · have hnp : needsProbeC R p (.normal sq d pr) = true := by
          simp [needsProbeC, hpc, hkg]
        refine ⟨_, ExS.seq e1 (tail1 t2 (by simp [t2, Locals.upd, hkg]; rfl)), rfl, ?_, fun x hx => ?_⟩
        · have hnp' : needsProbeC (ksRec p p.side) p (.normal sq d pr) = true := hnp
          simp only [Locals.upd, if_true, hnp']
        · simp [Locals.upd, show x ≠ 11 by omega, show x ≠ 16 by omega]; exact hsame x hx
      · have hkgf : decide (pc.type = .king) = false := by simpa using hkg
        have l13 : t2.locals 13 = some (boolVal false) := by simp [t2, Locals.upd, hkgf]
        have l8 : t2.locals 8 = some (.ptr Sb 0) := by simp [t2, t1, Locals.upd]; exact hl8
        have l10 : t2.locals 10 = some (.ptr n 0) := by simp [t2, t1, Locals.upd]; exact hl10
        have hSb2 : t2.mem Sb = some R := hSb
        have hn2 : t2.mem n = some (moveBytes p (.normal sq d pr)) := hn
        have hfrom2 := ev_blk_u8 l10 hn2 (k := 0) (by omega)
        rw [hm0] at hfrom2
        have hpinv : EvE Gen.prog t2 (.cast ⟨32, true⟩ (.load (.int ⟨8, false⟩) (.index (.field (.var 8) 3)
            (.load (.int ⟨8, false⟩) (.field (.var 10) 0)) 1))) (.int IntTy.i32 (R.getD (3 + sq.val) 0).toNat) := by
          refine EvE.cast (load_u8_at (o := 0 + 3 + sq.val * 1) (EvE.index (pb := .ptr Sb (0 + 3))
            (EvE.field (EvE.var l8) (by simp [ptrAddN, hSb2, hRl])) hfrom2 (by simp [ptrAddN, hSb2, hRl, IntTy.u8]; omega))
            hSb2 (by rw [hRl]; omega) |> fun h => by simpa using h) (truthy_i32c _ (UInt8.toNat_lt _))
        have hpb := ksRec_pinned p p.side k sq hks
        let PS := pinnedSpec p p.side k sq
        let SK := sameKingRay k sq d
        have hnp : needsProbeC R p (.normal sq d pr) = (PS && !SK) := by
          simp only [needsProbeC, hpc, hR1', hR2', Bool.false_or, hks]
          have hk' : (pc.type == PieceType.king) = false := by simpa using hkg
          have hpb' : R.getD (3 + sq.val) 0 = (if PS then 1 else 0) := hpb
          rw [hk', hpb', Bool.false_or]
          cases PS <;> rfl
        -- the pinned branch
        obtain ⟨t5, e5, e5m, l15, e5l⟩ : ∃ t5, ExS Gen.prog t2 (.ite (.cast ⟨32, true⟩ (.load (.int ⟨8, false⟩) (.index (.field (.var 8) 3) (.load (.int ⟨8, false⟩) (.field (.var 10) 0)) 1))) (.seq (.call (some 14) 20 [(.load (.int ⟨8, false⟩) (.field (.var 8) 0)), (.load (.int ⟨8, false⟩) (.field (.var 10) 0)), (.load (.int ⟨8, false⟩) (.field (.var 10) 1))]) (.set 15 (.land (.const (.int ⟨32, true⟩ 1)) (.un .lnot ⟨32, true⟩ (.var 14))))) (.set 15 (.const (.int ⟨32, true⟩ 0)))) .normal t5 ∧
            t5.mem = t2.mem ∧ t5.locals 15 = some (boolVal (PS && !SK)) ∧
            (∀ x, x < 11 → t5.locals x = t2.locals x) := by
          by_cases hps : PS = true
          · have hR0' := ev_blk_u8 l8 hSb2 (k := 0) (by omega)
            rw [hR0, toNat_toUInt8_lt _ (by omega)] at hR0'
            have hto2 := ev_blk_u8 l10 hn2 (k := 1) (by omega)
            rw [hm1] at hto2
            obtain ⟨sb, eb, hsbm⟩ := same_king_ray_spec k sq d t2.mem t2.ro
            let t3 : State := { t2 with mem := sb.mem, locals := t2.locals.upd 14 (u8 (if SK then 1 else 0)) }
            have ecall : ExS Gen.prog t2 (.call (some 14) 20 [(.load (.int ⟨8, false⟩) (.field (.var 8) 0)),
                (.load (.int ⟨8, false⟩) (.field (.var 10) 0)), (.load (.int ⟨8, false⟩) (.field (.var 10) 1))]) .normal t3 :=
              ExS.call_dst (EvArgs.cons hR0' (EvArgs.cons hfrom2 (EvArgs.cons hto2 EvArgs.nil))) rfl rfl eb
            have hmsb : sb.mem = t2.mem := hsbm
            have l14 : t3.locals 14 = some (u8 (if SK then 1 else 0)) := by simp [t3, Locals.upd]
            have hv15 := evB_and' (s := t3) (b1 := true) (EvE.const (.int ⟨32, true⟩ 1)) rfl
              (evB_not (EvE.var l14) (truthy_u8 _)) (truthy_boolVal _)
            have hsk : (!((if SK then 1 else 0 : Nat) != 0)) = !SK := by cases SK <;> rfl
            rw [hsk] at hv15
            refine ⟨_, ExS.ite (bc := true) hpinv (by rw [hpb]; simp [PS] at hps ⊢; simp [hps]; rfl)
              (ExS.seq ecall (ExS.set hv15)), by simp [t3, hmsb], by simp [Locals.upd, hps], fun x hx => ?_⟩
            simp [t3, Locals.upd, show x ≠ 15 by omega, show x ≠ 14 by omega]
          · have hpsf : PS = false := by simpa using hps
            refine ⟨_, ExS.ite (bc := false) hpinv (by rw [hpb]; simp [PS] at hpsf ⊢; simp [hpsf]; rfl)
              (ExS.set (EvE.const _)), rfl, by simp [Locals.upd, hpsf]; rfl, fun x hx => ?_⟩
            simp [Locals.upd, show x ≠ 15 by omega]
        have h16 := evB_or' (s := t5) (b1 := false) (EvE.const (.int ⟨32, true⟩ 0)) rfl (EvE.var l15) (truthy_boolVal _)
        simp only [Bool.false_or] at h16
        let t6 : State := { t5 with locals := t5.locals.upd 16 (boolVal (PS && !SK)) }
        have h11 := evB_u8 (s := t6) (x := PS && !SK) (e1 := .var 16) (EvE.var (by simp [t6, Locals.upd]))
        refine ⟨_, ExS.seq e1 (ExS.seq (ExS.ite (bc := false) (EvE.var l13) (truthy_boolVal _)
          (ExS.seq e5 (ExS.set h16))) (ExS.set h11)), ?_, ?_, fun x hx => ?_⟩
        · show t5.mem = s.mem; rw [e5m]
        · have hnp' : needsProbeC (ksRec p p.side) p (.normal sq d pr) = (PS && !SK) := hnp
          simp [Locals.upd, hnp']
        · simp [t6, Locals.upd, show x ≠ 11 by omega, show x ≠ 16 by omega]
          rw [e5l x hx]; exact hsame x hx

end Shogi.C.Proofs
