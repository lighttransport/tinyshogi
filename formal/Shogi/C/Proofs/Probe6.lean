/-
  T8: `make_legal_probe`, part 6 — the board-move branch.
-/
import Shogi.C.Proofs.Probe5

namespace Shogi.C.Proofs
open MiniC Shogi Shogi.C

def normHands (pa : Square → Option Piece) (h : Color → Fin 7 → Nat) (c : Color) (d : Square) :
    Color → Fin 7 → Nat :=
  match pa d with
  | some q => match q.type.unpromote.handIndex with
    | some i => hupd h c i (h c i + 1)
    | none => h
  | none => h

theorem toNat_toUInt8_lt (n : Nat) (h : n < 256) : n.toUInt8.toNat = n := by
  simp [Nat.toUInt8, UInt8.toNat_ofNat, Nat.mod_eq_of_lt h]

theorem pieceByte_toNat' (o : Option Piece) : (pieceByte o).toNat < 256 := UInt8.toNat_lt _

theorem unpromote_hand (t : PieceType) (h : t ≠ .king) : ∃ i, t.unpromote.handIndex = some i := by
  cases t <;> first | exact absurd rfl h | exact ⟨_, rfl⟩

theorem probe_norm {s : State} {pa h kb kw} {c : Color} {n ub : Nat} {U : List UInt8}
    {sq d : Square} {pc : Piece} {pr : Bool}
    (hl0 : s.locals 0 = some posPtr) (hl1 : s.locals 1 = some (.ptr n 0)) (hl2 : s.locals 2 = some (.ptr ub 0))
    (hl4 : s.locals 4 = some (.int IntTy.u32 c.idx))
    (hmp : s.mem posBlock = some (enc pa h c kb kw))
    (hmn : s.mem n = some [sq.val.toUInt8, d.val.toUInt8, pc.code.toUInt8, if pr then 1 else 0, 0])
    (hmu : s.mem ub = some U) (hU : U.length = 20)
    (hpu : posBlock ≠ ub) (hpn : posBlock ≠ n) (hnu : n ≠ ub) (hro : s.ro = false)
    (hsq : pa sq = some pc) (hcol : pc.color = c) (hcap : ∀ q, pa d = some q → q.type ≠ .king) :
    ∃ s' U', ExS Gen.prog s pbNorm .normal s' ∧ s'.ro = s.ro ∧
      s'.mem posBlock = some (enc (fun y => if y = sq then none else pa y) (normHands pa h c d) c kb kw) ∧
      s'.mem ub = some U' ∧ U'.length = 20 ∧ U'.getD 12 0 = (movedPiece c pc pr).code.toUInt8 ∧
      U'.getD 13 0 = pieceByte (pa d) ∧
      (∀ x, x ≠ posBlock → x ≠ ub → s'.mem x = s.mem x) ∧
      (∀ x, x ≤ 6 → s'.locals x = s.locals x) := by
  let P := enc pa h c kb kw
  have hP : P.length = 114 := enc_length _ _ _ _ _
  let MV : List UInt8 := [sq.val.toUInt8, d.val.toUInt8, pc.code.toUInt8, if pr then 1 else 0, 0]
  have hpcl := piece_code_lt pc
  have hsq81 := sq.isLt
  have hd81 := d.isLt
  have evMV : ∀ (t : State) (k : Nat), t.locals 1 = some (.ptr n 0) → t.mem n = some MV → k < 5 →
      EvE Gen.prog t (.load (.int ⟨8, false⟩) (.field (.var 1) k)) (.int IntTy.u8 (MV.getD k 0).toNat) :=
    fun t k h1 h2 hk => ev_blk_u8 h1 h2 (by simp [MV]; omega)
  -- pn0, pn1 : moving and captured bytes
  have hfrom := evMV s 0 hl1 hmn (by decide)
  have hfrom' : (MV.getD 0 0).toNat = sq.val := by simp [MV, toNat_toUInt8_lt sq.val (by omega)]
  rw [hfrom'] at hfrom
  have ev7 := ev_pos_u (base := 0) hP hl0 hmp (t := IntTy.u8) rfl hfrom (by omega)
  rw [Nat.zero_add, enc_getD_board, hsq] at ev7
  let s1 : State := { s with locals := s.locals.upd 7 (.int IntTy.u8 (pieceByte (some pc)).toNat) }
  have e0 : ExS Gen.prog s pn0 .normal s1 := ExS.set ev7
  have hto := evMV s1 1 (by simp [s1, Locals.upd]; exact hl1) hmn (by decide)
  have hto' : (MV.getD 1 0).toNat = d.val := by simp [MV, toNat_toUInt8_lt d.val (by omega)]
  rw [hto'] at hto
  have ev8 := ev_pos_u (s := s1) (base := 0) hP (by simp [s1, Locals.upd]; exact hl0) hmp (t := IntTy.u8) rfl hto (by omega)
  rw [Nat.zero_add, enc_getD_board] at ev8
  let capb := (pieceByte (pa d)).toNat
  let s2 : State := { s1 with locals := s1.locals.upd 8 (.int IntTy.u8 capb) }
  have e1 : ExS Gen.prog s1 pn1 .normal s2 := ExS.set ev8
  have l2s2 : s2.locals 2 = some (.ptr ub 0) := by simp [s2, s1, Locals.upd]; exact hl2
  have e2 := store_int_field (s := s2) (o := 0) (b := ub) (j := 2) (t := ⟨8, false⟩) (i := 12)
    (v := (pieceByte (some pc)).toNat) (e := .var 7) (blk := U) l2s2 hmu (by rw [hU]; decide)
    (EvE.var (by simp [s2, s1, Locals.upd]; rfl)) hro (encodeLE_length _ _)
  let m3 := s.mem.write ub (0 + 12) (encodeLE 1 (pieceByte (some pc)).toNat)
  let U2 := U.set 12 (pieceByte (some pc))
  have hm3u : m3 ub = some U2 := by
    show (s.mem.write ub (0 + 12) _) ub = _
    rw [write1_set (o := 0 + 12) hmu (by omega)]; simp [U2]
  have e3 := store_int_field (s := { s2 with mem := m3 }) (o := 0) (b := ub) (j := 2) (t := ⟨8, false⟩) (i := 13)
    (v := capb) (e := .var 8) (blk := U2) l2s2 hm3u (by simp [U2, hU, IntTy.bytes])
    (EvE.var (by simp [s2, Locals.upd]; rfl)) hro (encodeLE_length _ _)
  let m4 := m3.write ub (0 + 13) (encodeLE 1 capb)
  let U3 := U2.set 13 (pieceByte (pa d))
  have hm4u : m4 ub = some U3 := by
    show (m3.write ub (0 + 13) _) ub = _
    rw [write1_set (o := 0 + 13) hm3u (by simp [U2, hU])]; simp [U3, capb]
  have hm4p : m4 posBlock = some P := by
    simp only [m4, m3]; rw [Mem.write_ne hpu, Mem.write_ne hpu]; exact hmp
  have hm4n : m4 n = some MV := by
    simp only [m4, m3]; rw [Mem.write_ne hnu, Mem.write_ne hnu]; exact hmn
  -- pn4 : board[from] = 0
  let t4 : State := { s2 with mem := m4 }
  have hfrom4 := evMV t4 0 (by simp [t4, s2, s1, Locals.upd]; exact hl1) hm4n (by decide)
  rw [hfrom'] at hfrom4
  have e4 := st_pos_u (s := t4) (base := 0) hP (by simp [t4, s2, s1, Locals.upd]; exact hl0) hm4p
    (t := IntTy.u8) rfl hfrom4 (by omega) (ev := .cast ⟨8, false⟩ (.const (.int ⟨32, true⟩ 0))) (v := 0)
    (EvE_of_eval (n := 3) (by rfl)) hro
  let P1 := enc (fun y => if y = sq then none else pa y) h c kb kw
  let m5 := m4.write posBlock (0 + sq.val) (encodeLE 1 0)
  have hm5p : m5 posBlock = some P1 := by
    show (m4.write posBlock (0 + sq.val) (encodeLE 1 0)) posBlock = _
    rw [Nat.zero_add, write1_set hm4p (by rw [hP]; omega)]
    have := enc_set_board pa h c kb kw sq none
    simp only [pieceByte] at this; exact congrArg some this
  let t5 : State := { t4 with mem := m5 }
  have hm5u : m5 ub = some U3 := by simp only [m5]; rw [Mem.write_ne (Ne.symm hpu)]; exact hm4u
  have l8 : t5.locals 8 = some (.int IntTy.u8 capb) := by simp [t5, t4, s2, Locals.upd]
  obtain ⟨s6, U4, e5, hro6, hm6p, hm6u, hU4, hU412, hU413, hm6o, hl6⟩ : ∃ s6 U4,
      ExS Gen.prog t5 pn5 .normal s6 ∧ s6.ro = t5.ro ∧
      s6.mem posBlock = some (enc (fun y => if y = sq then none else pa y) (normHands pa h c d) c kb kw) ∧
      s6.mem ub = some U4 ∧ U4.length = 20 ∧ U4.getD 12 0 = pieceByte (some pc) ∧
      U4.getD 13 0 = pieceByte (pa d) ∧ (∀ x, x ≠ posBlock → x ≠ ub → s6.mem x = t5.mem x) ∧
      (∀ x, x ≠ 9 → x ≠ 10 → x ≠ 11 → x ≠ 12 → s6.locals x = t5.locals x) := by
    have hU3l : U3.length = 20 := by simp [U3, U2, hU]
    have hU312 : U3.getD 12 0 = pieceByte (some pc) := by
      simp [U3, U2, List.getD_eq_getElem?_getD, List.getElem?_set, hU]
    have hU313 : U3.getD 13 0 = pieceByte (pa d) := by
      simp [U3, U2, List.getD_eq_getElem?_getD, List.getElem?_set, hU]
    cases hpd : pa d with
    | none =>
      have hc0 : capb = 0 := by simp [capb, hpd, pieceByte]
      have hz := ev_ne0 (s := t5) (by rw [hc0]; decide) l8
      refine ⟨t5, U3, by rw [pn5_eq]; exact ExS.ite (bc := false) hz (by simp [truthy_boolVal, hc0]) ExS.skip,
        rfl, ?_, hm5u, hU3l, hU312, by rw [hU313, hpd], fun _ _ _ => rfl, fun _ _ _ _ _ => rfl⟩
      simp only [normHands, hpd]; exact hm5p
    | some q =>
      obtain ⟨i, hi⟩ := unpromote_hand q.type (hcap q hpd)
      have hcq : capb = q.code := by simp [capb, hpd, pieceByte, toNat_toUInt8_lt _ (piece_code_lt q)]
      have hq0 : q.code ≠ 0 := by obtain ⟨qc, qt⟩ := q; cases qc <;> cases qt <;> decide
      have hz := ev_ne0 (s := t5) (by rw [hcq]; exact piece_code_lt q) l8
      obtain ⟨s6, ec, hro6, hp6, hu6, ho6, hl6⟩ := cap_spec (s := t5) (q := q) (i := i)
        (by simp [t5, t4, s2, s1, Locals.upd]; exact hl0) (by simp [t5, t4, s2, s1, Locals.upd]; exact hl2)
        (by simp [t5, t4, s2, s1, Locals.upd]; exact hl4) (by rw [l8, hcq]; rfl) hm5p hm5u hU3l hpu hro hi
      refine ⟨s6, (U3.set 15 i.val.toUInt8).set 16 (h c i).toUInt8,
        by rw [pn5_eq]; exact ExS.ite (bc := true) hz (by simp [truthy_boolVal, hcq, hq0]) ec,
        hro6, ?_, hu6, by simp [hU3l], ?_, ?_, ho6, hl6⟩
      · simp only [normHands, hpd, hi]; exact hp6
      · rw [← hU312]; simp [List.getD_eq_getElem?_getD, List.getElem?_set]
      · rw [← hpd, ← hU313]; simp [List.getD_eq_getElem?_getD, List.getElem?_set]
  have l1_6 : s6.locals 1 = some (.ptr n 0) := by
    rw [hl6 1 (by decide) (by decide) (by decide) (by decide)]; simp [t5, t4, s2, s1, Locals.upd]; exact hl1
  have hm6n : s6.mem n = some MV := by rw [hm6o n (Ne.symm hpn) hnu]; simp only [t5, m5]; rw [Mem.write_ne (Ne.symm hpn)]; exact hm4n
  have hprv := evMV s6 3 l1_6 hm6n (by decide)
  have hpr' : (MV.getD 3 0).toNat = if pr then 1 else 0 := by cases pr <;> rfl
  rw [hpr'] at hprv
  have l7_6 : s6.locals 7 = some (u8 pc.code) := by
    rw [hl6 7 (by decide) (by decide) (by decide) (by decide)]
    simp [t5, t4, s2, s1, Locals.upd, pieceByte, u8, toNat_toUInt8_lt _ hpcl]
  have l4_6 : s6.locals 4 = some (u32 c.idx) := by
    rw [hl6 4 (by decide) (by decide) (by decide) (by decide)]; simp [t5, t4, s2, s1, Locals.upd]; exact hl4
  have l2_6 : s6.locals 2 = some (.ptr ub 0) := by
    rw [hl6 2 (by decide) (by decide) (by decide) (by decide)]; simp [t5, t4, s2, s1, Locals.upd]; exact hl2
  have hmv : (movedPiece c pc pr).code.toUInt8 = if pr then (Piece.code ⟨c, pc.type.promote⟩).toUInt8
      else pieceByte (some pc) := by
    cases pr <;> simp [movedPiece, pieceByte, ← hcol]
  have hmvl : (Piece.code ⟨c, pc.type.promote⟩) < 256 := piece_code_lt _
  by_cases hp : pr = true
  · -- promotion: undo->moving_piece = shogi_piece(color, promoted_type(type))
    let s7a : State := { s6 with locals := s6.locals.upd 13 (u32 pc.type.code) }
    have c1 : ExS Gen.prog s6 (.call (some 13) 2 [(.var 7)]) .normal s7a :=
      callS rfl pureS_type rfl (run_type pc) (EvArgs.cons (EvE.var l7_6) EvArgs.nil)
    let s7b : State := { s7a with locals := s7a.locals.upd 14 (u32 pc.type.promote.code) }
    have c2 : ExS Gen.prog s7a (.call (some 14) 6 [(.var 13)]) .normal s7b :=
      callS rfl pureS_promote rfl (run_promote pc.type) (EvArgs.cons (EvE.var (by simp [s7a, Locals.upd])) EvArgs.nil)
    let s7c : State := { s7b with locals := s7b.locals.upd 15 (u8 (Piece.code ⟨c, pc.type.promote⟩)) }
    have c3 : ExS Gen.prog s7b (.call (some 15) 0 [(.var 4), (.var 14)]) .normal s7c :=
      callS rfl pureS_piece rfl (run_piece c pc.type.promote)
        (EvArgs.cons (EvE.var (by simp [s7b, s7a, Locals.upd]; exact l4_6))
          (EvArgs.cons (EvE.var (by simp [s7b, Locals.upd])) EvArgs.nil))
    have st := store_int_field (s := s7c) (o := 0) (b := ub) (j := 2) (t := ⟨8, false⟩) (i := 12)
      (v := Piece.code ⟨c, pc.type.promote⟩) (e := .var 15) (blk := U4)
      (by simp [s7c, s7b, s7a, Locals.upd]; exact l2_6) hm6u (by rw [hU4]; decide)
      (EvE.var (by simp [s7c, Locals.upd]; rfl)) (show s6.ro = false by rw [hro6]; exact hro) (encodeLE_length _ _)
    let U5 := U4.set 12 (Piece.code ⟨c, pc.type.promote⟩).toUInt8
    refine ⟨{ s7c with mem := s6.mem.write ub (0 + 12) (encodeLE 1 (Piece.code ⟨c, pc.type.promote⟩)) }, U5,
      ExS.seq e0 (ExS.seq e1 (ExS.seq e2 (ExS.seq e3 (ExS.seq e4 (ExS.seq e5
        (ExS.ite (bc := true) hprv (by simp [truthy, hp]) (ExS.seq c1 (ExS.seq c2 (ExS.seq c3 st))))))))),
      hro6, ?_, ?_, by simp [U5, hU4], ?_, ?_, ?_, ?_⟩
    · show (s6.mem.write ub _ _) posBlock = _; rw [Mem.write_ne hpu]; exact hm6p
    · show (s6.mem.write ub _ _) ub = _; rw [write1_set hm6u (by omega)]
    · rw [hmv, if_pos hp]; simp [U5, List.getD_eq_getElem?_getD, List.getElem?_set, hU4]
    · rw [← hU413]; simp [U5, List.getD_eq_getElem?_getD, List.getElem?_set]
    · intro x a b; show (s6.mem.write ub _ _) x = _; rw [Mem.write_ne b, hm6o x a b]
      simp only [t5, m5, m4, m3]; rw [Mem.write_ne a, Mem.write_ne b, Mem.write_ne b]
    · intro x hx
      simp [s7c, s7b, s7a, Locals.upd, show x ≠ 13 by omega, show x ≠ 14 by omega, show x ≠ 15 by omega]
      rw [hl6 x (by omega) (by omega) (by omega) (by omega)]
      simp [t5, t4, s2, s1, Locals.upd, show x ≠ 7 by omega, show x ≠ 8 by omega]
  · have hpf : pr = false := by simpa using hp
    refine ⟨s6, U4, ExS.seq e0 (ExS.seq e1 (ExS.seq e2 (ExS.seq e3 (ExS.seq e4 (ExS.seq e5
        (ExS.ite (bc := false) hprv (by simp [truthy, hpf]) ExS.skip)))))),
      by rw [hro6], hm6p, hm6u, hU4, by rw [hmv, if_neg hp]; exact hU412, hU413, ?_, ?_⟩
    · intro x a b; rw [hm6o x a b]
      simp only [t5, m5, m4, m3]; rw [Mem.write_ne a, Mem.write_ne b, Mem.write_ne b]
    · intro x hx
      rw [hl6 x (by omega) (by omega) (by omega) (by omega)]
      simp [t5, t4, s2, s1, Locals.upd, show x ≠ 7 by omega, show x ≠ 8 by omega]

end Shogi.C.Proofs
