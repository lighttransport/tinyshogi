/-
  T8: `make_legal_probe`, part 9 — what membership in `pseudoMoves` gives,
  and the final refinement theorem.
-/
import Shogi.C.Proofs.Probe8

namespace Shogi.C.Proofs
open MiniC Shogi Shogi.C

theorem pseudo_normal {p : Position} {s d : Square} {pr : Bool} (h : Move.normal s d pr ∈ p.pseudoMoves) :
    ∃ pc, p.pieceAt s = some pc ∧ pc.color = p.side ∧ ∀ q, p.pieceAt d = some q → q.type ≠ .king := by
  unfold Position.pseudoMoves at h
  rw [List.mem_append] at h
  rcases h with h | h
  · rw [List.mem_flatMap] at h
    obtain ⟨s', _, hs'⟩ := h
    cases hp : p.pieceAt s' with
    | none => simp [hp] at hs'
    | some pc =>
      simp only [hp] at hs'
      split at hs'
      · next hc =>
        unfold Position.boardMoves at hs'
        rw [List.mem_flatMap] at hs'
        obtain ⟨d', _, hd'⟩ := hs'
        cases hq : p.pieceAt d' with
        | none =>
          simp only [hq, List.mem_map] at hd'
          obtain ⟨_, _, e⟩ := hd'; cases e
          exact ⟨pc, hp, by simpa using hc, fun q hq' => by rw [hq] at hq'; cases hq'⟩
        | some q =>
          simp only [hq] at hd'
          split at hd'
          · simp at hd'
          · next hk =>
            simp only [List.mem_map] at hd'
            obtain ⟨_, _, e⟩ := hd'; cases e
            refine ⟨pc, hp, by simpa using hc, fun q' hq' => ?_⟩
            rw [hq] at hq'; cases hq'
            intro hqk; apply hk; simp [hqk]
      · simp at hs'
  · unfold Position.dropMoves at h
    rw [List.mem_flatMap] at h
    obtain ⟨_, _, h⟩ := h
    rw [List.mem_filterMap] at h
    obtain ⟨_, _, h⟩ := h
    simp only at h; split at h <;> simp at h

theorem pseudo_drop {p : Position} {t : PieceType} {d : Square} (h : Move.drop t d ∈ p.pseudoMoves) :
    ∃ i, t.handIndex = some i ∧ 0 < p.hand p.side i ∧ p.pieceAt d = none := by
  unfold Position.pseudoMoves at h
  rw [List.mem_append] at h
  rcases h with h | h
  · rw [List.mem_flatMap] at h
    obtain ⟨s', _, hs'⟩ := h
    cases hp : p.pieceAt s' with
    | none => simp [hp] at hs'
    | some pc =>
      simp only [hp] at hs'
      split at hs'
      · unfold Position.boardMoves at hs'
        rw [List.mem_flatMap] at hs'
        obtain ⟨d', _, hd'⟩ := hs'
        cases hq : p.pieceAt d' with
        | none => simp [hq] at hd'
        | some q => simp only [hq] at hd'; split at hd' <;> simp at hd'
      · simp at hs'
  · unfold Position.dropMoves at h
    rw [List.mem_flatMap] at h
    obtain ⟨d', _, h⟩ := h
    rw [List.mem_filterMap] at h
    obtain ⟨i, _, h⟩ := h
    simp only at h; split at h
    · next hc =>
      simp only [Option.some.injEq, Move.drop.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      simp only [Bool.and_eq_true, decide_eq_true_eq, Position.dropAllowed, Position.isEmpty,
        Option.isNone_iff_eq_none] at hc
      exact ⟨i, PieceType.handIndex_ofHandIndex i, hc.1, hc.2.1.1⟩
    · simp at h

theorem wrb_getD_out (blk : List UInt8) (o k : Nat) (bs : List UInt8) (hl : o + bs.length ≤ blk.length)
    (hk : k < o ∨ o + bs.length ≤ k) : (wrb blk o bs).getD k 0 = blk.getD k 0 := by
  simp only [wrb, List.getD_eq_getElem?_getD]
  rcases hk with hk | hk
  · rw [List.append_assoc, List.getElem?_append_left (by simp; omega), List.getElem?_take, if_pos hk]
  · rw [List.getElem?_append_right (by simp; omega), List.getElem?_drop]
    congr 2; simp; omega

theorem wrb_getD_in (blk : List UInt8) (o k : Nat) (bs : List UInt8) (hl : o + bs.length ≤ blk.length)
    (hk1 : o ≤ k) (hk2 : k < o + bs.length) : (wrb blk o bs).getD k 0 = bs.getD (k - o) 0 := by
  simp only [wrb, List.getD_eq_getElem?_getD]
  rw [List.getElem?_append_left (by simp; omega), List.getElem?_append_right (by simp; omega)]
  congr 2; simp; omega

theorem take_of_getD (U L : List UInt8) (o n : Nat) (hL : L.length = n) (hU : o + n ≤ U.length)
    (h : ∀ k, k < n → U.getD (o + k) 0 = L.getD k 0) : (U.drop o).take n = L := by
  apply List.ext_getElem
  · simp; omega
  · intro k h1 h2
    have := h k (by omega)
    simp only [List.getD_eq_getElem?_getD] at this
    rw [List.getElem?_eq_getElem (by omega), List.getElem?_eq_getElem (by omega)] at this
    simp only [Option.getD_some] at this
    simp [this]

section ub1facts
variable (UB MV : List UInt8) (c : Nat) (kbc : UInt8) (hU : UB.length = 20) (hM : MV.length = 5)
include hU hM

theorem ub1_getD_out (k : Nat) (h1 : 5 ≤ k) (h2 : k < 8 ∨ 17 ≤ k) : (ub1 UB MV c kbc).getD k 0 = UB.getD k 0 := by
  have l4 := encodeLE_length 4 c
  simp only [ub1]
  rw [wrb_getD_out _ _ _ _ (by simp [wrb, hU, hM, l4]) (by simp [l4]; omega)]
  rw [wrb_getD_out _ _ _ _ (by simp [wrb, hU, hM, l4]) (by simp [l4]; omega)]
  rw [wrb_getD_out _ _ _ _ (by simp [wrb, hU, hM, l4]) (by simp [l4]; omega)]
  rw [wrb_getD_out _ _ _ _ (by simp [wrb, hU, hM, l4]) (by simp [l4]; omega)]
  rw [wrb_getD_out _ _ _ _ (by simp [wrb, hU, hM, l4]) (by simp [l4]; omega)]
  rw [wrb_getD_out _ _ _ _ (by simp [wrb, hU, hM, l4]) (by simp [l4]; omega)]

theorem ub1_mv (k : Nat) (hk : k < 5) : (ub1 UB MV c kbc).getD k 0 = MV.getD k 0 := by
  have l4 := encodeLE_length 4 c
  simp only [ub1]
  rw [wrb_getD_out _ _ _ _ (by simp [wrb, hU, hM, l4]) (by simp [l4]; omega)]
  rw [wrb_getD_out _ _ _ _ (by simp [wrb, hU, hM, l4]) (by simp [l4]; omega)]
  rw [wrb_getD_out _ _ _ _ (by simp [wrb, hU, hM, l4]) (by simp [l4]; omega)]
  rw [wrb_getD_out _ _ _ _ (by simp [wrb, hU, hM, l4]) (by simp [l4]; omega)]
  rw [wrb_getD_out _ _ _ _ (by simp [wrb, hU, hM, l4]) (by simp [l4]; omega)]
  rw [wrb_getD_in _ _ _ _ (by simp [hU, hM]) (by omega) (by omega), Nat.sub_zero]

theorem ub1_c (k : Nat) (hk : k < 4) : (ub1 UB MV c kbc).getD (8 + k) 0 = (encodeLE 4 c).getD k 0 := by
  have l4 := encodeLE_length 4 c
  simp only [ub1]
  rw [wrb_getD_out _ _ _ _ (by simp [wrb, hU, hM, l4]) (by simp [l4]; omega)]
  rw [wrb_getD_out _ _ _ _ (by simp [wrb, hU, hM, l4]) (by simp [l4]; omega)]
  rw [wrb_getD_out _ _ _ _ (by simp [wrb, hU, hM, l4]) (by simp [l4]; omega)]
  rw [wrb_getD_out _ _ _ _ (by simp [wrb, hU, hM, l4]) (by simp [l4]; omega)]
  rw [wrb_getD_in _ _ _ _ (by simp [wrb, hU, hM, l4]) (by omega) (by omega)]; congr 1; omega

theorem ub1_14 : (ub1 UB MV c kbc).getD 14 0 = kbc := by
  have l4 := encodeLE_length 4 c
  simp only [ub1]
  rw [wrb_getD_out _ _ _ _ (by simp [wrb, hU, hM, l4]) (by simp [l4])]
  rw [wrb_getD_out _ _ _ _ (by simp [wrb, hU, hM, l4]) (by simp [l4])]
  rw [wrb_getD_in _ _ _ _ (by simp [wrb, hU, hM, l4]) (by omega) (by simp)]; rfl

theorem ub1_15 : (ub1 UB MV c kbc).getD 15 0 = 255 := by
  have l4 := encodeLE_length 4 c
  simp only [ub1]
  rw [wrb_getD_out _ _ _ _ (by simp [wrb, hU, hM, l4]) (by simp [l4])]
  rw [wrb_getD_in _ _ _ _ (by simp [wrb, hU, hM, l4]) (by omega) (by simp)]; rfl

theorem ub1_len : (ub1 UB MV c kbc).length = 20 := ub1_length UB MV c kbc hU hM

end ub1facts

/-- What the probe leaves in the undo record (what `unmake_legal_probe` reads). -/
def UndoRec (p : Position) (mv : Move) (U : List UInt8) : Prop :=
  U.length = 20 ∧ (U.drop 0).take 5 = moveBytes p mv ∧ (U.drop 8).take 4 = le32 p.side.idx ∧
  U.getD 14 0 = kingByte p p.side ∧
  match mv with
  | .normal _ d _ => U.getD 13 0 = pieceByte (p.pieceAt d) ∧
      (match p.pieceAt d with
        | some q => match q.type.unpromote.handIndex with
          | some i => U.getD 15 0 = i.val.toUInt8 ∧ U.getD 16 0 = (p.hand p.side i).toUInt8
          | none => True
        | none => U.getD 15 0 = 255)
  | .drop t _ => match t.handIndex with
      | some i => U.getD 15 0 = i.val.toUInt8 ∧ U.getD 16 0 = (p.hand p.side i).toUInt8
      | none => True

theorem kbAfter_eq (p : Position) {s d : Square} {pc : Piece} {pr : Bool} (hcol : pc.color = p.side) (me : Color) :
    kbAfter p.side (movedPiece p.side pc pr) d (kingByte p me) me = kbOf (kingAfter p s d pc me) := by
  unfold kbAfter kingAfter
  have : (movedPiece p.side pc pr).type = .king ↔ pc.type = .king := by
    simp only [movedPiece]; cases pr <;> simp [promote_king]
  by_cases hk : pc.type = .king ∧ p.side = me
  · rw [if_pos (by rw [this]; exact hk), if_pos ⟨hk.1, by rw [hcol]; exact hk.2.symm⟩]; rfl
  · rw [if_neg (by rw [this]; exact hk), if_neg (fun h => hk ⟨h.1, by rw [← hcol]; exact h.2.symm⟩)]
    unfold kingByte kbOf; cases p.kingSquare me <;> rfl

theorem pbCond_ev {s : State} {n : Nat} {MV : List UInt8} (hl1 : s.locals 1 = some (.ptr n 0))
    (hmn : s.mem n = some MV) (hMV : MV.length = 5) :
    EvE Gen.prog s pbCond (boolVal (decide ((MV.getD 0 0).toNat = 255))) := by
  have hv := ev_blk_u8 hl1 hmn (k := 0) (by omega)
  have hb := UInt8.toNat_lt (MV.getD 0 0)
  generalize hx : (MV.getD 0 0).toNat = x at hv hb ⊢
  refine EvE.bin (EvE.cast hv rfl) (EvE.const _) ?_
  have : x < 256 := hb
  simp [evalBin, isPtr, evalBinInt, binInt, intOf, IntTy.u8, evalCast, IntTy.modulus, IntTy.toInt, Res.bind,
    Nat.mod_eq_of_lt (show x < 4294967296 by omega), show ¬ (2147483648 ≤ x) by omega]
  congr 2; exact propext (by omega)

/-- **`make_legal_probe` refines `Position.play`** on the position block, for
    every pseudo-legal move of a shaped position with at most one king per
    colour. -/
theorem Fresh.congr {m m' : Mem} {n : Nat} (hf : Fresh m n) (h0 : m' 0 = m 0) (h : ∀ x, n ≤ x → m' x = m x) :
    Fresh m' n := ⟨by rw [h0]; exact hf.1, hf.2.1, fun x hx => by rw [h x hx]; exact hf.2.2 x hx⟩

theorem kbc_eq (p : Position) :
    (enc p.pieceAt p.hand p.side (kingByte p .black) (kingByte p .white)).getD (112 + p.side.idx) 0 =
      kingByte p p.side := by
  rw [enc_getD_king]; cases p.side <;> rfl

theorem make_probe_spec (p : Position) (hS : p.Shaped) (hK : KingsUnique p) (mv : Move) (hm : mv ∈ p.pseudoMoves)
    {M : Mem} {mvb ub n : Nat} {UB : List UInt8}
    (hp : M posBlock = some (encode p)) (hmv : M mvb = some (moveBytes p mv)) (hub : M ub = some UB)
    (hUB : UB.length = 20) (hf : Fresh M n) (h64 : n + 1 < 2 ^ 64)
    (hmvb0 : mvb ≠ 0) (hub0 : ub ≠ 0) (hpu : posBlock ≠ ub) :
    ∃ s', ExS Gen.prog ⟨frameLocals Gen.make_legal_probe.params [posPtr, .ptr mvb 0, .ptr ub 0], M, false⟩
        Gen.make_legal_probe.body .normal s' ∧
      s'.mem posBlock = some (encode (p.play mv)) ∧
      (∀ x, x ≠ 0 → x ≠ n → x ≠ ub → x ≠ posBlock → s'.mem x = M x) ∧ s'.ro = false ∧
      (∃ U, s'.mem ub = some U ∧ UndoRec p mv U) ∧ Fresh s'.mem (n + 1) := by
  rw [encode_enc] at hp
  have hMVl : (moveBytes p mv).length = 5 := by cases mv <;> rfl
  obtain ⟨s1, hpre, hP⟩ := probe_pre (sd := p.side) hp hmv hub hMVl hUB hf h64 hmvb0 hub0 hpu
  have hnu : n ≠ ub := fun e => by rw [← e, hf.2.2 n (Nat.le_refl _)] at hub; cases hub
  have hbody : Gen.make_legal_probe.body = pbPre (.seq (.ite pbCond pbDrop pbNorm) (.seq pb11 (.seq pb12 pb13))) :=
    probe_body_eq
  rw [hbody]
  have hpn : posBlock ≠ n := fun e => by rw [e, hf.2.2 n (Nat.le_refl _)] at hp; cases hp
  have hcond := pbCond_ev hP.l1 hP.mn hMVl
  have hUl := ub1_length UB (moveBytes p mv) p.side.idx ((enc p.pieceAt p.hand p.side (kingByte p .black)
    (kingByte p .white)).getD (112 + p.side.idx) 0) hUB hMVl
  cases mv with
  | normal sq d pr =>
    obtain ⟨pc, hpc, hcol, hcap⟩ := pseudo_normal hm
    have hmvb : moveBytes p (.normal sq d pr) = [sq.val.toUInt8, d.val.toUInt8, pc.code.toUInt8,
        if pr then 1 else 0, 0] := by simp [moveBytes, hpc, pieceByte]
    have hc0 : ((moveBytes p (.normal sq d pr)).getD 0 0).toNat = sq.val := by
      rw [hmvb]; simp [toNat_toUInt8_lt sq.val (by omega)]
    rw [hc0] at hcond
    have hmn := hP.mn; rw [hmvb] at hmn
    obtain ⟨s2, U2, e2, hro2, hp2, hu2, hU2, hU212, hU213, hUT, ho2, hl2⟩ := probe_norm (pa := p.pieceAt) (h := p.hand)
      (sq := sq) (d := d) (pc := pc) (pr := pr) hP.l0 hP.l1 hP.l2 hP.l4 hP.mp hmn hP.mu hUl hpu hpn hnu hP.ro
      hpc hcol hcap
    have hmn2 : s2.mem n = some (moveBytes p (.normal sq d pr)) := by rw [ho2 n (Ne.symm hpn) hnu]; exact hP.mn
    obtain ⟨s3, e3, hro3, hp3, ho3, hl3⟩ := probe_tail (M := movedPiece p.side pc pr) (d := d)
      (by rw [hl2 0 (by omega)]; exact hP.l0) (by rw [hl2 1 (by omega)]; exact hP.l1)
      (by rw [hl2 2 (by omega)]; exact hP.l2) (by rw [hl2 4 (by omega)]; exact hP.l4) hp2 hmn2 hMVl
      (by rw [hmvb]; rfl) hu2 hU2 hU212 hpu hpn (by rw [hro2]; exact hP.ro)
    refine ⟨s3, hpre (ExS.seq (ExS.ite (bc := false) hcond (by simp [truthy_boolVal]; omega) e2) e3), ?_, ?_, ?_⟩
    · rw [hp3, encode_play_normal p hS hK hpc hcol (fun c' h => hcap _ h rfl), kbAfter_eq p hcol,
        kbAfter_eq p hcol]
      rfl
    · intro x a b c d'
      rw [ho3 x d', ho2 x d' c, hP.other x a b c]
    · refine ⟨by rw [hro3, hro2]; exact hP.ro, ⟨U2, by rw [ho3 ub (Ne.symm hpu)]; exact hu2, ?_⟩, ?_⟩
      · have hk := kbc_eq p
        refine ⟨hU2, take_of_getD _ _ 0 5 hMVl (by omega) (fun k hk5 => ?_),
          take_of_getD _ _ 8 4 (by simp [le32]) (by omega) (fun k hk4 => ?_), ?_, hU213, ?_⟩
        · rw [Nat.zero_add, hUT.1 k (by omega) (by omega) (by omega) (by omega), ub1_mv _ _ _ _ hUB hMVl k hk5]
        · rw [hUT.1 (8 + k) (by omega) (by omega) (by omega) (by omega), ub1_c _ _ _ _ hUB hMVl k hk4,
            le32_small _ (by cases p.side <;> decide)]
        · rw [hUT.1 14 (by omega) (by omega) (by omega) (by omega), ub1_14 _ _ _ _ hUB hMVl, hk]
        · have h2 := hUT.2
          cases hpd : p.pieceAt d with
          | none => simp only [hpd] at h2 ⊢; rw [h2.1, ub1_15 _ _ _ _ hUB hMVl]
          | some q => simp only [hpd] at h2 ⊢; exact h2
      · have hp1 : posBlock < n := Nat.lt_of_not_le (fun hc => by
          have := hf.2.2 posBlock hc; rw [this] at hp; cases hp)
        have hu1 : ub < n := Nat.lt_of_not_le (fun hc => by
          have := hf.2.2 ub hc; rw [this] at hub; cases hub)
        exact hP.fresh.congr (by rw [ho3 0 (by decide), ho2 0 (by decide) (Ne.symm hub0)])
          (fun x hx => by rw [ho3 x (by omega), ho2 x (by omega) (by omega)])
  | drop t d =>
    obtain ⟨i, hi, hh, hd⟩ := pseudo_drop hm
    have hcode := code_handIndex hi
    have hmvb : moveBytes p (.drop t d) = [255, d.val.toUInt8, 0, 0, t.code.toUInt8] := rfl
    have hc0 : ((moveBytes p (.drop t d)).getD 0 0).toNat = 255 := rfl
    rw [hc0] at hcond
    have hmn := hP.mn; rw [hmvb] at hmn
    obtain ⟨s2, U2, e2, hro2, hp2, hu2, hU2, hU212, hDo, hD15, hD16, ho2, hl2⟩ := probe_drop (pa := p.pieceAt) (h := p.hand)
      (d := d) (t := t) (i := i) hP.l0 hP.l1 hP.l2 hP.l4 hP.mp hmn hP.mu hUl hpu hpn hnu hP.ro hi hh
    have hmn2 : s2.mem n = some (moveBytes p (.drop t d)) := by rw [ho2 n (Ne.symm hpn) hnu]; exact hP.mn
    obtain ⟨s3, e3, hro3, hp3, ho3, hl3⟩ := probe_tail (M := ⟨p.side, t⟩) (d := d)
      (by rw [hl2 0 (by omega)]; exact hP.l0) (by rw [hl2 1 (by omega)]; exact hP.l1)
      (by rw [hl2 2 (by omega)]; exact hP.l2) (by rw [hl2 4 (by omega)]; exact hP.l4) hp2 hmn2 hMVl
      (by rw [hmvb]; rfl) hu2 hU2 hU212 hpu hpn (by rw [hro2]; exact hP.ro)
    have htk : t ≠ .king := by intro h; subst h; simp [PieceType.handIndex] at hi
    refine ⟨s3, hpre (ExS.seq (ExS.ite (bc := true) hcond (by simp [truthy_boolVal]) e2) e3), ?_, ?_, ?_⟩
    · rw [hp3, encode_play_drop p hS hi hd]
      simp [kbAfter, htk]
    · intro x a b c d'
      rw [ho3 x d', ho2 x d' c, hP.other x a b c]
    · refine ⟨by rw [hro3, hro2]; exact hP.ro, ⟨U2, by rw [ho3 ub (Ne.symm hpu)]; exact hu2, ?_⟩, ?_⟩
      · have hk := kbc_eq p
        refine ⟨hU2, take_of_getD _ _ 0 5 hMVl (by omega) (fun k hk5 => ?_),
          take_of_getD _ _ 8 4 (by simp [le32]) (by omega) (fun k hk4 => ?_), ?_, ?_⟩
        · rw [Nat.zero_add, hDo k (by omega) (by omega) (by omega), ub1_mv _ _ _ _ hUB hMVl k hk5]
        · rw [hDo (8 + k) (by omega) (by omega) (by omega), ub1_c _ _ _ _ hUB hMVl k hk4,
            le32_small _ (by cases p.side <;> decide)]
        · rw [hDo 14 (by omega) (by omega) (by omega), ub1_14 _ _ _ _ hUB hMVl, hk]
        · simp only [hi]; exact ⟨hD15, hD16⟩
      · have hp1 : posBlock < n := Nat.lt_of_not_le (fun hc => by
          have := hf.2.2 posBlock hc; rw [this] at hp; cases hp)
        have hu1 : ub < n := Nat.lt_of_not_le (fun hc => by
          have := hf.2.2 ub hc; rw [this] at hub; cases hub)
        exact hP.fresh.congr (by rw [ho3 0 (by decide), ho2 0 (by decide) (Ne.symm hub0)])
          (fun x hx => by rw [ho3 x (by omega), ho2 x (by omega) (by omega)])

end Shogi.C.Proofs
