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
    ∃ s, (∀ {rest o s'}, ExS Gen.prog s rest o s' →
        ExS Gen.prog ⟨frameLocals Gen.unmake_legal_probe.params [posPtr, .ptr ub 0], M, false⟩
        (.seq um0 (.seq um1 (.seq um2 (.seq um3 rest)))) o s') ∧
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
  refine ⟨{ t4 with mem := m4 }, fun h => ExS.seq (ExS.seq ea eb) (ExS.seq e1 (ExS.seq e2 (ExS.seq e3 h))), l0,
    by simp [t3, t2, s1, s0, Locals.upd]; rfl, by simp [t4, t3, t2, s1, Locals.upd], l3, rfl, hm4p,
    by show m4 n = _; rw [hm4o n hnp]; exact hm2n, by show m4 ub = _; rw [hm4o ub (Ne.symm hpu)]; exact hm2u, ?_, ?_⟩
  · have hpb : posBlock < n := Nat.lt_of_not_le (fun hc => by have := hf.2.2 posBlock hc; rw [this] at hp; cases hp)
    have hf2 : Fresh m2 (n + 1) := (hf.after_alloc _).write hn0
    exact hf2.congr (by show m4 0 = _; rw [hm4o 0 (by decide)]) (fun x hx => by
      show m4 x = _; rw [hm4o x (by omega)])
  · intro x a b d; show m4 x = _; rw [hm4o x d, hm2 x b, hm1 x a b]

theorem ev_cmp255 {s : State} {j b k : Nat} {B : List UInt8} (hl : s.locals j = some (.ptr b 0))
    (hm : s.mem b = some B) (hk : k < B.length) (op : BinOp) (hop : op = .eq ∨ op = .ne) :
    EvE Gen.prog s (.bin op (some ⟨32, true⟩) (.cast ⟨32, true⟩ (.load (.int ⟨8, false⟩) (.field (.var j) k)))
      (.const (.int ⟨32, true⟩ 255)))
      (boolVal (if op = .eq then decide ((B.getD k 0).toNat = 255) else decide ((B.getD k 0).toNat ≠ 255))) := by
  have hv := ev_blk_u8 hl hm hk
  generalize hx : (B.getD k 0).toNat = x at hv ⊢
  have hb : x < 256 := by rw [← hx]; exact UInt8.toNat_lt _
  refine EvE.bin (EvE.cast hv rfl) (EvE.const _) ?_
  rcases hop with rfl | rfl <;>
  simp [evalBin, isPtr, evalBinInt, binInt, intOf, evalCast, IntTy.modulus, IntTy.toInt, Res.bind,
    Nat.mod_eq_of_lt (show x < 4294967296 by omega), show ¬ (2147483648 ≤ x) by omega] <;>
  (have e : ((x : Int) = 255) = (x = 255) := propext (by omega)
   simp only [e])

theorem opp_ne (c : Color) : c.opp ≠ c := by cases c <;> decide

theorem kingAfter_other (p : Position) {s d : Square} {pc : Piece} (hcol : pc.color = p.side) {me : Color}
    (hme : me ≠ p.side) : kbOf (kingAfter p s d pc me) = kingByte p me := by
  unfold kingAfter
  rw [if_neg (fun h => hme (by rw [h.2, hcol]))]
  unfold kbOf kingByte; cases p.kingSquare me <;> rfl

theorem setKb_restore (p : Position) (kb kw : UInt8) (hb : p.side ≠ .black → kb = kingByte p .black)
    (hw : p.side ≠ .white → kw = kingByte p .white) :
    (setKb p.side (kingByte p p.side) kb kw).1 = kingByte p .black ∧
    (setKb p.side (kingByte p p.side) kb kw).2 = kingByte p .white := by
  cases hs : p.side
  · simp only [setKb]; exact ⟨by simp [hs], hw (by rw [hs]; decide)⟩
  · simp only [setKb]; exact ⟨hb (by rw [hs]; decide), by simp [hs]⟩

theorem toUInt8_toNat_toUInt8 (b : UInt8) : b.toNat.toUInt8 = b := by
  apply UInt8.toNat_inj.mp; simp [Nat.toUInt8, UInt8.toNat_ofNat]

/-- **`unmake_legal_probe` undoes the probe**: from `encode (p.play mv)` and the
    probe's undo record, the position block returns to `encode p`. -/
theorem unmake_spec (p : Position) (hS : p.Shaped) (hK : KingsUnique p) (mv : Move) (hm : mv ∈ p.pseudoMoves)
    {M : Mem} {ub n : Nat} {U : List UInt8}
    (hp : M posBlock = some (encode (p.play mv))) (hub : M ub = some U) (hR : UndoRec p mv U)
    (hf : Fresh M n) (h64 : n + 1 < 2 ^ 64) (hub0 : ub ≠ 0) (hpu : posBlock ≠ ub) :
    ∃ s', ExS Gen.prog ⟨frameLocals Gen.unmake_legal_probe.params [posPtr, .ptr ub 0], M, false⟩
        Gen.unmake_legal_probe.body .normal s' ∧
      s'.mem posBlock = some (encode p) ∧
      (∀ x, x ≠ 0 → x ≠ n → x ≠ posBlock → s'.mem x = M x) ∧ Fresh s'.mem (n + 1) := by
  obtain ⟨hUl, hUmv, hUc, hU14, hUx⟩ := hR
  rw [unmake_body_eq]
  have hMVl : (moveBytes p mv).length = 5 := by cases mv <;> rfl
  cases mv with
  | normal sq d pr =>
    obtain ⟨pc, hpc, hcol, hcap⟩ := pseudo_normal hm
    rw [encode_play_normal p hS hK hpc hcol (fun c' h => hcap _ h rfl)] at hp
    obtain ⟨s1, e1, l0, l1, l2, l3, hro, hp1, hn1, hu1, hf1, ho1⟩ := um_pre (c := p.side) (kbc := kingByte p p.side)
      hp hub hUl hUmv hUc hU14 hf h64 hub0 hpu
    have hnp : n ≠ posBlock := fun e => by
      have := hf.2.2 n (Nat.le_refl _); rw [e] at this; rw [this] at hp; cases hp
    have hnu : n ≠ ub := fun e => by rw [← e, hf.2.2 n (Nat.le_refl _)] at hub; cases hub
    have hmvb : moveBytes p (.normal sq d pr) = [sq.val.toUInt8, d.val.toUInt8, pc.code.toUInt8,
        if pr then 1 else 0, 0] := by simp [moveBytes, hpc, pieceByte]
    have hsq := sq.isLt
    have hd := d.isLt
    have hpcl := piece_code_lt pc
    let P1 := enc (fun y => if y = d then some (movedPiece p.side pc pr) else if y = sq then none else p.pieceAt y)
      (handsAfter p d) p.side (setKb p.side (kingByte p p.side) (kbOf (kingAfter p sq d pc .black))
        (kbOf (kingAfter p sq d pc .white))).1 (setKb p.side (kingByte p p.side)
        (kbOf (kingAfter p sq d pc .black)) (kbOf (kingAfter p sq d pc .white))).2
    have hc := ev_cmp255 l2 hn1 (k := 0) (by rw [hMVl]; decide) .eq (Or.inl rfl)
    have hc0 : ((moveBytes p (.normal sq d pr)).getD 0 0).toNat = sq.val := by
      rw [hmvb]; simp [toNat_toUInt8_lt sq.val (by omega)]
    rw [hc0] at hc
    -- board[from] = move.piece
    have hfr := ev_blk_u8 l2 hn1 (k := 0) (by rw [hMVl]; decide)
    rw [hc0] at hfr
    have hpv := ev_blk_u8 l2 hn1 (k := 2) (by rw [hMVl]; decide)
    have hpv' : ((moveBytes p (.normal sq d pr)).getD 2 0).toNat = pc.code := by
      rw [hmvb]; simp [toNat_toUInt8_lt _ hpcl]
    rw [hpv'] at hpv
    have st1 := st_pos_u (base := 0) (P := P1) (enc_length _ _ _ _ _) l0 hp1 (t := IntTy.u8) rfl hfr (by omega) hpv hro
    let m2 := s1.mem.write posBlock (0 + sq.val) (encodeLE 1 pc.code)
    let pa2 := fun y => if y = sq then some pc else
      (if y = d then some (movedPiece p.side pc pr) else if y = sq then none else p.pieceAt y)
    have hm2p : m2 posBlock = some (enc pa2 (handsAfter p d) p.side
        (setKb p.side (kingByte p p.side) (kbOf (kingAfter p sq d pc .black)) (kbOf (kingAfter p sq d pc .white))).1
        (setKb p.side (kingByte p p.side) (kbOf (kingAfter p sq d pc .black)) (kbOf (kingAfter p sq d pc .white))).2) := by
      show (s1.mem.write posBlock (0 + sq.val) _) posBlock = _
      rw [Nat.zero_add, write1_set hp1 (by rw [enc_length]; omega)]
      have := enc_set_board (fun y => if y = d then some (movedPiece p.side pc pr) else if y = sq then none
        else p.pieceAt y) (handsAfter p d) p.side
        (setKb p.side (kingByte p p.side) (kbOf (kingAfter p sq d pc .black)) (kbOf (kingAfter p sq d pc .white))).1
        (setKb p.side (kingByte p p.side) (kbOf (kingAfter p sq d pc .black)) (kbOf (kingAfter p sq d pc .white))).2
        sq (some pc)
      simp only [pieceByte] at this; exact congrArg some this
    have hm2o : ∀ x, x ≠ posBlock → m2 x = s1.mem x := fun x hx => Mem.write_ne hx
    let t2 : State := { s1 with mem := m2 }
    -- board[to] = undo->captured_piece
    have hto := ev_blk_u8 (s := t2) l2 (by show m2 n = _; rw [hm2o n hnp]; exact hn1) (k := 1) (by rw [hMVl]; decide)
    have hto' : ((moveBytes p (.normal sq d pr)).getD 1 0).toNat = d.val := by
      rw [hmvb]; simp [toNat_toUInt8_lt d.val (by omega)]
    rw [hto'] at hto
    have hu2 : t2.mem ub = some U := by show m2 ub = _; rw [hm2o ub (Ne.symm hpu)]; exact hu1
    have hcp := ev_blk_u8 (s := t2) l1 hu2 (k := 13) (by omega)
    obtain ⟨h13, h1516⟩ := hUx
    rw [h13] at hcp
    have st2 := st_pos_u (s := t2) (base := 0) (enc_length _ _ _ _ _) l0 hm2p (t := IntTy.u8) rfl hto (by omega)
      hcp hro
    let m3 := m2.write posBlock (0 + d.val) (encodeLE 1 (pieceByte (p.pieceAt d)).toNat)
    let pa3 := fun y => if y = d then p.pieceAt d else pa2 y
    have hm3p : m3 posBlock = some (enc pa3 (handsAfter p d) p.side
        (setKb p.side (kingByte p p.side) (kbOf (kingAfter p sq d pc .black)) (kbOf (kingAfter p sq d pc .white))).1
        (setKb p.side (kingByte p p.side) (kbOf (kingAfter p sq d pc .black)) (kbOf (kingAfter p sq d pc .white))).2) := by
      show (m2.write posBlock (0 + d.val) _) posBlock = _
      rw [Nat.zero_add, write1_set hm2p (by rw [enc_length]; omega), toUInt8_toNat_toUInt8]
      exact congrArg some (enc_set_board _ _ _ _ _ d _)
    have hm3o : ∀ x, x ≠ posBlock → m3 x = s1.mem x := fun x hx => by
      show (m2.write posBlock _ _) x = _; rw [Mem.write_ne hx, hm2o x hx]
    let t3 : State := { s1 with mem := m3 }
    have e4 : ExS Gen.prog s1 um4 .normal t3 :=
      ExS.ite (bc := false) hc (by simp [truthy_boolVal]; omega) (ExS.seq st1 st2)
    have hu3 : t3.mem ub = some U := by show m3 ub = _; rw [hm3o ub (Ne.symm hpu)]; exact hu1
    have hc5 := ev_cmp255 (s := t3) l1 hu3 (k := 15) (by omega) .ne (Or.inr rfl)
    have hpa3 : ∀ y, pa3 y = p.pieceAt y := fun y => by
      simp only [pa3, pa2]
      by_cases e1 : y = d
      · simp [e1]
      · by_cases e2 : y = sq
        · subst e2; simp [e1, hpc]
        · simp [e1, e2]
    have hkb := setKb_restore p (kbOf (kingAfter p sq d pc .black)) (kbOf (kingAfter p sq d pc .white))
      (fun h => kingAfter_other p hcol (Ne.symm h)) (fun h => kingAfter_other p hcol (Ne.symm h))
    obtain ⟨t4, e5, hm4p, hm4o⟩ : ∃ t4, ExS Gen.prog t3 um5 .normal t4 ∧ t4.mem posBlock = some (encode p) ∧
        (∀ x, x ≠ posBlock → t4.mem x = t3.mem x) := by
      rw [encode_enc]
      cases hq : p.pieceAt d with
      | none =>
        simp only [hq] at h1516
        refine ⟨t3, ExS.ite (bc := false) hc5 (by rw [h1516]; rfl) ExS.skip, ?_, fun _ _ => rfl⟩
        show m3 posBlock = _; rw [hm3p]
        congr 1; apply enc_congr hpa3 (fun c i => by simp [handsAfter, hq]) hkb.1 hkb.2
      | some q =>
        obtain ⟨i, hi⟩ := unpromote_hand q.type (hcap q hq)
        simp only [hq, hi] at h1516
        have hi7 := i.isLt
        have hv15 := ev_blk_u8 (s := t3) l1 hu3 (k := 15) (by omega)
        rw [h1516.1, toNat_toUInt8_lt _ (by omega)] at hv15
        have hv16 := ev_blk_u8 (s := t3) l1 hu3 (k := 16) (by omega)
        rw [h1516.2] at hv16
        have st := st_hand_e (s := t3) (c := p.side) (enc_length _ _ _ _ _) l0 hm3p l3 hi7 hv15 hv16 hro
        refine ⟨_, ExS.ite (bc := true) hc5 (by
          rw [h1516.1, toNat_toUInt8_lt _ (show i.val < 256 by omega)]
          simp only [show BinOp.ne ≠ BinOp.eq by decide, ite_false, truthy_boolVal]
          simp; omega) st, ?_, fun x hx => Mem.write_ne hx⟩
        show (m3.write posBlock _ _) posBlock = _
        have hsi : p.side.idx < 2 := by cases p.side <;> decide
        rw [write1_set hm3p (by rw [enc_length]; omega), toUInt8_toNat_toUInt8, enc_set_hand]
        congr 1; apply enc_congr hpa3 (fun c j => ?_) hkb.1 hkb.2
        simp only [hupd, handsAfter, hq, hi]
        by_cases e : c = p.side ∧ j = i
        · rw [if_pos e]; obtain ⟨rfl, rfl⟩ := e; rfl
        · rw [if_neg e, if_neg e]
    refine ⟨t4, e1 (ExS.seq e4 e5), hm4p, ?_, ?_⟩
    · intro x a b c; rw [hm4o x c]; show m3 x = _; rw [hm3o x c, ho1 x a b c]
    · have hpb : posBlock < n := Nat.lt_of_not_le (fun hc => by have := hf.2.2 posBlock hc; rw [this] at hp; cases hp)
      exact hf1.congr (by rw [hm4o 0 (by decide)]; show m3 0 = _; rw [hm3o 0 (by decide)])
        (fun x hx => by rw [hm4o x (by omega)]; show m3 x = _; rw [hm3o x (by omega)])
  | drop t d =>
    obtain ⟨i, hi, hh, hd0⟩ := pseudo_drop hm
    rw [encode_play_drop p hS hi hd0] at hp
    obtain ⟨s1, e1, l0, l1, l2, l3, hro, hp1, hn1, hu1, hf1, ho1⟩ := um_pre (c := p.side) (kbc := kingByte p p.side)
      hp hub hUl hUmv hUc hU14 hf h64 hub0 hpu
    have hnp : n ≠ posBlock := fun e => by
      have := hf.2.2 n (Nat.le_refl _); rw [e] at this; rw [this] at hp; cases hp
    have hd := d.isLt
    have hi7 := i.isLt
    have hkb := setKb_restore p (kingByte p .black) (kingByte p .white) (fun _ => rfl) (fun _ => rfl)
    let kb1 := (setKb p.side (kingByte p p.side) (kingByte p .black) (kingByte p .white)).1
    let kw1 := (setKb p.side (kingByte p p.side) (kingByte p .black) (kingByte p .white)).2
    let pa1 := fun y => if y = d then some (⟨p.side, t⟩ : Piece) else p.pieceAt y
    let h1 := hupd p.hand p.side i (p.hand p.side i - 1)
    have hc := ev_cmp255 l2 hn1 (k := 0) (by rw [hMVl]; decide) .eq (Or.inl rfl)
    have hc0 : ((moveBytes p (.drop t d)).getD 0 0).toNat = 255 := rfl
    rw [hc0] at hc
    have hto := ev_blk_u8 l2 hn1 (k := 1) (by rw [hMVl]; decide)
    have hto' : ((moveBytes p (.drop t d)).getD 1 0).toNat = d.val := by
      simp [moveBytes, toNat_toUInt8_lt d.val (by omega)]
    rw [hto'] at hto
    have st := st_pos_u (base := 0) (P := enc pa1 h1 p.side kb1 kw1) (enc_length _ _ _ _ _) l0 hp1 (t := IntTy.u8) rfl
      hto (by omega) (ev := .cast ⟨8, false⟩ (.const (.int ⟨32, true⟩ 0))) (v := 0) (EvE_of_eval (n := 3) (by rfl)) hro
    let m2 := s1.mem.write posBlock (0 + d.val) (encodeLE 1 0)
    let pa2 := fun y => if y = d then (none : Option Piece) else pa1 y
    have hm2p : m2 posBlock = some (enc pa2 h1 p.side kb1 kw1) := by
      show (s1.mem.write posBlock (0 + d.val) _) posBlock = _
      rw [Nat.zero_add, write1_set hp1 (by rw [enc_length]; omega)]
      have := enc_set_board pa1 h1 p.side kb1 kw1 d none
      simp only [pieceByte] at this; exact congrArg some this
    have hm2o : ∀ x, x ≠ posBlock → m2 x = s1.mem x := fun x hx => Mem.write_ne hx
    let t2 : State := { s1 with mem := m2 }
    have e4 : ExS Gen.prog s1 um4 .normal t2 := ExS.ite (bc := true) hc (by simp [truthy_boolVal]) st
    have hu2 : t2.mem ub = some U := by show m2 ub = _; rw [hm2o ub (Ne.symm hpu)]; exact hu1
    simp only [hi] at hUx
    have hc5 := ev_cmp255 (s := t2) l1 hu2 (k := 15) (by omega) .ne (Or.inr rfl)
    have hv15 := ev_blk_u8 (s := t2) l1 hu2 (k := 15) (by omega)
    rw [hUx.1, toNat_toUInt8_lt _ (by omega)] at hv15
    have hv16 := ev_blk_u8 (s := t2) l1 hu2 (k := 16) (by omega)
    rw [hUx.2] at hv16
    have st5 := st_hand_e (s := t2) (c := p.side) (enc_length _ _ _ _ _) l0 hm2p l3 hi7 hv15 hv16 hro
    have hsi : p.side.idx < 2 := by cases p.side <;> decide
    refine ⟨_, e1 (ExS.seq e4 (ExS.ite (bc := true) hc5 (by
          rw [hUx.1, toNat_toUInt8_lt _ (show i.val < 256 by omega)]
          simp only [show BinOp.ne ≠ BinOp.eq by decide, ite_false, truthy_boolVal]
          simp; omega) st5)), ?_, ?_, ?_⟩
    · show (m2.write posBlock _ _) posBlock = _
      rw [write1_set hm2p (by rw [enc_length]; omega), toUInt8_toNat_toUInt8, enc_set_hand, encode_enc]
      congr 1
      apply enc_congr (fun y => ?_) (fun c j => ?_) hkb.1 hkb.2
      · simp only [pa2, pa1]; by_cases e : y = d
        · subst e; simp [hd0]
        · simp [e]
      · simp only [hupd, h1]
        by_cases e : c = p.side ∧ j = i
        · rw [if_pos e]; obtain ⟨rfl, rfl⟩ := e; rfl
        · rw [if_neg e, if_neg e]
    · intro x a b c; show (m2.write posBlock _ _) x = _; rw [Mem.write_ne c, hm2o x c, ho1 x a b c]
    · have hpb : posBlock < n := Nat.lt_of_not_le (fun hc => by have := hf.2.2 posBlock hc; rw [this] at hp; cases hp)
      exact hf1.congr (by show (m2.write posBlock _ _) 0 = _; rw [Mem.write_ne (by decide), hm2o 0 (by decide)])
        (fun x hx => by show (m2.write posBlock _ _) x = _; rw [Mem.write_ne (by omega), hm2o x (by omega)])

/-- Probe then unprobe: the position block is `encode (p.play mv)` in between
    and `encode p` again afterwards. -/
theorem probe_roundtrip (p : Position) (hS : p.Shaped) (hK : KingsUnique p) (mv : Move) (hm : mv ∈ p.pseudoMoves)
    {M : Mem} {mvb ub n : Nat} {UB : List UInt8}
    (hp : M posBlock = some (encode p)) (hmv : M mvb = some (moveBytes p mv)) (hub : M ub = some UB)
    (hUB : UB.length = 20) (hf : Fresh M n) (h64 : n + 2 < 2 ^ 64)
    (hmvb0 : mvb ≠ 0) (hub0 : ub ≠ 0) (hpu : posBlock ≠ ub) :
    ∃ s1 s2, ExS Gen.prog ⟨frameLocals Gen.make_legal_probe.params [posPtr, .ptr mvb 0, .ptr ub 0], M, false⟩
        Gen.make_legal_probe.body .normal s1 ∧ s1.mem posBlock = some (encode (p.play mv)) ∧
      ExS Gen.prog ⟨frameLocals Gen.unmake_legal_probe.params [posPtr, .ptr ub 0], s1.mem, false⟩
        Gen.unmake_legal_probe.body .normal s2 ∧ s2.mem posBlock = some (encode p) := by
  obtain ⟨s1, e1, hp1, _, _, ⟨U, hU, hR⟩, hf1⟩ := make_probe_spec p hS hK mv hm hp hmv hub hUB hf (by omega)
    hmvb0 hub0 hpu
  obtain ⟨s2, e2, hp2, _, _⟩ := unmake_spec p hS hK mv hm hp1 hU hR hf1 (by omega) hub0 hpu
  exact ⟨s1, s2, e1, hp1, e2, hp2⟩

end Shogi.C.Proofs
