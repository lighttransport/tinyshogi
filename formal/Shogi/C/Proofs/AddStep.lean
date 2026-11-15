/-
  T7 generators, layer 2: `add_step` emits the moves of one step offset
  (none off the board, onto an own piece or onto a king).
-/
import Shogi.C.Proofs.AddNormal
import Shogi.C.Proofs.Pure

namespace Shogi.C.Proofs
open MiniC Shogi Shogi.C

theorem toInt_wrap32 (z : Int) (h1 : -2147483648 ≤ z) (h2 : z < 2147483648) :
    IntTy.toInt ⟨32, true⟩ (IntTy.wrap ⟨32, true⟩ z) = z := by
  simp only [IntTy.toInt, IntTy.wrap, IntTy.modulus, show (2:Nat)^32 = 4294967296 from rfl,
    show (2:Nat)^(32-1) = 2147483648 from rfl]
  have h3 : 0 ≤ z % (4294967296 : Int) := Int.emod_nonneg _ (by decide)
  have h4 : ((z % (4294967296 : Int)).toNat : Int) = z % (4294967296 : Int) := Int.toNat_of_nonneg h3
  split <;> rename_i h <;> simp only [true_and] at h <;> omega

theorem add_i32 (a b : Int) (h1 : -2147483648 ≤ a + b) (h2 : a + b < 2147483648)
    (ha1 : -2147483648 ≤ a) (ha2 : a < 2147483648) (hb1 : -2147483648 ≤ b) (hb2 : b < 2147483648) :
    evalBin .add (some ⟨32, true⟩) (i32 a) (i32 b) = .ok (i32 (a + b)) := by
  simp [evalBin, isPtr, evalBinInt, binInt, intOf, i32, IntTy.i32, Res.bind, arith,
    toInt_wrap32 a ha1 ha2, toInt_wrap32 b hb1 hb2, IntTy.inRange, IntTy.minVal, IntTy.maxVal]
  omega

theorem wrap_nat32 (k : Nat) (h : k < 2147483648) : IntTy.wrap ⟨32, true⟩ (k : Int) = k := by
  simp only [IntTy.wrap, IntTy.modulus, show (2:Nat)^32 = 4294967296 from rfl]
  omega

theorem call_pure {s : State} {d f : Nat} {fn : Func} {e : Expr} {args : List Expr} {vs : List Val} {v : Val}
    (hf : Gen.prog f = some fn) (hb : fn.body = .ret (some e)) (hp : pureE e = true)
    (hlen : fn.params.length = vs.length) (hrun : run f vs = some (some v))
    (hargs : EvArgs Gen.prog s args vs) :
    ExS Gen.prog s (.call (some d) f args) .normal { s with locals := s.locals.upd d v } :=
  ExS.call_dst (s' := ⟨frameLocals fn.params vs, s.mem, s.ro⟩) hargs hf hlen (pure_ret hf hb hp hlen hrun s.mem s.ro)

theorem load_i32_field {s : State} {j b o i : Nat} {blk : Block}
    (hj : s.locals j = some (.ptr b o)) (hb : s.mem b = some blk) (hi : o + i + 4 ≤ blk.length) :
    EvE Gen.prog s (.load (.int ⟨32, true⟩) (.field (.var j) i))
      (.int ⟨32, true⟩ (decodeLE ((blk.drop (o + i)).take 4))) := by
  refine EvE.load (pa := .ptr b (o + i)) (EvE.field (EvE.var hj) (by simp [ptrAddN, hb]; omega)) ?_
  simp only [load, readBytes, hb, Ty.size, IntTy.bytes, show o + i + 32 / 8 ≤ blk.length by omega, ite_true]
  rfl

theorem decode_le32 (k : Nat) (h : k < 2 ^ 32) : decodeLE (le32 k) = k := by
  simp [le32, decodeLE]; omega

theorem src_row (fr pc : Nat) (c : Color) (t : PieceType) (row col : Nat) (cp iz : Bool) :
    decodeLE (((srcBytes fr pc c t row col cp iz).drop (0 + 12)).take 4) = decodeLE (le32 row) := by
  simp [srcBytes, le32]

theorem src_col (fr pc : Nat) (c : Color) (t : PieceType) (row col : Nat) (cp iz : Bool) :
    decodeLE (((srcBytes fr pc c t row col cp iz).drop (0 + 16)).take 4) = decodeLE (le32 col) := by
  simp [srcBytes, le32]

/-- What `add_step` offers, from the source square `(row, col)`. -/
def stepOut (p : Position) (c : Color) (t : PieceType) (fr pc row col : Nat) (cp iz : Bool)
    (dr dc : Int) : List (List UInt8) :=
  match Square.mk? (row + dr) (col + dc) with
  | none => []
  | some d =>
    match p.pieceAt d with
    | some q => if q.color == c || q.type == .king then [] else (promoC c t d.row cp iz).map (nmBytes fr d.val pc)
    | none => (promoC c t d.row cp iz).map (nmBytes fr d.val pc)

theorem i32_nat (k : Nat) (h : k < 2147483648) : i32 (k : Int) = .int IntTy.i32 k := by
  simp [i32, IntTy.i32, wrap_nat32 k h]

theorem byte_color (q : Piece) : q.code / 16 % 2 = q.color.idx := by
  obtain ⟨c, t⟩ := q; cases c <;> cases t <;> rfl

theorem byte_type (q : Piece) : q.code % 16 = q.type.code := by
  obtain ⟨c, t⟩ := q; cases c <;> cases t <;> rfl

theorem piece_code_lt (q : Piece) : q.code < 256 := by
  obtain ⟨c, t⟩ := q; cases c <;> cases t <;> decide

theorem pieceByte_toNat (o : Option Piece) :
    (pieceByte o).toNat = match o with | some q => q.code | none => 0 := by
  cases o with
  | none => rfl
  | some q => simp [pieceByte, Nat.mod_eq_of_lt (piece_code_lt q)]

theorem ev_ne0 {s : State} {i b : Nat} (hb : b < 256) (h : s.locals i = some (.int IntTy.u8 b)) :
    EvE Gen.prog s (.bin .ne (some ⟨32, true⟩) (.cast ⟨32, true⟩ (.var i)) (.const (.int ⟨32, true⟩ 0)))
      (boolVal (decide (b ≠ 0))) := by
  refine EvE.bin (EvE.cast (EvE.var h) rfl) (EvE.const _) ?_
  simp [evalBin, isPtr, evalBinInt, binInt, intOf, IntTy.u8, evalCast, IntTy.modulus, IntTy.toInt, Res.bind,
    Nat.mod_eq_of_lt (show b < 4294967296 by omega), show ¬ (2147483648 ≤ b) by omega]

theorem cast_u32_var {s : State} {i a : Nat} (ha : a < 2 ^ 32) (h : s.locals i = some (.int IntTy.u32 a)) :
    EvE Gen.prog s (.cast ⟨32, false⟩ (.var i)) (.int IntTy.u32 a) :=
  EvE.cast (EvE.var h) (by simp [evalCast, IntTy.u32, IntTy.modulus, Nat.mod_eq_of_lt ha])

theorem ev_land_eq {s : State} {ea eb : Expr} {a b : Nat}
    (ha : EvE Gen.prog s ea (.int IntTy.u32 a)) (hb : EvE Gen.prog s eb (.int IntTy.u32 b)) :
    EvE Gen.prog s (.land (.const (.int ⟨32, true⟩ 1)) (.bin .eq (some ⟨32, false⟩) ea eb))
      (boolVal (decide (a = b))) :=
  EvE.land_true (EvE.const _) rfl (EvE.bin ha hb (by simp [evalBin, isPtr, evalBinInt, binInt, intOf,
    IntTy.u32, Res.bind])) (truthy_boolVal _)

/-- Pieces of `add_step`'s body (verbatim from `Gen`). -/
def stepSq : Stmt := (.seq (.call (some 11) 10 [(.var 7), (.var 8)]) (.set 10 (.var 11)))
def stepLoad : Stmt := (.set 12 (.load (.int ⟨8, false⟩) (.index (.field (.var 0) 0) (.var 10) 1)))
def stepOwn : Stmt := (.seq (.ite (.bin .ne (some ⟨32, true⟩) (.cast ⟨32, true⟩ (.var 12)) (.const (.int ⟨32, true⟩ 0))) (.seq (.call (some 13) 1 [(.var 12)]) (.set 14 (.land (.const (.int ⟨32, true⟩ 1)) (.bin .eq (some ⟨32, false⟩) (.cast ⟨32, false⟩ (.var 13)) (.cast ⟨32, false⟩ (.load (.int ⟨32, false⟩) (.field (.var 1) 4))))))) (.set 14 (.const (.int ⟨32, true⟩ 0)))) (.ite (.var 14) (.ret none) .skip))
def stepKing : Stmt := (.seq (.ite (.bin .ne (some ⟨32, true⟩) (.cast ⟨32, true⟩ (.var 12)) (.const (.int ⟨32, true⟩ 0))) (.seq (.call (some 15) 2 [(.var 12)]) (.set 16 (.land (.const (.int ⟨32, true⟩ 1)) (.bin .eq (some ⟨32, false⟩) (.cast ⟨32, false⟩ (.var 15)) (.cast ⟨32, false⟩ (.const (.int ⟨32, true⟩ 8))))))) (.set 16 (.const (.int ⟨32, true⟩ 0)))) (.ite (.var 16) (.ret none) .skip))
def stepCall : Stmt := (.call none 23 [(.var 1), (.var 10), (.var 7), (.var 4), (.var 5), (.var 6)])

theorem add_step_body_eq : Gen.add_step.body = .seq (.set 7 (.bin .add (some ⟨32, true⟩)
    (.load (.int ⟨32, true⟩) (.field (.var 1) 12)) (.var 2))) (.seq (.set 8 (.bin .add (some ⟨32, true⟩)
    (.load (.int ⟨32, true⟩) (.field (.var 1) 16)) (.var 3))) (.seq (.seq (.call (some 9) 9 [(.var 7), (.var 8)])
    (.ite (.un .lnot ⟨32, true⟩ (.var 9)) (.ret none) .skip))
    (.seq stepSq (.seq stepLoad (.seq stepOwn (.seq stepKing stepCall)))))) := rfl

section step
variable {p : Position} {sb fr pc mb mo cb co cap n row col : Nat} {c : Color} {t : PieceType}
  {cp iz : Bool} {L : List (List UInt8)} {m : Mem} {dr dc : Int}

theorem add_step_spec (hrow : row < 9) (hcol : col < 9) (hdr : -2 ≤ dr ∧ dr ≤ 2) (hdc : -2 ≤ dc ∧ dc ≤ 2)
    (hbuf : Buf m mb mo cb co cap L) (hf : Fresh m n) (h64 : n + 4 < 2 ^ 64)
    (hsb : m sb = some (srcBytes fr pc c t row col cp iz)) (hfr : fr < 256) (hpc : pc < 256)
    (hm : m posBlock = some (encode p))
    (hsb0 : sb ≠ 0) (hsbm : sb ≠ mb) (hsbc : sb ≠ cb) (hpm : posBlock ≠ mb) (hpc' : posBlock ≠ cb) :
    ∃ o s', ExS Gen.prog ⟨frameLocals Gen.add_step.params
        [posPtr, .ptr sb 0, i32 dr, i32 dc, .ptr mb mo, .ptr cb co, .int IntTy.u64 cap], m, false⟩
      Gen.add_step.body o s' ∧ (o = .normal ∨ o = .ret none) ∧
      Buf s'.mem mb mo cb co cap (L ++ stepOut p c t fr pc row col cp iz dr dc) ∧
      Fresh s'.mem (n + 2 * (stepOut p c t fr pc row col cp iz dr dc).length) ∧ Frame m s'.mem mb cb := by
  let s0 : State := ⟨frameLocals Gen.add_step.params
    [posPtr, .ptr sb 0, i32 dr, i32 dc, .ptr mb mo, .ptr cb co, .int IntTy.u64 cap], m, false⟩
  have l1 : s0.locals 1 = some (.ptr sb 0) := rfl
  -- to_row, to_col
  have hR : EvE Gen.prog s0 (.load (.int ⟨32, true⟩) (.field (.var 1) 12)) (i32 (row : Int)) := by
    have := load_i32_field (i := 12) l1 hsb (by simp [srcBytes_length])
    rw [src_row, decode_le32 row (by omega)] at this
    rw [i32_nat row (by omega)]; exact this
  let v7 := i32 ((row : Int) + dr)
  let v8 := i32 ((col : Int) + dc)
  let s1 : State := { s0 with locals := s0.locals.upd 7 v7 }
  have e1 : ExS Gen.prog s0 (.set 7 (.bin .add (some ⟨32, true⟩) (.load (.int ⟨32, true⟩) (.field (.var 1) 12))
      (.var 2))) .normal s1 :=
    ExS.set (EvE.bin hR (EvE.var rfl) (add_i32 _ _ (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)))
  have hC : EvE Gen.prog s1 (.load (.int ⟨32, true⟩) (.field (.var 1) 16)) (i32 (col : Int)) := by
    have := load_i32_field (s := s1) (i := 16) (show s1.locals 1 = some (.ptr sb 0) from rfl) hsb (by simp [srcBytes_length])
    rw [src_col, decode_le32 col (by omega)] at this
    rw [i32_nat col (by omega)]; exact this
  let s2 : State := { s1 with locals := s1.locals.upd 8 v8 }
  have e2 : ExS Gen.prog s1 (.set 8 (.bin .add (some ⟨32, true⟩) (.load (.int ⟨32, true⟩) (.field (.var 1) 16))
      (.var 3))) .normal s2 :=
    ExS.set (EvE.bin (s := s1) hC (EvE.var rfl)
      (add_i32 _ _ (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)))
  -- on_board
  let ob := (Square.mk? ((row : Int) + dr) ((col : Int) + dc)).isSome
  have hob : run Gen.fid_on_board [v7, v8] = some (some (bool8 ob)) := by
    have := on_board_refines ⟨((row : Int) + dr + 9).toNat, by omega⟩ ⟨((col : Int) + dc + 9).toNat, by omega⟩
    simp only at this
    rw [show (((row : Int) + dr + 9).toNat : Int) - 9 = row + dr by omega,
      show (((col : Int) + dc + 9).toNat : Int) - 9 = col + dc by omega] at this
    exact this
  let s3 : State := { s2 with locals := s2.locals.upd 9 (bool8 ob) }
  have e3 : ExS Gen.prog s2 (.call (some 9) 9 [(.var 7), (.var 8)]) .normal s3 :=
    call_pure rfl rfl rfl rfl hob (EvArgs.cons (EvE.var rfl) (EvArgs.cons (EvE.var rfl) EvArgs.nil))
  have hnot : EvE Gen.prog s3 (.un .lnot ⟨32, true⟩ (.var 9)) (boolVal (!ob)) :=
    EvE.un (va := bool8 ob) (EvE.var (by simp [s3, Locals.upd])) (by cases ob <;> rfl)
  have hhead : ∀ {o s'}, ob = true →
      ExS Gen.prog s3 (.seq stepSq (.seq stepLoad (.seq stepOwn (.seq stepKing stepCall)))) o s' →
      ExS Gen.prog s0 Gen.add_step.body o s' := by
    intro o s' hob1 h
    rw [add_step_body_eq]
    exact ExS.seq e1 (ExS.seq e2 (ExS.seq (ExS.seq e3 (ExS.ite (bc := false) hnot
      (by rw [hob1]; rfl) ExS.skip)) h))
  cases hsq : Square.mk? ((row : Int) + dr) ((col : Int) + dc) with
  | none =>
    have hobf : ob = false := by simp [ob, hsq]
    have hout : stepOut p c t fr pc row col cp iz dr dc = [] := by simp [stepOut, hsq]
    refine ⟨.ret none, s3, ?_, Or.inr rfl, ?_, ?_, Frame.refl m mb cb⟩
    · exact ExS.seq e1 (ExS.seq e2 (ExS.seq_ret (ExS.seq e3 (ExS.ite (bc := true) hnot
        (by rw [hobf]; rfl) ExS.ret_none))))
    · rw [hout, List.append_nil]; exact hbuf
    · rw [hout]; exact hf
  | some d =>
    have hobt : ob = true := by simp [ob, hsq]
    have hdv := d.isLt
    obtain ⟨hin, hdeq⟩ : (0 ≤ (row : Int) + dr ∧ (row : Int) + dr < 9 ∧ 0 ≤ (col : Int) + dc ∧
        (col : Int) + dc < 9) ∧ d.val = (((row : Int) + dr) * 9 + ((col : Int) + dc)).toNat := by
      unfold Square.mk? at hsq; split at hsq
      · next h => simp only [Option.some.injEq] at hsq; subst hsq; exact ⟨h, rfl⟩
      · cases hsq
    let R := ((row : Int) + dr).toNat
    let C := ((col : Int) + dc).toNat
    have hR9 : R < 9 := by omega
    have hC9 : C < 9 := by omega
    have hdRC : d.val = R * 9 + C := by omega
    have hdrow : d.row = R := by simp only [Square.row]; omega
    have hv7 : v7 = i32 (R : Int) := by simp only [v7]; congr 1; omega
    have hv8 : v8 = i32 (C : Int) := by simp only [v8]; congr 1; omega
    have hsqa : run Gen.fid_square_at [v7, v8] = some (some (u8 d.val)) := by
      rw [hv7, hv8, hdRC]; exact square_at_refines ⟨R, hR9⟩ ⟨C, hC9⟩
    let s4a : State := { s3 with locals := s3.locals.upd 11 (u8 d.val) }
    let s4 : State := { s4a with locals := s4a.locals.upd 10 (u8 d.val) }
    have e4 : ExS Gen.prog s3 stepSq .normal s4 :=
      ExS.seq (call_pure rfl rfl rfl rfl hsqa (EvArgs.cons (EvE.var rfl) (EvArgs.cons (EvE.var rfl) EvArgs.nil)))
        (ExS.set (EvE.var (by simp [s4a, Locals.upd])))
    -- the target square's byte
    let bt := (pieceByte (p.pieceAt d)).toNat
    have hlen : (encode p).length = 114 := by simp [encode, Gen.off_side, Gen.off_king_square, le32]
    have hrd := readBoard hm d.val hdv
    let s5 : State := { s4 with locals := s4.locals.upd 12 (.int IntTy.u8 bt) }
    have e5 : ExS Gen.prog s4 stepLoad .normal s5 := by
      refine ExS.set (EvE.load (pa := .ptr posBlock (0 + 0 + d.val * 1)) (EvE.index (pb := .ptr posBlock (0 + 0))
        (EvE.field (EvE.var (v := posPtr) rfl) (by simp [ptrAddN, posPtr, s4, s4a, s3, s2, s1, s0, hm, hlen]))
        (EvE.var (v := .int IntTy.u8 d.val) (by simp [s4, Locals.upd]; rfl)) ?_) ?_)
      · simp [IntTy.u8, ptrAddN, s4, s4a, s3, s2, s1, s0, hm, hlen]; omega
      · simp only [load, Ty.size, IntTy.bytes, show (8 : Nat) / 8 = 1 by rfl, s4, s4a, s3, s2, s1, s0]
        simp [hrd, Res.bind, decodeLE, bt]; rfl
    have hbt : bt < 256 := UInt8.toNat_lt _
    -- the final call, from any state that kept the arguments and the memory
    have hfinal : ∀ s7 : State, s7.mem = m → s7.ro = false → s7.locals 1 = some (.ptr sb 0) →
        s7.locals 10 = some (u8 d.val) → s7.locals 7 = some v7 → s7.locals 4 = some (.ptr mb mo) →
        s7.locals 5 = some (.ptr cb co) → s7.locals 6 = some (.int IntTy.u64 cap) →
        ∃ s', ExS Gen.prog s7 stepCall .normal s' ∧
          Buf s'.mem mb mo cb co cap (L ++ (promoC c t R cp iz).map (nmBytes fr d.val pc)) ∧
          Fresh s'.mem (n + 2 * (promoC c t R cp iz).length) ∧ Frame m s'.mem mb cb := by
      intro s7 hm7 hro7 a1 a10 a7 a4 a5 a6
      obtain ⟨sN, hN, hbN, hfN, hfrN, _⟩ := add_normal_move_spec (to := d.val) (r := R) hR9 hbuf hf h64 hsb hfr hpc
        (by omega) hsb0 hsbm hsbc
      refine ⟨{ s7 with mem := sN.mem }, ?_, hbN, hfN, hfrN⟩
      refine ExS.call (vs := [.ptr sb 0, .int IntTy.u8 d.val, i32 (R : Int), .ptr mb mo, .ptr cb co,
        .int IntTy.u64 cap]) ?_ rfl rfl ?_ (Or.inl rfl)
      · exact EvArgs.cons (EvE.var a1) (EvArgs.cons (EvE.var a10) (EvArgs.cons (EvE.var (by rw [a7, hv7]))
          (EvArgs.cons (EvE.var a4) (EvArgs.cons (EvE.var a5) (EvArgs.cons (EvE.var a6) EvArgs.nil)))))
      · rw [hm7, hro7]; exact hN
    have hstep : stepOut p c t fr pc row col cp iz dr dc = (match p.pieceAt d with
        | some q => if q.color == c || q.type == .king then [] else (promoC c t R cp iz).map (nmBytes fr d.val pc)
        | none => (promoC c t R cp iz).map (nmBytes fr d.val pc)) := by
      simp only [stepOut, hsq, hdrow]
    have hpre : ∀ {o s'}, ExS Gen.prog s5 (.seq stepOwn (.seq stepKing stepCall)) o s' →
        ExS Gen.prog s0 Gen.add_step.body o s' := fun h => hhead hobt (ExS.seq e4 (ExS.seq e5 h))
    have lsrc : ∀ (st : State), st.mem = m → st.locals 1 = some (.ptr sb 0) →
        EvE Gen.prog st (.cast ⟨32, false⟩ (.load (.int ⟨32, false⟩) (.field (.var 1) 4))) (.int IntTy.u32 c.idx) := by
      intro st hmst h1
      have := load_u32_field (s := st) (i := 4) h1 (by rw [hmst]; exact hsb) (by simp [srcBytes_length])
      rw [src_color] at this
      exact EvE.cast this (by have : c.idx < 2 := by cases c <;> decide
                              simp [evalCast, IntTy.u32, IntTy.modulus, Nat.mod_eq_of_lt (show c.idx < 4294967296 by omega)])
    cases hq : p.pieceAt d with
    | none =>
      have hbt0 : bt = 0 := by simp [bt, hq, pieceByte]
      have l12 : s5.locals 12 = some (.int IntTy.u8 bt) := by simp [s5, Locals.upd]
      let s6 : State := { s5 with locals := s5.locals.upd 14 (.int IntTy.i32 0) }
      have e6 : ExS Gen.prog s5 stepOwn .normal s6 :=
        ExS.seq (ExS.ite (bc := false) (ev_ne0 hbt l12) (by rw [hbt0]; rfl) (ExS.set (EvE.const _)))
          (ExS.ite (bc := false) (EvE.var (v := .int IntTy.i32 0) (by simp [s6, Locals.upd]; rfl)) rfl ExS.skip)
      let s7 : State := { s6 with locals := s6.locals.upd 16 (.int IntTy.i32 0) }
      have e7 : ExS Gen.prog s6 stepKing .normal s7 :=
        ExS.seq (ExS.ite (bc := false) (ev_ne0 hbt (by simp [s6, Locals.upd]; exact l12)) (by rw [hbt0]; rfl)
          (ExS.set (EvE.const _)))
          (ExS.ite (bc := false) (EvE.var (v := .int IntTy.i32 0) (by simp [s7, Locals.upd]; rfl)) rfl ExS.skip)
      obtain ⟨s', e8, hb', hf', hfr'⟩ := hfinal s7 rfl rfl (by simp [s7, s6, s5, s4, s4a, s3, s2, s1, Locals.upd]; rfl)
        (by simp [s7, s6, s5, s4, Locals.upd]) (by simp [s7, s6, s5, s4, s4a, s3, s2, s1, Locals.upd])
        (by simp [s7, s6, s5, s4, s4a, s3, s2, s1, Locals.upd]; rfl)
        (by simp [s7, s6, s5, s4, s4a, s3, s2, s1, Locals.upd]; rfl)
        (by simp [s7, s6, s5, s4, s4a, s3, s2, s1, Locals.upd]; rfl)
      refine ⟨.normal, s', hpre (ExS.seq e6 (ExS.seq e7 e8)), Or.inl rfl, ?_, ?_, hfr'⟩
      · rw [hstep, hq]; exact hb'
      · rw [hstep, hq]; simpa using hf'
    | some q =>
      have hbtq : bt = q.code := by simp [bt, hq, pieceByte_toNat]
      have hcode1 : q.code ≠ 0 := by obtain ⟨qc, qt⟩ := q; cases qc <;> cases qt <;> decide
      have l12 : s5.locals 12 = some (.int IntTy.u8 bt) := by simp [s5, Locals.upd]
      have hpcol : run Gen.fid_shogi_piece_color [u8 bt] = some (some (u32 q.color.idx)) := by
        have := shogi_piece_color_total ⟨bt, hbt⟩
        simp only at this; rw [this]
        have hb : bt / 16 % 2 = q.color.idx := by simp only [bt, hq, pieceByte_toNat]; exact byte_color q
        rw [hb]; obtain ⟨qc, qt⟩ := q; cases qc <;> rfl
      let own := decide (q.color.idx = c.idx)
      let s6a : State := { s5 with locals := s5.locals.upd 13 (u32 q.color.idx) }
      let s6 : State := { s6a with locals := s6a.locals.upd 14 (boolVal own) }
      have hci : q.color.idx < 2 := by cases q.color <;> decide
      have e6a : ExS Gen.prog s5 (.ite (.bin .ne (some ⟨32, true⟩) (.cast ⟨32, true⟩ (.var 12))
          (.const (.int ⟨32, true⟩ 0))) (.seq (.call (some 13) 1 [(.var 12)]) (.set 14 (.land
          (.const (.int ⟨32, true⟩ 1)) (.bin .eq (some ⟨32, false⟩) (.cast ⟨32, false⟩ (.var 13))
          (.cast ⟨32, false⟩ (.load (.int ⟨32, false⟩) (.field (.var 1) 4))))))) (.set 14 (.const
          (.int ⟨32, true⟩ 0)))) .normal s6 :=
        ExS.ite (bc := true) (ev_ne0 hbt l12) (by simp [truthy_boolVal, hbtq, hcode1])
          (ExS.seq (call_pure rfl rfl rfl rfl hpcol (EvArgs.cons (EvE.var l12) EvArgs.nil))
            (ExS.set (ev_land_eq (cast_u32_var (by omega) (by simp [s6a, Locals.upd]; rfl))
              (lsrc s6a rfl (by simp [s6a, s5, s4, s4a, s3, s2, s1, Locals.upd]; rfl)))))
      have l14 : s6.locals 14 = some (boolVal own) := by simp [s6, Locals.upd]
      cases hown : own
      · -- not an own piece: the king test
        have hneq : (q.color == c) = false := by
          have : ¬ q.color.idx = c.idx := by simpa [own] using hown
          cases hqc : q.color <;> cases c <;> simp_all [Color.idx]
        have l12' : s6.locals 12 = some (.int IntTy.u8 bt) := by simp [s6, s6a, Locals.upd]; exact l12
        have hptyp : run Gen.fid_shogi_piece_type [u8 bt] = some (some (u32 q.type.code)) := by
          have := shogi_piece_type_total ⟨bt, hbt⟩
          simp only at this; rw [this]
          have hb : bt % 16 = q.type.code := by simp only [bt, hq, pieceByte_toNat]; exact byte_type q
          rw [hb]
        have htc : q.type.code < 16 := by cases q.type <;> decide
        let kg := decide (q.type.code = 8)
        let s7a : State := { s6 with locals := s6.locals.upd 15 (u32 q.type.code) }
        let s7 : State := { s7a with locals := s7a.locals.upd 16 (boolVal kg) }
        have e7a : ExS Gen.prog s6 (.ite (.bin .ne (some ⟨32, true⟩) (.cast ⟨32, true⟩ (.var 12))
            (.const (.int ⟨32, true⟩ 0))) (.seq (.call (some 15) 2 [(.var 12)]) (.set 16 (.land
            (.const (.int ⟨32, true⟩ 1)) (.bin .eq (some ⟨32, false⟩) (.cast ⟨32, false⟩ (.var 15))
            (.cast ⟨32, false⟩ (.const (.int ⟨32, true⟩ 8))))))) (.set 16 (.const (.int ⟨32, true⟩ 0))))
            .normal s7 :=
          ExS.ite (bc := true) (ev_ne0 hbt l12') (by simp [truthy_boolVal, hbtq, hcode1])
            (ExS.seq (call_pure rfl rfl rfl rfl hptyp (EvArgs.cons (EvE.var l12') EvArgs.nil))
              (ExS.set (ev_land_eq (cast_u32_var (by omega) (by simp [s7a, Locals.upd]; rfl))
                (EvE.cast (EvE.const _) rfl))))
        have l16 : s7.locals 16 = some (boolVal kg) := by simp [s7, Locals.upd]
        have e6 : ExS Gen.prog s5 stepOwn .normal s6 :=
          ExS.seq e6a (ExS.ite (bc := false) (EvE.var l14) (by rw [hown]; rfl) ExS.skip)
        cases hkg : kg
        · have hnk : (q.type == PieceType.king) = false := by
            have : ¬ q.type.code = 8 := by simpa [kg] using hkg
            cases hqt : q.type <;> simp_all [PieceType.code]
          have e7 : ExS Gen.prog s6 stepKing .normal s7 :=
            ExS.seq e7a (ExS.ite (bc := false) (EvE.var l16) (by rw [hkg]; rfl) ExS.skip)
          obtain ⟨s', e8, hb', hf', hfr'⟩ := hfinal s7 rfl rfl
            (by simp [s7, s7a, s6, s6a, s5, s4, s4a, s3, s2, s1, Locals.upd]; rfl)
            (by simp [s7, s7a, s6, s6a, s5, s4, Locals.upd])
            (by simp [s7, s7a, s6, s6a, s5, s4, s4a, s3, s2, s1, Locals.upd])
            (by simp [s7, s7a, s6, s6a, s5, s4, s4a, s3, s2, s1, Locals.upd]; rfl)
            (by simp [s7, s7a, s6, s6a, s5, s4, s4a, s3, s2, s1, Locals.upd]; rfl)
            (by simp [s7, s7a, s6, s6a, s5, s4, s4a, s3, s2, s1, Locals.upd]; rfl)
          refine ⟨.normal, s', hpre (ExS.seq e6 (ExS.seq e7 e8)), Or.inl rfl, ?_, ?_, hfr'⟩
          · rw [hstep, hq]; simpa [hneq, hnk] using hb'
          · rw [hstep, hq]; simpa [hneq, hnk] using hf'
        · have hk : (q.type == PieceType.king) = true := by
            have : q.type.code = 8 := by simpa [kg] using hkg
            cases hqt : q.type <;> simp_all [PieceType.code]
          have e7 : ExS Gen.prog s6 stepKing (.ret none) s7 :=
            ExS.seq e7a (ExS.ite (bc := true) (EvE.var l16) (by rw [hkg]; rfl) ExS.ret_none)
          refine ⟨.ret none, s7, hpre (ExS.seq e6 (ExS.seq_ret e7)), Or.inr rfl, ?_, ?_, Frame.refl m mb cb⟩
          · rw [hstep, hq]; simpa [hk] using hbuf
          · rw [hstep, hq]; simpa [hk] using hf
      · have hown' : (q.color == c) = true := by
          have : q.color.idx = c.idx := by simpa [own] using hown
          cases hqc : q.color <;> cases c <;> simp_all [Color.idx]
        have e6 : ExS Gen.prog s5 stepOwn (.ret none) s6 :=
          ExS.seq e6a (ExS.ite (bc := true) (EvE.var l14) (by rw [hown]; rfl) ExS.ret_none)
        refine ⟨.ret none, s6, hpre (ExS.seq_ret e6), Or.inr rfl, ?_, ?_, Frame.refl m mb cb⟩
        · rw [hstep, hq]; simpa [hown'] using hbuf
        · rw [hstep, hq]; simpa [hown'] using hf
end step

end Shogi.C.Proofs
