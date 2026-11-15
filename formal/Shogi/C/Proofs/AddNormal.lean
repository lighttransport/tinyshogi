/-
  T7 generators, layer 1: `add_normal_move` emits a board move with the
  spec's promotion choices (`promoChoices`).
-/
import Shogi.C.Proofs.AddMove
import Shogi.C.Proofs.Helpers

namespace Shogi.C.Proofs
open MiniC Shogi Shogi.C

/-- Bytes of a `MoveSource` local (24 bytes, as the generator stores them). -/
def srcBytes (fr pc : Nat) (c : Color) (t : PieceType) (row col : Nat) (cp iz : Bool) : List UInt8 :=
  [fr.toUInt8, pc.toUInt8, 0, 0] ++ le32 c.idx ++ le32 t.code ++ le32 row ++ le32 col ++
    [if cp then 1 else 0, if iz then 1 else 0, 0, 0]

/-- The 5 bytes of a board move `{from, to, piece, promote, 0}`. -/
def nmBytes (fr to pc : Nat) (pr : Bool) : List UInt8 :=
  [fr.toUInt8, to.toUInt8, pc.toUInt8, if pr then 1 else 0, 0]

theorem store_u8_field {s : State} {j b o i v : Nat} {e : Expr} {blk : Block}
    (hj : s.locals j = some (.ptr b o)) (hb : s.mem b = some blk) (hi : o + i + 1 ≤ blk.length)
    (he : EvE Gen.prog s e (.int IntTy.u8 v)) (hro : s.ro = false) :
    ExS Gen.prog s (.store (.int ⟨8, false⟩) (.field (.var j) i) e) .normal
      { s with mem := s.mem.write b (o + i) (encodeLE 1 v) } :=
  ExS.store (pa := .ptr b (o + i)) (EvE.field (EvE.var hj) (by simp [ptrAddN, hb]; omega)) he hro
    (by simp only [store, IntTy.u8, IntTy.bytes, ite_true]; exact writeBytes_ok hb (by simp [encodeLE]; omega))

theorem load_u8_field {s : State} {j b o i : Nat} {blk : Block}
    (hj : s.locals j = some (.ptr b o)) (hb : s.mem b = some blk) (hi : o + i + 1 ≤ blk.length) :
    EvE Gen.prog s (.load (.int ⟨8, false⟩) (.field (.var j) i)) (.int IntTy.u8 (blk.getD (o + i) 0).toNat) := by
  refine EvE.load (pa := .ptr b (o + i)) (EvE.field (EvE.var hj) (by simp [ptrAddN, hb]; omega)) ?_
  simp only [load, readBytes, hb, Ty.size, IntTy.bytes, show o + i + 8 / 8 ≤ blk.length by omega, ite_true]
  rw [List.take_one, List.head?_drop]
  simp [List.getD, show o + i < blk.length by omega, decodeLE, Res.bind]; rfl

/-- One `ShogiMove` compound literal followed by `add_move`. -/
def emitStmt (j pr : Nat) : Stmt :=
  .seq (.alloc j 5) (.seq (.store (.int ⟨8, false⟩) (.field (.var j) 0) (.load (.int ⟨8, false⟩) (.field (.var 0) 0)))
    (.seq (.store (.int ⟨8, false⟩) (.field (.var j) 1) (.var 1))
    (.seq (.store (.int ⟨8, false⟩) (.field (.var j) 2) (.load (.int ⟨8, false⟩) (.field (.var 0) 1)))
    (.seq (.store (.int ⟨8, false⟩) (.field (.var j) 3) (.cast ⟨8, false⟩ (.const (.int ⟨32, true⟩ pr))))
    (.seq (.store (.int ⟨8, false⟩) (.field (.var j) 4) (.cast ⟨8, false⟩ (.const (.int ⟨32, true⟩ 0))))
      (.call none 22 [(.var 3), (.var 4), (.var 5), (.var j)]))))))

theorem srcBytes_length (fr pc : Nat) (c : Color) (t : PieceType) (row col : Nat) (cp iz : Bool) :
    (srcBytes fr pc c t row col cp iz).length = 24 := by simp [srcBytes, le32]

section emit
variable {s : State} {sb fr pc to mb mo cb co cap n : Nat} {c : Color} {t : PieceType}
  {row col : Nat} {cp iz : Bool} {L : List (List UInt8)}

theorem emit_spec (j : Nat) (pr : Bool) (hj : j ≠ 0 ∧ j ≠ 1 ∧ j ≠ 3 ∧ j ≠ 4 ∧ j ≠ 5)
    (h0 : s.locals 0 = some (.ptr sb 0)) (h1 : s.locals 1 = some (.int IntTy.u8 to))
    (h3 : s.locals 3 = some (.ptr mb mo)) (h4 : s.locals 4 = some (.ptr cb co))
    (h5 : s.locals 5 = some (.int IntTy.u64 cap)) (hro : s.ro = false)
    (hsb : s.mem sb = some (srcBytes fr pc c t row col cp iz)) (hfr : fr < 256) (hpc : pc < 256)
    (hto : to < 256) (hbuf : Buf s.mem mb mo cb co cap L) (hf : Fresh s.mem n) (h64 : n + 2 < 2 ^ 64)
    (hsb0 : sb ≠ 0) (hsbm : sb ≠ mb) (hsbc : sb ≠ cb) :
    ∃ s', ExS Gen.prog s (emitStmt j (if pr then 1 else 0)) .normal s' ∧
      s'.locals = s.locals.upd j (.ptr n 0) ∧ s'.ro = s.ro ∧
      Buf s'.mem mb mo cb co cap (L ++ [nmBytes fr to pc pr]) ∧ Fresh s'.mem (n + 1 + 1) ∧
      Frame s.mem s'.mem mb cb ∧ s'.mem sb = s.mem sb := by
  obtain ⟨j0, j1, j3, j4, j5⟩ := hj
  have hsbn : sb ≠ n := fun e => by rw [e, hf.2.2 n (Nat.le_refl _)] at hsb; cases hsb
  let m1 := (s.mem.upd 0 (encodeLE 8 (n + 1))).upd n (List.replicate 5 0)
  let s1 : State := { s with mem := m1, locals := s.locals.upd j (.ptr n 0) }
  have ha : ExS Gen.prog s (.alloc j 5) .normal s1 := exec_alloc (hf.allocAt (by omega)) j 5
  have hj' : ∀ x, x ≠ j → s1.locals x = s.locals x := fun x hx => by simp [s1, Locals.upd, hx]
  have hjj : s1.locals j = some (.ptr n 0) := by simp [s1, Locals.upd]
  have hm1sb : m1 sb = s.mem sb := by simp only [m1]; rw [Mem.upd_ne hsbn, Mem.upd_ne hsb0]
  have hld0 : ∀ (st : State), st.locals 0 = some (.ptr sb 0) →
      st.mem sb = some (srcBytes fr pc c t row col cp iz) →
      EvE Gen.prog st (.load (.int ⟨8, false⟩) (.field (.var 0) 0)) (.int IntTy.u8 fr) := by
    intro st hl hm
    have := load_u8_field (i := 0) hl hm (by simp [srcBytes_length])
    simpa [srcBytes, Nat.mod_eq_of_lt hfr] using this
  have hld1 : ∀ (st : State), st.locals 0 = some (.ptr sb 0) →
      st.mem sb = some (srcBytes fr pc c t row col cp iz) →
      EvE Gen.prog st (.load (.int ⟨8, false⟩) (.field (.var 0) 1)) (.int IntTy.u8 pc) := by
    intro st hl hm
    have := load_u8_field (i := 1) hl hm (by simp [srcBytes_length])
    simpa [srcBytes, Nat.mod_eq_of_lt hpc] using this
  have hmbn : mb ≠ n := fun e => by
    obtain ⟨blk, hb, _⟩ := hbuf.buf; rw [e, hf.2.2 n (Nat.le_refl _)] at hb; cases hb
  have hcbn : cb ≠ n := fun e => by
    obtain ⟨blk, hb, _⟩ := hbuf.cnt; rw [e, hf.2.2 n (Nat.le_refl _)] at hb; cases hb
  have hm1n : m1 n = some (List.replicate 5 0) := Mem.upd_eq
  have hm1o : ∀ x, x ≠ 0 → x ≠ n → m1 x = s.mem x := fun x a b => by
    simp only [m1]; rw [Mem.upd_ne b, Mem.upd_ne a]
  let prb : Nat := if pr then 1 else 0
  have hprb : prb < 256 := by simp only [prb]; split <;> omega
  -- the five field stores
  let m2 := m1.write n (0 + 0) (encodeLE 1 fr)
  let m3 := m2.write n (0 + 1) (encodeLE 1 to)
  let m4 := m3.write n (0 + 2) (encodeLE 1 pc)
  let m5 := m4.write n (0 + 3) (encodeLE 1 prb)
  let m6 := m5.write n (0 + 4) (encodeLE 1 0)
  have hw : ∀ (mm : Mem) (o v : Nat), mm n ≠ none → (mm.write n o (encodeLE 1 v)) sb = mm sb ∧
      ∀ x, x ≠ n → (mm.write n o (encodeLE 1 v)) x = mm x := fun mm o v _ =>
    ⟨Mem.write_ne hsbn, fun x hx => Mem.write_ne hx⟩
  have hm2n : m2 n = some [fr.toUInt8, 0, 0, 0, 0] := by
    simp only [m2]; rw [Mem.write_eq hm1n]; simp [encodeLE, Nat.mod_eq_of_lt hfr]
  have hm3n : m3 n = some [fr.toUInt8, to.toUInt8, 0, 0, 0] := by
    simp only [m3]; rw [Mem.write_eq hm2n]; simp [encodeLE, Nat.mod_eq_of_lt hto]
  have hm4n : m4 n = some [fr.toUInt8, to.toUInt8, pc.toUInt8, 0, 0] := by
    simp only [m4]; rw [Mem.write_eq hm3n]; simp [encodeLE, Nat.mod_eq_of_lt hpc]
  have hm5n : m5 n = some (nmBytes fr to pc pr) := by
    simp only [m5]; rw [Mem.write_eq hm4n]; simp [encodeLE, Nat.mod_eq_of_lt hprb, nmBytes, prb]
    cases pr <;> rfl
  have hm6n : m6 n = some (nmBytes fr to pc pr) := by
    simp only [m6]; rw [Mem.write_eq hm5n]; simp [encodeLE, nmBytes]
  have hmo : ∀ x, x ≠ n → m6 x = m1 x := fun x hx => by
    simp only [m6, m5, m4, m3, m2]; rw [Mem.write_ne hx, Mem.write_ne hx, Mem.write_ne hx,
      Mem.write_ne hx, Mem.write_ne hx]
  have hsb1 : m1 sb = some (srcBytes fr pc c t row col cp iz) := by rw [hm1sb]; exact hsb
  have hsb2 : m2 sb = some (srcBytes fr pc c t row col cp iz) := by simp only [m2]; rw [Mem.write_ne hsbn]; exact hsb1
  have hsb3 : m3 sb = some (srcBytes fr pc c t row col cp iz) := by simp only [m3]; rw [Mem.write_ne hsbn]; exact hsb2
  let s2 : State := { s1 with mem := m2 }
  let s3 : State := { s1 with mem := m3 }
  let s4 : State := { s1 with mem := m4 }
  let s5 : State := { s1 with mem := m5 }
  let s6 : State := { s1 with mem := m6 }
  have l0 : s1.locals 0 = some (.ptr sb 0) := by rw [hj' 0 (Ne.symm j0)]; exact h0
  have st0 : ExS Gen.prog s1 (.store (.int ⟨8, false⟩) (.field (.var j) 0) (.load (.int ⟨8, false⟩)
      (.field (.var 0) 0))) .normal s2 :=
    store_u8_field hjj hm1n (by simp) (hld0 s1 l0 hsb1) hro
  have st1 : ExS Gen.prog s2 (.store (.int ⟨8, false⟩) (.field (.var j) 1) (.var 1)) .normal s3 :=
    store_u8_field (s := s2) hjj hm2n (by simp) (EvE.var (by rw [hj' 1 (Ne.symm j1)]; exact h1)) hro
  have st2 : ExS Gen.prog s3 (.store (.int ⟨8, false⟩) (.field (.var j) 2) (.load (.int ⟨8, false⟩)
      (.field (.var 0) 1))) .normal s4 :=
    store_u8_field (s := s3) hjj hm3n (by simp) (hld1 s3 l0 hsb3) hro
  have st3 : ExS Gen.prog s4 (.store (.int ⟨8, false⟩) (.field (.var j) 3) (.cast ⟨8, false⟩
      (.const (.int ⟨32, true⟩ (if pr then 1 else 0))))) .normal s5 :=
    store_u8_field (s := s4) hjj hm4n (by simp) (EvE_of_eval (n := 2) (by
      cases pr <;> simp [evalExpr, evalCast, IntTy.wrap, IntTy.modulus, prb, IntTy.u8, IntTy.toInt] <;> rfl)) hro
  have st4 : ExS Gen.prog s5 (.store (.int ⟨8, false⟩) (.field (.var j) 4) (.cast ⟨8, false⟩
      (.const (.int ⟨32, true⟩ 0)))) .normal s6 :=
    store_u8_field (s := s5) hjj hm5n (by simp [nmBytes]) (EvE_of_eval (n := 2) rfl) hro
  -- the call
  have hbuf6 : Buf m6 mb mo cb co cap L := hbuf.frame
    (by rw [hmo mb hmbn, hm1o mb hbuf.mb0 hmbn]) (by rw [hmo cb hcbn, hm1o cb hbuf.cb0 hcbn])
  have hf6 : Fresh m6 (n + 1) := by
    have := hf.after_alloc (List.replicate 5 0)
    exact ((((this.write hf.2.1).write hf.2.1).write hf.2.1).write hf.2.1).write hf.2.1
  have hrd : readBytes m6 n 0 5 = .ok (nmBytes fr to pc pr) := by
    simp [readBytes, hm6n, nmBytes]
  obtain ⟨sA, hA, hbA, hfA, hfrA⟩ := add_move_spec hbuf6 hrd hf6 (by omega) hf.2.1
  have hcall : ExS Gen.prog s6 (.call none 22 [(.var 3), (.var 4), (.var 5), (.var j)]) .normal
      { s6 with mem := sA.mem } := by
    refine ExS.call (vs := [.ptr mb mo, .ptr cb co, .int IntTy.u64 cap, .ptr n 0]) ?_ rfl rfl ?_ (Or.inl rfl)
    · refine EvArgs.cons (EvE.var ?_) (EvArgs.cons (EvE.var ?_) (EvArgs.cons (EvE.var ?_)
        (EvArgs.cons (EvE.var hjj) EvArgs.nil)))
      · show s1.locals 3 = _; rw [hj' 3 (Ne.symm j3)]; exact h3
      · show s1.locals 4 = _; rw [hj' 4 (Ne.symm j4)]; exact h4
      · show s1.locals 5 = _; rw [hj' 5 (Ne.symm j5)]; exact h5
    · rw [hro]; exact hA
  refine ⟨{ s6 with mem := sA.mem }, ExS.seq ha (ExS.seq st0 (ExS.seq st1 (ExS.seq st2 (ExS.seq st3
    (ExS.seq st4 hcall))))), rfl, rfl, hbA, hfA, ?_, ?_⟩
  · intro x a b c d
    have hxn : x ≠ n := fun e => by subst e; exact d (hf.2.2 _ (Nat.le_refl _))
    show sA.mem x = s.mem x
    rw [hfrA x a b c (by rw [hmo x hxn, hm1o x a hxn]; exact d), hmo x hxn, hm1o x a hxn]
  · show sA.mem sb = s.mem sb
    rw [hfrA sb hsb0 hsbm hsbc (by rw [hmo sb hsbn, hm1sb, hsb]; simp), hmo sb hsbn, hm1sb]
end emit

theorem ipz_body (c : Color) (r : Nat) (hr : r < 9) (m : Mem) :
    ∃ s', ExS Gen.prog ⟨frameLocals Gen.in_promotion_zone.params [u32 c.idx, i32 r], m, false⟩
      Gen.in_promotion_zone.body (.ret (some (bool8 (inZone c r)))) s' ∧ s'.mem = m := by
  cases c <;> (match r, hr with
    | 0, _ | 1, _ | 2, _ | 3, _ | 4, _ | 5, _ | 6, _ | 7, _ | 8, _ =>
      exact ⟨_, ExS_of_execStmt Gen.prog (n := 30) (Eq.refl _), rfl⟩)

theorem fp_body (c : Color) (t : PieceType) (r : Nat) (hr : r < 9) (m : Mem) :
    ∃ s', ExS Gen.prog ⟨frameLocals Gen.forced_promotion.params [u32 c.idx, u32 t.code, i32 r], m, false⟩
      Gen.forced_promotion.body (.ret (some (bool8 (deadRow c t r)))) s' ∧ s'.mem = m := by
  cases c <;> cases t <;> (match r, hr with
    | 0, _ | 1, _ | 2, _ | 3, _ | 4, _ | 5, _ | 6, _ | 7, _ | 8, _ =>
      exact ⟨_, ExS_of_execStmt Gen.prog (n := 30) (Eq.refl _), rfl⟩)

theorem call_ipz {s : State} {d : Nat} {args : List Expr} {c : Color} {r : Nat} (hr : r < 9)
    (hargs : EvArgs Gen.prog s args [u32 c.idx, i32 r]) (hro : s.ro = false) :
    ExS Gen.prog s (.call (some d) 11 args) .normal { s with locals := s.locals.upd d (bool8 (inZone c r)) } := by
  obtain ⟨s', h, hm⟩ := ipz_body c r hr s.mem
  have := ExS.call_dst (d := d) (f := 11) (fn := Gen.in_promotion_zone) hargs rfl rfl (by rw [hro]; exact h)
  rw [hm] at this; exact this

theorem call_fp {s : State} {d : Nat} {args : List Expr} {c : Color} {t : PieceType} {r : Nat} (hr : r < 9)
    (hargs : EvArgs Gen.prog s args [u32 c.idx, u32 t.code, i32 r]) (hro : s.ro = false) :
    ExS Gen.prog s (.call (some d) 12 args) .normal { s with locals := s.locals.upd d (bool8 (deadRow c t r)) } := by
  obtain ⟨s', h, hm⟩ := fp_body c t r hr s.mem
  have := ExS.call_dst (d := d) (f := 12) (fn := Gen.forced_promotion) hargs rfl rfl (by rw [hro]; exact h)
  rw [hm] at this; exact this

theorem load_u32_field {s : State} {j b o i : Nat} {blk : Block}
    (hj : s.locals j = some (.ptr b o)) (hb : s.mem b = some blk) (hi : o + i + 4 ≤ blk.length) :
    EvE Gen.prog s (.load (.int ⟨32, false⟩) (.field (.var j) i))
      (.int ⟨32, false⟩ (decodeLE ((blk.drop (o + i)).take 4))) := by
  refine EvE.load (pa := .ptr b (o + i)) (EvE.field (EvE.var hj) (by simp [ptrAddN, hb]; omega)) ?_
  simp only [load, readBytes, hb, Ty.size, IntTy.bytes, show o + i + 32 / 8 ≤ blk.length by omega, ite_true]
  rfl

/-- The promotion choices exactly as `add_normal_move` makes them. -/
def promoC (c : Color) (t : PieceType) (r : Nat) (cp iz : Bool) : List Bool :=
  if deadRow c t r then [true] else if cp && (iz || inZone c r) then [false, true] else [false]

theorem src_color (fr pc : Nat) (c : Color) (t : PieceType) (row col : Nat) (cp iz : Bool) :
    decodeLE (((srcBytes fr pc c t row col cp iz).drop (0 + 4)).take 4) = c.idx := by
  cases c <;> simp [srcBytes, le32, decodeLE, Color.idx]

theorem src_type (fr pc : Nat) (c : Color) (t : PieceType) (row col : Nat) (cp iz : Bool) :
    decodeLE (((srcBytes fr pc c t row col cp iz).drop (0 + 8)).take 4) = t.code := by
  have : t.code < 16 := by cases t <;> decide
  simp [srcBytes, le32, decodeLE]
  omega

end Shogi.C.Proofs

namespace Shogi.C.Proofs
open MiniC Shogi Shogi.C

section anm
variable {sb fr pc to mb mo cb co cap n r : Nat} {c : Color} {t : PieceType}
  {row col : Nat} {cp iz : Bool} {L : List (List UInt8)} {m : Mem}

theorem src_flag (st : State) (i : Nat) (b : Bool) (hl : st.locals 0 = some (.ptr sb 0))
    (hm : st.mem sb = some (srcBytes fr pc c t row col cp iz))
    (hb : (srcBytes fr pc c t row col cp iz).getD (0 + i) 0 = if b then 1 else 0) (hi : i < 24) :
    EvE Gen.prog st (.cast ⟨32, true⟩ (.load (.int ⟨8, false⟩) (.field (.var 0) i)))
      (.int IntTy.i32 (if b then 1 else 0)) := by
  refine EvE.cast (load_u8_field hl hm (by simp [srcBytes_length]; omega)) ?_
  rw [hb]; cases b <;> rfl

theorem add_normal_move_spec (hr : r < 9) (hbuf : Buf m mb mo cb co cap L) (hf : Fresh m n)
    (h64 : n + 4 < 2 ^ 64) (hsb : m sb = some (srcBytes fr pc c t row col cp iz))
    (hfr : fr < 256) (hpc : pc < 256) (hto : to < 256)
    (hsb0 : sb ≠ 0) (hsbm : sb ≠ mb) (hsbc : sb ≠ cb) :
    ∃ s', ExS Gen.prog ⟨frameLocals Gen.add_normal_move.params
        [.ptr sb 0, .int IntTy.u8 to, i32 r, .ptr mb mo, .ptr cb co, .int IntTy.u64 cap], m, false⟩
      Gen.add_normal_move.body .normal s' ∧
      Buf s'.mem mb mo cb co cap (L ++ (promoC c t r cp iz).map (nmBytes fr to pc)) ∧
      Fresh s'.mem (n + 2 * (promoC c t r cp iz).length) ∧ Frame m s'.mem mb cb ∧ s'.mem sb = m sb := by
  let s0 : State := ⟨frameLocals Gen.add_normal_move.params
    [.ptr sb 0, .int IntTy.u8 to, i32 r, .ptr mb mo, .ptr cb co, .int IntTy.u64 cap], m, false⟩
  have l0 : s0.locals 0 = some (.ptr sb 0) := rfl
  have hcpE := src_flag s0 20 cp l0 hsb (by cases cp <;> simp [srcBytes, le32]) (by omega)
  have hizE := src_flag s0 21 iz l0 hsb (by cases iz <;> simp [srcBytes, le32]) (by omega)
  have hcol : EvE Gen.prog s0 (.load (.int ⟨32, false⟩) (.field (.var 0) 4)) (u32 c.idx) := by
    have := load_u32_field (i := 4) l0 hsb (by simp [srcBytes_length])
    rw [src_color] at this; exact this
  have htyp : EvE Gen.prog s0 (.load (.int ⟨32, false⟩) (.field (.var 0) 8)) (u32 t.code) := by
    have := load_u32_field (i := 8) l0 hsb (by simp [srcBytes_length])
    rw [src_type] at this; exact this
  have hrow : EvE Gen.prog s0 (.var 2) (i32 r) := EvE.var rfl
  -- part A: `promotion_possible` into local 6
  let pp := cp && (iz || inZone c r)
  have hA : ∃ L6, ExS Gen.prog s0 (.seq (.ite (.cast ⟨32, true⟩ (.load (.int ⟨8, false⟩) (.field (.var 0) 20)))
      (.seq (.ite (.cast ⟨32, true⟩ (.load (.int ⟨8, false⟩) (.field (.var 0) 21)))
        (.set 8 (.const (.int ⟨32, true⟩ 1)))
        (.seq (.call (some 7) 11 [(.load (.int ⟨32, false⟩) (.field (.var 0) 4)), (.var 2)])
          (.set 8 (.lor (.const (.int ⟨32, true⟩ 0)) (.cast ⟨32, true⟩ (.var 7))))))
        (.set 9 (.land (.const (.int ⟨32, true⟩ 1)) (.var 8))))
      (.set 9 (.const (.int ⟨32, true⟩ 0))))
      (.set 6 (.cast ⟨8, false⟩ (.bin .ne (some ⟨32, true⟩) (.var 9) (.const (.int ⟨32, true⟩ 0))))))
      .normal { s0 with locals := L6 } ∧ L6 6 = some (.int IntTy.u8 (if pp then 1 else 0)) ∧
      ∀ x, x ≠ 6 → x ≠ 7 → x ≠ 8 → x ≠ 9 → L6 x = s0.locals x := by
    cases hcp : cp
    · rw [hcp] at hcpE
      refine ⟨_, ExS.seq (ExS.ite (bc := false) hcpE rfl (ExS.set (EvE.const _)))
        (ExS.set (EvE_of_eval (n := 4) rfl)), ?_, ?_⟩
      · simp [Locals.upd, pp, hcp, IntTy.u8, IntTy.wrap, IntTy.toInt, IntTy.i32, IntTy.modulus]
      · intro x a b c d; simp [Locals.upd, a, d]
    · rw [hcp] at hcpE
      cases hiz : iz
      · rw [hiz] at hizE
        have hcall := call_ipz (d := 7) hr (EvArgs.cons hcol (EvArgs.cons hrow EvArgs.nil)) (s := s0) rfl
        cases hz : inZone c r
        · rw [hz] at hcall
          refine ⟨_, ExS.seq (ExS.ite (bc := true) hcpE rfl (ExS.seq (ExS.ite (bc := false) hizE rfl
            (ExS.seq hcall (ExS.set (EvE_of_eval (n := 4) rfl)))) (ExS.set (EvE_of_eval (n := 4) rfl))))
            (ExS.set (EvE_of_eval (n := 4) rfl)), ?_, ?_⟩
          · simp [Locals.upd, pp, hz, hiz, hcp, IntTy.u8, IntTy.wrap, IntTy.toInt, IntTy.i32, IntTy.modulus]
          · intro x a b c d; simp [Locals.upd, a, b, c, d]
        · rw [hz] at hcall
          refine ⟨_, ExS.seq (ExS.ite (bc := true) hcpE rfl (ExS.seq (ExS.ite (bc := false) hizE rfl
            (ExS.seq hcall (ExS.set (EvE_of_eval (n := 4) rfl)))) (ExS.set (EvE_of_eval (n := 4) rfl))))
            (ExS.set (EvE_of_eval (n := 4) rfl)), ?_, ?_⟩
          · simp [Locals.upd, pp, hz, hiz, hcp, IntTy.u8, IntTy.wrap, IntTy.toInt, IntTy.i32, IntTy.modulus]
          · intro x a b c d; simp [Locals.upd, a, b, c, d]
      · rw [hiz] at hizE
        refine ⟨_, ExS.seq (ExS.ite (bc := true) hcpE rfl (ExS.seq (ExS.ite (bc := true) hizE rfl
          (ExS.set (EvE.const _))) (ExS.set (EvE_of_eval (n := 4) rfl))))
          (ExS.set (EvE_of_eval (n := 4) rfl)), ?_, ?_⟩
        · simp [Locals.upd, pp, hiz, hcp, IntTy.u8, IntTy.wrap, IntTy.toInt, IntTy.i32, IntTy.modulus]
        · intro x a b c d; simp [Locals.upd, a, c, d]
  obtain ⟨L6, hexA, h6, hL6⟩ := hA
  let sA : State := { s0 with locals := L6 }
  have lA : ∀ x, x ≠ 6 → x ≠ 7 → x ≠ 8 → x ≠ 9 → sA.locals x = s0.locals x := hL6
  -- part B: `mandatory` into local 10
  let dd := deadRow c t r
  have hcolA : EvE Gen.prog sA (.load (.int ⟨32, false⟩) (.field (.var 0) 4)) (u32 c.idx) := by
    have := load_u32_field (s := sA) (i := 4) (by rw [lA 0 (by decide) (by decide) (by decide) (by decide)]; rfl)
      hsb (by simp [srcBytes_length])
    rw [src_color] at this; exact this
  have htypA : EvE Gen.prog sA (.load (.int ⟨32, false⟩) (.field (.var 0) 8)) (u32 t.code) := by
    have := load_u32_field (s := sA) (i := 8) (by rw [lA 0 (by decide) (by decide) (by decide) (by decide)]; rfl)
      hsb (by simp [srcBytes_length])
    rw [src_type] at this; exact this
  have hrowA : EvE Gen.prog sA (.var 2) (i32 r) :=
    EvE.var (by rw [lA 2 (by decide) (by decide) (by decide) (by decide)]; rfl)
  have hcallB := call_fp (d := 11) (c := c) (t := t) hr
    (EvArgs.cons hcolA (EvArgs.cons htypA (EvArgs.cons hrowA EvArgs.nil))) (s := sA) rfl
  let sB : State := { sA with locals := (sA.locals.upd 11 (bool8 dd)).upd 10 (bool8 dd) }
  have hexB : ExS Gen.prog sA (.seq (.call (some 11) 12 [(.load (.int ⟨32, false⟩) (.field (.var 0) 4)),
      (.load (.int ⟨32, false⟩) (.field (.var 0) 8)), (.var 2)]) (.set 10 (.var 11))) .normal sB :=
    ExS.seq hcallB (ExS.set (EvE.var (by simp [Locals.upd]; rfl)))
  have lB : ∀ x, x ≠ 6 → x ≠ 7 → x ≠ 8 → x ≠ 9 → x ≠ 10 → x ≠ 11 → sB.locals x = s0.locals x := by
    intro x a b c d e f; simp only [sB, Locals.upd, e, f, if_false]; exact lA x a b c d
  have hB6 : sB.locals 6 = some (.int IntTy.u8 (if pp then 1 else 0)) := by
    simp only [sB, Locals.upd]; simp; exact h6
  have hB10 : sB.locals 10 = some (bool8 dd) := by simp [sB, Locals.upd]
  have hpre : ∀ {C : Stmt} {o s'}, ExS Gen.prog sB C o s' →
      ExS Gen.prog s0 (.seq (.seq (.ite (.cast ⟨32, true⟩ (.load (.int ⟨8, false⟩) (.field (.var 0) 20)))
      (.seq (.ite (.cast ⟨32, true⟩ (.load (.int ⟨8, false⟩) (.field (.var 0) 21)))
        (.set 8 (.const (.int ⟨32, true⟩ 1)))
        (.seq (.call (some 7) 11 [(.load (.int ⟨32, false⟩) (.field (.var 0) 4)), (.var 2)])
          (.set 8 (.lor (.const (.int ⟨32, true⟩ 0)) (.cast ⟨32, true⟩ (.var 7))))))
        (.set 9 (.land (.const (.int ⟨32, true⟩ 1)) (.var 8))))
      (.set 9 (.const (.int ⟨32, true⟩ 0))))
      (.set 6 (.cast ⟨8, false⟩ (.bin .ne (some ⟨32, true⟩) (.var 9) (.const (.int ⟨32, true⟩ 0))))))
      (.seq (.seq (.call (some 11) 12 [(.load (.int ⟨32, false⟩) (.field (.var 0) 4)),
      (.load (.int ⟨32, false⟩) (.field (.var 0) 8)), (.var 2)]) (.set 10 (.var 11))) C)) o s' :=
    fun h => ExS.seq hexA (ExS.seq hexB h)
  have g := fun x (a : x ≠ 6) (b : x ≠ 7) (c : x ≠ 8) (d : x ≠ 9) (e : x ≠ 10) (f : x ≠ 11) => lB x a b c d e f
  have b0 : sB.locals 0 = some (.ptr sb 0) := by rw [g 0 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; rfl
  have b1 : sB.locals 1 = some (.int IntTy.u8 to) := by rw [g 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; rfl
  have b3 : sB.locals 3 = some (.ptr mb mo) := by rw [g 3 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; rfl
  have b4 : sB.locals 4 = some (.ptr cb co) := by rw [g 4 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; rfl
  have b5 : sB.locals 5 = some (.int IntTy.u64 cap) := by rw [g 5 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; rfl
  unfold Gen.add_normal_move
  simp only
  cases hdd : dd
  · -- not mandatory: the plain move, then maybe the promotion
    obtain ⟨s1, he1, hl1, hro1, hb1, hf1, hfr1, hsb1⟩ := emit_spec (s := sB) 13 false (by decide) b0 b1 b3 b4 b5 rfl
      hsb hfr hpc hto hbuf hf (by omega) hsb0 hsbm hsbc
    have hpromo : promoC c t r cp iz = false :: (if pp then [true] else []) := by
      simp only [promoC, pp]; rw [show deadRow c t r = false from hdd]
      cases cp <;> cases iz <;> simp <;> cases inZone c r <;> simp
    have h1_6 : s1.locals 6 = some (.int IntTy.u8 (if pp then 1 else 0)) := by rw [hl1]; simp [Locals.upd]; exact hB6
    cases hpp : pp
    · refine ⟨s1, hpre (ExS.ite (bc := false) (EvE.var hB10) (by simp [bool8, hdd, u8]; rfl)
        (ExS.seq he1 (ExS.ite (bc := false) (EvE.var h1_6) (by simp [hpp]; rfl) ExS.skip))), ?_, ?_, hfr1, hsb1⟩
      · rw [hpromo, hpp]; simpa using hb1
      · rw [hpromo, hpp]; simpa using hf1
    · have c0 : s1.locals 0 = some (.ptr sb 0) := by rw [hl1]; simp [Locals.upd]; exact b0
      have c1 : s1.locals 1 = some (.int IntTy.u8 to) := by rw [hl1]; simp [Locals.upd]; exact b1
      have c3 : s1.locals 3 = some (.ptr mb mo) := by rw [hl1]; simp [Locals.upd]; exact b3
      have c4 : s1.locals 4 = some (.ptr cb co) := by rw [hl1]; simp [Locals.upd]; exact b4
      have c5 : s1.locals 5 = some (.int IntTy.u64 cap) := by rw [hl1]; simp [Locals.upd]; exact b5
      obtain ⟨s2, he2, _, _, hb2, hf2, hfr2, hsb2⟩ := emit_spec (s := s1) 14 true (by decide) c0 c1 c3 c4 c5
        (by rw [hro1]) (by rw [hsb1]; exact hsb) hfr hpc hto hb1 hf1 (by omega) hsb0 hsbm hsbc
      refine ⟨s2, hpre (ExS.ite (bc := false) (EvE.var hB10) (by simp [bool8, hdd, u8]; rfl)
        (ExS.seq he1 (ExS.ite (bc := true) (EvE.var h1_6) (by simp [hpp]; rfl) he2))), ?_, ?_,
        hfr1.trans hfr2, by rw [hsb2, hsb1]⟩
      · rw [hpromo, hpp]; simpa using hb2
      · rw [hpromo, hpp]; simpa [show n + 1 + 1 + 1 + 1 = n + 2 * 2 by omega] using hf2
  · obtain ⟨s1, he1, _, _, hb1, hf1, hfr1, hsb1⟩ := emit_spec (s := sB) 12 true (by decide) b0 b1 b3 b4 b5 rfl
      hsb hfr hpc hto hbuf hf (by omega) hsb0 hsbm hsbc
    have hpromo : promoC c t r cp iz = [true] := by
      simp only [promoC]; rw [show deadRow c t r = true from hdd]; rfl
    refine ⟨s1, hpre (ExS.ite (bc := true) (EvE.var hB10) (by simp [bool8, hdd, u8]; rfl) he1), ?_, ?_, hfr1, hsb1⟩
    · rw [hpromo]; simpa using hb1
    · rw [hpromo]; simpa using hf1
end anm

end Shogi.C.Proofs
