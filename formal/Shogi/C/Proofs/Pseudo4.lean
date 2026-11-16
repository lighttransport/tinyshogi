/-
  T7 generators, layer 3: `generate_pseudo_for_color`, part 4 — building the
  `MoveSource` record.
-/
import Shogi.C.Proofs.Pseudo3

namespace Shogi.C.Proofs
open MiniC Shogi Shogi.C

theorem store_int_field {s : State} {j b o i v : Nat} {t : IntTy} {e : Expr} {blk : Block}
    (hj : s.locals j = some (.ptr b o)) (hb : s.mem b = some blk) (hi : o + i + t.bytes ≤ blk.length)
    (he : EvE Gen.prog s e (.int t v)) (hro : s.ro = false) (hlen : (encodeLE t.bytes v).length = t.bytes) :
    ExS Gen.prog s (.store (.int t) (.field (.var j) i) e) .normal
      { s with mem := s.mem.write b (o + i) (encodeLE t.bytes v) } :=
  ExS.store (pa := .ptr b (o + i)) (EvE.field (EvE.var hj) (by simp [ptrAddN, hb]; omega)) he hro
    (by simp only [store, ite_true]; exact writeBytes_ok hb (by rw [hlen]; omega))

theorem encodeLE_length : ∀ k v, (encodeLE k v).length = k := by
  intro k; induction k with
  | zero => intro _; rfl
  | succ k ih => intro v; simp [encodeLE, ih]

theorem le32_small (v : Nat) (h : v < 256) : encodeLE 4 v = le32 v := by
  simp [encodeLE, le32, Nat.div_eq_of_lt h, Nat.mod_eq_of_lt h, Nat.div_eq_of_lt (show v < 65536 by omega),
    Nat.div_eq_of_lt (show v < 16777216 by omega)]

theorem write_map (m : Mem) (b o : Nat) (bs : List UInt8) :
    (m.write b o bs) b = (m b).map (fun blk => blk.take o ++ bs ++ blk.drop (o + bs.length)) := by
  cases h : m b with
  | none => simp [Mem.write, h]
  | some blk => rw [Mem.write_eq h]; simp

def mkSrcStmt : Stmt := (.seq (.alloc 16 24) (.seq (.store (.int ⟨8, false⟩) (.field (.var 16) 0) (.var 6)) (.seq (.store (.int ⟨8, false⟩) (.field (.var 16) 1) (.var 7)) (.seq (.store (.int ⟨32, false⟩) (.field (.var 16) 4) (.var 1)) (.seq (.store (.int ⟨32, false⟩) (.field (.var 16) 8) (.var 10)) (.seq (.store (.int ⟨32, true⟩) (.field (.var 16) 12) (.var 12)) (.seq (.store (.int ⟨32, true⟩) (.field (.var 16) 16) (.var 14)) (.seq (.call (some 17) 5 [(.var 10)]) (.seq (.store (.int ⟨8, false⟩) (.field (.var 16) 20) (.var 17)) (.seq (.call (some 18) 11 [(.var 1), (.var 12)]) (.store (.int ⟨8, false⟩) (.field (.var 16) 21) (.var 18))))))))))))

theorem mkSrc_spec {s : State} {n fr pc row col : Nat} {c : Color} {t : PieceType}
    (hf : Fresh s.mem n) (h64 : n + 1 < 2 ^ 64) (hro : s.ro = false)
    (hfr : fr < 256) (hpc : pc < 256) (hrow : row < 9) (hcol : col < 9)
    (h1 : s.locals 1 = some (u32 c.idx)) (h6 : s.locals 6 = some (u8 fr)) (h7 : s.locals 7 = some (u8 pc))
    (h10 : s.locals 10 = some (u32 t.code)) (h12 : s.locals 12 = some (i32 (row : Int)))
    (h14 : s.locals 14 = some (i32 (col : Int))) :
    ∃ s', ExS Gen.prog s mkSrcStmt .normal s' ∧ s'.ro = s.ro ∧
      s'.mem n = some (srcBytes fr pc c t row col t.canPromote (inZone c row)) ∧ Fresh s'.mem (n + 1) ∧
      (∀ x, x ≠ 0 → x ≠ n → s'.mem x = s.mem x) ∧ s'.locals 16 = some (.ptr n 0) ∧
      (∀ x, x ≠ 16 → x ≠ 17 → x ≠ 18 → s'.locals x = s.locals x) := by
  let m1 := (s.mem.upd 0 (encodeLE 8 (n + 1))).upd n (List.replicate 24 0)
  let s1 : State := { s with mem := m1, locals := s.locals.upd 16 (.ptr n 0) }
  have ha : ExS Gen.prog s (.alloc 16 24) .normal s1 := exec_alloc (hf.allocAt (by omega)) 16 24
  have hj : ∀ x, x ≠ 16 → s1.locals x = s.locals x := fun x hx => by simp [s1, Locals.upd, hx]
  have hjj : s1.locals 16 = some (.ptr n 0) := by simp [s1, Locals.upd]
  have hjjm : ∀ m : Mem, ({ s1 with mem := m } : State).locals 16 = some (.ptr n 0) := fun _ => hjj
  have hm1n : m1 n = some (List.replicate 24 0) := Mem.upd_eq
  have hm1o : ∀ x, x ≠ 0 → x ≠ n → m1 x = s.mem x := fun x a b => by
    simp only [m1]; rw [Mem.upd_ne b, Mem.upd_ne a]
  have hro1 : s1.ro = false := hro
  have len : ∀ (m : Mem) (o : Nat) (bs : List UInt8), (m n).map List.length = some 24 → o + bs.length ≤ 24 →
      ∃ blk, m n = some blk ∧ blk.length = 24 ∧ ((m.write n o bs) n).map List.length = some 24 := by
    intro m o bs h hl
    cases hm : m n with
    | none => rw [hm] at h; simp at h
    | some blk =>
      rw [hm] at h; simp at h
      refine ⟨blk, rfl, h, ?_⟩
      rw [write_map, hm]; simp; omega
  -- stores
  have e6 : ∀ m : Mem, EvE Gen.prog { s1 with mem := m } (.var 6) (.int IntTy.u8 fr) := fun _ => EvE.var (by show s1.locals 6 = _; rw [hj 6 (by decide)]; exact h6)
  have e7 : ∀ m : Mem, EvE Gen.prog { s1 with mem := m } (.var 7) (.int IntTy.u8 pc) := fun _ => EvE.var (by show s1.locals 7 = _; rw [hj 7 (by decide)]; exact h7)
  have e1 : ∀ m : Mem, EvE Gen.prog { s1 with mem := m } (.var 1) (.int IntTy.u32 c.idx) := fun _ => EvE.var (by show s1.locals 1 = _; rw [hj 1 (by decide)]; exact h1)
  have e10 : ∀ m : Mem, EvE Gen.prog { s1 with mem := m } (.var 10) (.int IntTy.u32 t.code) := fun _ => EvE.var (by show s1.locals 10 = _; rw [hj 10 (by decide)]; exact h10)
  have e12 : ∀ m : Mem, EvE Gen.prog { s1 with mem := m } (.var 12) (.int IntTy.i32 row) :=
    fun _ => EvE.var (by show s1.locals 12 = _; rw [hj 12 (by decide), h12, i32_nat row (by omega)])
  have e14 : ∀ m : Mem, EvE Gen.prog { s1 with mem := m } (.var 14) (.int IntTy.i32 col) :=
    fun _ => EvE.var (by show s1.locals 14 = _; rw [hj 14 (by decide), h14, i32_nat col (by omega)])
  let w1 := m1.write n (0 + 0) (encodeLE 1 fr)
  let w2 := w1.write n (0 + 1) (encodeLE 1 pc)
  let w3 := w2.write n (0 + 4) (encodeLE 4 c.idx)
  let w4 := w3.write n (0 + 8) (encodeLE 4 t.code)
  let w5 := w4.write n (0 + 12) (encodeLE 4 row)
  let w6 := w5.write n (0 + 16) (encodeLE 4 col)
  have l1 : (m1 n).map List.length = some 24 := by rw [hm1n]; simp
  obtain ⟨b1, hb1, hl1, l2⟩ := len m1 (0 + 0) (encodeLE 1 fr) l1 (by simp [encodeLE_length])
  obtain ⟨b2, hb2, hl2, l3⟩ := len w1 (0 + 1) (encodeLE 1 pc) l2 (by simp [encodeLE_length])
  obtain ⟨b3, hb3, hl3, l4⟩ := len w2 (0 + 4) (encodeLE 4 c.idx) l3 (by simp [encodeLE_length])
  obtain ⟨b4, hb4, hl4, l5⟩ := len w3 (0 + 8) (encodeLE 4 t.code) l4 (by simp [encodeLE_length])
  obtain ⟨b5, hb5, hl5, l6⟩ := len w4 (0 + 12) (encodeLE 4 row) l5 (by simp [encodeLE_length])
  obtain ⟨b6, hb6, hl6, l7⟩ := len w5 (0 + 16) (encodeLE 4 col) l6 (by simp [encodeLE_length])
  have st1 := store_int_field (o := 0) (b := n) (t := ⟨8, false⟩) (i := 0) (blk := b1) hjj hb1 (by rw [hl1]; decide) (e6 m1) hro1
    (encodeLE_length _ _)
  have st2 := store_int_field (o := 0) (b := n) (s := { s1 with mem := w1 }) (t := ⟨8, false⟩) (i := 1) (blk := b2) (hjjm w1) hb2
    (by rw [hl2]; decide) (e7 w1) hro1 (encodeLE_length _ _)
  have st3 := store_int_field (o := 0) (b := n) (s := { s1 with mem := w2 }) (t := ⟨32, false⟩) (i := 4) (blk := b3) (hjjm w2) hb3
    (by rw [hl3]; decide) (e1 w2) hro1 (encodeLE_length _ _)
  have st4 := store_int_field (o := 0) (b := n) (s := { s1 with mem := w3 }) (t := ⟨32, false⟩) (i := 8) (blk := b4) (hjjm w3) hb4
    (by rw [hl4]; decide) (e10 w3) hro1 (encodeLE_length _ _)
  have st5 := store_int_field (o := 0) (b := n) (s := { s1 with mem := w4 }) (t := ⟨32, true⟩) (i := 12) (blk := b5) (hjjm w4) hb5
    (by rw [hl5]; decide) (e12 w4) hro1 (encodeLE_length _ _)
  have st6 := store_int_field (o := 0) (b := n) (s := { s1 with mem := w5 }) (t := ⟨32, true⟩) (i := 16) (blk := b6) (hjjm w5) hb6
    (by rw [hl6]; decide) (e14 w5) hro1 (encodeLE_length _ _)
  -- shogi_can_promote(type)
  let cp := t.canPromote
  let iz := inZone c row
  have hcp : run Gen.fid_shogi_can_promote [u32 t.code] = some (some (bool8 cp)) := by
    cases t <;> decide +kernel
  have hiz : run Gen.fid_in_promotion_zone [u32 c.idx, i32 (row : Int)] = some (some (bool8 iz)) :=
    in_promotion_zone_refines c ⟨row, hrow⟩
  let s7 : State := { s1 with mem := w6, locals := s1.locals.upd 17 (bool8 cp) }
  have ec1 : ExS Gen.prog { s1 with mem := w6 } (.call (some 17) 5 [(.var 10)]) .normal s7 :=
    call_pure rfl rfl rfl rfl hcp (EvArgs.cons (EvE.var (by show s1.locals 10 = _; rw [hj 10 (by decide)]; exact h10))
      EvArgs.nil)
  obtain ⟨b7, hb7, hl7, l8⟩ := len w6 (0 + 20) (encodeLE 1 (if cp then 1 else 0)) l7 (by simp [encodeLE_length])
  have st7 := store_int_field (o := 0) (b := n) (s := s7) (j := 16) (e := .var 17) (t := ⟨8, false⟩) (i := 20) (v := if cp then 1 else 0)
    (by simp [s7, Locals.upd]; exact hjj) hb7 (by rw [hl7]; decide)
    (EvE.var (by simp [s7, Locals.upd, bool8, u8]; rfl)) hro1 (encodeLE_length _ _)
  let w7 := w6.write n (0 + 20) (encodeLE 1 (if cp then 1 else 0))
  let s8 : State := { s7 with mem := w7, locals := s7.locals.upd 18 (bool8 iz) }
  have ec2 : ExS Gen.prog { s7 with mem := w7 } (.call (some 18) 11 [(.var 1), (.var 12)]) .normal s8 :=
    call_pure rfl rfl rfl rfl hiz (EvArgs.cons (EvE.var (by
        show s7.locals 1 = _; simp [s7, Locals.upd]; rw [hj 1 (by decide)]; exact h1))
      (EvArgs.cons (EvE.var (by show s7.locals 12 = _; simp [s7, Locals.upd]; rw [hj 12 (by decide)]; exact h12))
      EvArgs.nil))
  obtain ⟨b8, hb8, hl8, _⟩ := len w7 (0 + 21) (encodeLE 1 (if iz then 1 else 0)) l8 (by simp [encodeLE_length])
  have st8 := store_int_field (o := 0) (b := n) (s := s8) (j := 16) (e := .var 18) (t := ⟨8, false⟩) (i := 21) (v := if iz then 1 else 0)
    (by simp [s8, s7, Locals.upd]; exact hjj) hb8 (by rw [hl8]; decide)
    (EvE.var (by simp [s8, Locals.upd, bool8, u8]; rfl)) hro1 (encodeLE_length _ _)
  let w8 := w7.write n (0 + 21) (encodeLE 1 (if iz then 1 else 0))
  have hfin : w8 n = some (srcBytes fr pc c t row col cp iz) := by
    simp only [w8, w7, w6, w5, w4, w3, w2, w1, write_map, hm1n]
    have hc := show c.idx < 2 by cases c <;> decide
    have ht := show t.code < 15 by cases t <;> decide
    rw [le32_small c.idx (by omega), le32_small t.code (by omega), le32_small row (by omega),
      le32_small col (by omega)]
    cases cp <;> cases iz <;> simp [srcBytes, encodeLE, Nat.mod_eq_of_lt hfr, Nat.mod_eq_of_lt hpc, le32] <;> rfl
  refine ⟨{ s8 with mem := w8 }, ?_, rfl, hfin, ?_, ?_, ?_, ?_⟩
  · exact ExS.seq ha (ExS.seq st1 (ExS.seq st2 (ExS.seq st3 (ExS.seq st4 (ExS.seq st5 (ExS.seq st6
      (ExS.seq ec1 (ExS.seq st7 (ExS.seq ec2 st8)))))))))
  · have h0 := hf.2.1
    exact (((((((((hf.after_alloc _).write h0).write h0).write h0).write h0).write h0).write h0).write h0).write h0)
  · intro x a b
    show w8 x = s.mem x
    simp only [w8, w7, w6, w5, w4, w3, w2, w1]
    rw [Mem.write_ne b, Mem.write_ne b, Mem.write_ne b, Mem.write_ne b, Mem.write_ne b, Mem.write_ne b,
      Mem.write_ne b, Mem.write_ne b, hm1o x a b]
  · simp [s8, s7, Locals.upd, hjj]
  · intro x a b c; simp [s8, s7, Locals.upd, b, c]; exact hj x a

/-! ### The `switch` -/

/-- The C's ops for a piece type, in the C's order. -/
def cOps (f : Int) : PieceType → List Op
  | .pawn => (ops1 f).map (·.1)
  | .lance => (ops2 f).map (·.1)
  | .knight => (ops3 f).map (·.1)
  | .silver => (ops4 f).map (·.1)
  | .gold => (ops5 f).map (·.1)
  | .bishop => (ops6 f).map (·.1)
  | .rook => (ops7 f).map (·.1)
  | .king => kingOps
  | .proPawn => (ops9 f).map (·.1)
  | .proLance => (ops10 f).map (·.1)
  | .proKnight => (ops11 f).map (·.1)
  | .proSilver => (ops12 f).map (·.1)
  | .horse => (ops13 f).map (·.1)
  | .dragon => (ops14 f).map (·.1)

theorem kingOps_length : kingOps.length = 8 := by decide

theorem cOps_length (f : Int) (t : PieceType) : (cOps f t).length ≤ 8 := by
  cases t <;> simp [cOps, ops1, ops2, ops3, ops4, ops5, ops6, ops7, ops9, ops10, ops11, ops12, ops13, ops14, kingOps_length]

theorem flatMap_fst {α β γ : Type} (L : List (α × β)) (g : α → List γ) :
    L.flatMap (fun x => g x.1) = (L.map (·.1)).flatMap g := by
  rw [List.flatMap_map]

section sw
variable {p : Position} {sb fr pc mb mo cb co cap row col : Nat} {c : Color} {cp iz : Bool}

theorem swLoop_spec (t : PieceType) (f : Int) (hf : f = -1 ∨ f = 1)
    (hrow : row < 9) (hcol : col < 9) (hfr : fr < 256) (hpc : pc < 256)
    (hsb0 : sb ≠ 0) (hsbm : sb ≠ mb) (hsbc : sb ≠ cb) (hpm : posBlock ≠ mb) (hpc' : posBlock ≠ cb)
    (s : State) (L : List (List UInt8)) (n : Nat)
    (hb : Buf s.mem mb mo cb co cap L) (hfr' : Fresh s.mem n) (h64 : n + 324 < 2 ^ 64)
    (hsb : s.mem sb = some (srcBytes fr pc c t row col cp iz)) (hm : s.mem posBlock = some (encode p))
    (hro : s.ro = false) (a0 : s.locals 0 = some posPtr) (a16 : s.locals 16 = some (.ptr sb 0))
    (a2 : s.locals 2 = some (.ptr mb mo)) (a3 : s.locals 3 = some (.ptr cb co))
    (a4 : s.locals 4 = some (.int IntTy.u64 cap)) (a5 : s.locals 5 = some (i32 f))
    (a10 : s.locals 10 = some (u32 t.code)) :
    ∃ s', ExS Gen.prog s (swLoop f) .normal s' ∧ s'.ro = s.ro ∧
      (∀ x, x ≠ 19 → x ≠ 20 → s'.locals x = s.locals x) ∧
      Buf s'.mem mb mo cb co cap (L ++ (cOps f t).flatMap (opOut p c t fr pc row col cp iz)) ∧
      Fresh s'.mem (n + 2 * ((cOps f t).flatMap (opOut p c t fr pc row col cp iz)).length) ∧
      Frame s.mem s'.mem mb cb := by
  have hk : t.code < 2 ^ 32 := by cases t <;> decide
  have hcs : ∀ x ∈ swCases f, x.1 < 2 ^ 32 := by intro x hx; simp [swCases] at hx; rcases hx with h | h | h | h | h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp
  have wrap : ∀ (b : Stmt) (s' : State), ExS Gen.prog s b .brk s' → (swCases f).lookup t.code = some b →
      ExS Gen.prog s (swLoop f) .normal s' := fun b s' he hl =>
    ExS.loop_brk (ExS.seq_brk (switch_sel hk a10 _ .brk b hcs (Or.inl ⟨hl, he⟩)))
  have chainCase : ∀ (k : Nat) (ops : List (Op × Expr × Expr)), (swCases f).lookup t.code = some (chainStmt ops) →
      ArgsOk s.locals ops → cOps f t = ops.map (·.1) →
      ∃ s', ExS Gen.prog s (swLoop f) .normal s' ∧ s'.ro = s.ro ∧
        (∀ x, x ≠ 19 → x ≠ 20 → s'.locals x = s.locals x) ∧
        Buf s'.mem mb mo cb co cap (L ++ (cOps f t).flatMap (opOut p c t fr pc row col cp iz)) ∧
        Fresh s'.mem (n + 2 * ((cOps f t).flatMap (opOut p c t fr pc row col cp iz)).length) ∧
        Frame s.mem s'.mem mb cb := by
    intro _ ops hl hok hc
    have hlen : ops.length ≤ 8 := by have := cOps_length f t; rw [hc, List.length_map] at this; exact this
    obtain ⟨s', e, hl', hro', hb', hf', hfr''⟩ := chain_spec (p := p) hrow hcol hfr hpc hsb0 hsbm hsbc hpm hpc'
      ops s L n hok hb hfr' (by omega) hsb hm hro a0 a16 a2 a3 a4
    refine ⟨s', wrap _ _ e hl, hro', fun x _ _ => by rw [hl'], ?_, ?_, hfr''⟩
    · rw [hc, ← flatMap_fst]; exact hb'
    · rw [hc, ← flatMap_fst]; exact hf'
  have h5 := a5
  cases t
  case pawn => exact chainCase 0 (ops1 f) rfl (swOps_ok hf h5 1 (by decide)) rfl
  case lance => exact chainCase 0 (ops2 f) rfl (swOps_ok hf h5 2 (by decide)) rfl
  case knight => exact chainCase 0 (ops3 f) rfl (swOps_ok hf h5 3 (by decide)) rfl
  case silver => exact chainCase 0 (ops4 f) rfl (swOps_ok hf h5 4 (by decide)) rfl
  case gold => exact chainCase 0 (ops5 f) rfl (swOps_ok hf h5 5 (by decide)) rfl
  case bishop => exact chainCase 0 (ops6 f) rfl (swOps_ok hf h5 6 (by decide)) rfl
  case rook => exact chainCase 0 (ops7 f) rfl (swOps_ok hf h5 7 (by decide)) rfl
  case king =>
    let s0 : State := { s with locals := s.locals.upd 19 (i32 (-1)) }
    have e0 : ExS Gen.prog s (.set 19 (.un .neg ⟨32, true⟩ (.const (.int ⟨32, true⟩ 1)))) .normal s0 :=
      ExS.set (EvE_of_eval (n := 3) (by simp [evalExpr, evalUn, intOf, IntTy.toInt, Res.bind, i32, IntTy.wrap,
        IntTy.modulus, arith, IntTy.inRange, IntTy.i32]; decide))
    have h0x : ∀ x, x ≠ 19 → s0.locals x = s.locals x := fun x hx => by simp [s0, Locals.upd, hx]
    obtain ⟨s', e', hro', hl', hb', hf', hfr''⟩ := king_outer (p := p) (c := c) (t := .king) (cp := cp) (iz := iz)
      hrow hcol hfr hpc hsb0 hsbm hsbc hpm hpc' 3 (-1) s0 L n (by omega) (by omega) hb hfr' (by omega) hsb hm hro
      (by rw [h0x 0 (by decide)]; exact a0) (by rw [h0x 16 (by decide)]; exact a16)
      (by rw [h0x 2 (by decide)]; exact a2) (by rw [h0x 3 (by decide)]; exact a3)
      (by rw [h0x 4 (by decide)]; exact a4) (by simp [s0, Locals.upd])
    refine ⟨s', wrap case8 s' ?_ rfl, hro', fun x a b => by rw [hl' x a b, h0x x a], hb', hf', hfr''⟩
    exact ExS.seq (ExS.seq e0 (by rw [loop1_eq]; exact e')) ExS.brk
  case proPawn => exact chainCase 0 (ops9 f) rfl (swOps_ok hf h5 9 (by decide)) rfl
  case proLance => exact chainCase 0 (ops10 f) rfl (swOps_ok hf h5 10 (by decide)) rfl
  case proKnight => exact chainCase 0 (ops11 f) rfl (swOps_ok hf h5 11 (by decide)) rfl
  case proSilver => exact chainCase 0 (ops12 f) rfl (swOps_ok hf h5 12 (by decide)) rfl
  case horse => exact chainCase 0 (ops13 f) rfl (swOps_ok hf h5 13 (by decide)) rfl
  case dragon => exact chainCase 0 (ops14 f) rfl (swOps_ok hf h5 14 (by decide)) rfl

end sw

end Shogi.C.Proofs
