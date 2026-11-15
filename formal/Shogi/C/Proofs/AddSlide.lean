/-
  T7 generators, layer 2: `add_slide` emits the moves along one ray: every
  empty square, then the first occupied one if it holds an enemy non-king.
-/
import Shogi.C.Proofs.AddStep

namespace Shogi.C.Proofs
open MiniC Shogi Shogi.C

def slideSq : Stmt := (.seq (.call (some 11) 10 [(.var 7), (.var 8)]) (.set 10 (.var 11)))
def slideLd : Stmt := (.set 12 (.load (.int ⟨8, false⟩) (.index (.field (.var 0) 0) (.var 10) 1)))
def slideTgt : Stmt := (.ite (.bin .ne (some ⟨32, true⟩) (.cast ⟨32, true⟩ (.var 12)) (.const (.int ⟨32, true⟩ 0))) (.seq (.seq (.call (some 13) 1 [(.var 12)]) (.seq (.ite (.bin .ne (some ⟨32, false⟩) (.cast ⟨32, false⟩ (.var 13)) (.cast ⟨32, false⟩ (.load (.int ⟨32, false⟩) (.field (.var 1) 4)))) (.seq (.call (some 14) 2 [(.var 12)]) (.set 15 (.land (.const (.int ⟨32, true⟩ 1)) (.bin .ne (some ⟨32, false⟩) (.cast ⟨32, false⟩ (.var 14)) (.cast ⟨32, false⟩ (.const (.int ⟨32, true⟩ 8))))))) (.set 15 (.const (.int ⟨32, true⟩ 0)))) (.ite (.var 15) (.call none 23 [(.var 1), (.var 10), (.var 7), (.var 4), (.var 5), (.var 6)]) .skip))) .brk) .skip)
def slideCall : Stmt := (.call none 23 [(.var 1), (.var 10), (.var 7), (.var 4), (.var 5), (.var 6)])
def slideStep : Stmt := (.seq (.set 7 (.cast ⟨32, true⟩ (.bin .add (some ⟨32, true⟩) (.cast ⟨32, true⟩ (.var 7)) (.cast ⟨32, true⟩ (.var 2))))) (.set 8 (.cast ⟨32, true⟩ (.bin .add (some ⟨32, true⟩) (.cast ⟨32, true⟩ (.var 8)) (.cast ⟨32, true⟩ (.var 3))))))
def slideBody : Stmt := .seq (.call (some 9) 9 [(.var 7), (.var 8)]) (.ite (.var 9) (.seq slideSq (.seq slideLd (.seq slideTgt slideCall))) .brk)

theorem add_slide_loop_eq : Gen.add_slide_loop0 = .loop slideBody slideStep := rfl

/-- What `add_slide` offers from `(r, c)` on (fuel `k` bounds the ray). -/
def slideC (p : Position) (col : Color) (t : PieceType) (fr pc : Nat) (cp iz : Bool) (dr dc : Int) :
    Nat → Int → Int → List (List UInt8)
  | 0, _, _ => []
  | k + 1, r, c =>
    match Square.mk? r c with
    | none => []
    | some d =>
      match p.pieceAt d with
      | none => (promoC col t d.row cp iz).map (nmBytes fr d.val pc) ++ slideC p col t fr pc cp iz dr dc k (r + dr) (c + dc)
      | some q => if q.color != col && q.type != .king then (promoC col t d.row cp iz).map (nmBytes fr d.val pc) else []

theorem cast_i32 (z : Int) (h1 : -2147483648 ≤ z) (h2 : z < 2147483648) :
    evalCast ⟨32, true⟩ (i32 z) = .ok (i32 z) := by
  simp only [evalCast, i32, IntTy.i32, if_true]
  rw [toInt_wrap32 z h1 h2]

theorem ev_ne_u32 {s : State} {ea eb : Expr} {a b : Nat}
    (ha : EvE Gen.prog s ea (.int IntTy.u32 a)) (hb : EvE Gen.prog s eb (.int IntTy.u32 b)) :
    EvE Gen.prog s (.bin .ne (some ⟨32, false⟩) ea eb) (boolVal (decide (a ≠ b))) :=
  EvE.bin ha hb (by simp [evalBin, isPtr, evalBinInt, binInt, intOf, IntTy.u32, Res.bind])

theorem ev_land_ne {s : State} {ea eb : Expr} {a b : Nat}
    (ha : EvE Gen.prog s ea (.int IntTy.u32 a)) (hb : EvE Gen.prog s eb (.int IntTy.u32 b)) :
    EvE Gen.prog s (.land (.const (.int ⟨32, true⟩ 1)) (.bin .ne (some ⟨32, false⟩) ea eb))
      (boolVal (decide (a ≠ b))) :=
  EvE.land_true (EvE.const _) rfl (ev_ne_u32 ha hb) (truthy_boolVal _)

/-- `add_normal_move(source, to, to_row, moves, count, capacity)` from locals
    1, 10, 7, 4, 5, 6. -/
theorem ncall_spec {s : State} {sb fr pc mb mo cb co cap n row col to R : Nat} {cl : Color}
    {t : PieceType} {cp iz : Bool} {L : List (List UInt8)} (hR : R < 9) (hto : to < 256)
    (hbuf : Buf s.mem mb mo cb co cap L) (hf : Fresh s.mem n) (h64 : n + 4 < 2 ^ 64)
    (hsb : s.mem sb = some (srcBytes fr pc cl t row col cp iz)) (hfr : fr < 256) (hpc : pc < 256)
    (hsb0 : sb ≠ 0) (hsbm : sb ≠ mb) (hsbc : sb ≠ cb) (hro : s.ro = false)
    (a1 : s.locals 1 = some (.ptr sb 0)) (a10 : s.locals 10 = some (u8 to))
    (a7 : s.locals 7 = some (i32 (R : Int))) (a4 : s.locals 4 = some (.ptr mb mo))
    (a5 : s.locals 5 = some (.ptr cb co)) (a6 : s.locals 6 = some (.int IntTy.u64 cap)) :
    ∃ s', ExS Gen.prog s (.call none 23 [(.var 1), (.var 10), (.var 7), (.var 4), (.var 5), (.var 6)])
        .normal s' ∧ s'.locals = s.locals ∧ s'.ro = s.ro ∧
      Buf s'.mem mb mo cb co cap (L ++ (promoC cl t R cp iz).map (nmBytes fr to pc)) ∧
      Fresh s'.mem (n + 2 * (promoC cl t R cp iz).length) ∧ Frame s.mem s'.mem mb cb ∧
      s'.mem sb = s.mem sb := by
  obtain ⟨sN, hN, hbN, hfN, hfrN, hsbN⟩ := add_normal_move_spec (to := to) (r := R) hR hbuf hf h64 hsb hfr hpc
    hto hsb0 hsbm hsbc
  refine ⟨{ s with mem := sN.mem }, ?_, rfl, rfl, hbN, hfN, hfrN, hsbN⟩
  refine ExS.call (vs := [.ptr sb 0, .int IntTy.u8 to, i32 (R : Int), .ptr mb mo, .ptr cb co,
    .int IntTy.u64 cap]) ?_ rfl rfl ?_ (Or.inl rfl)
  · exact EvArgs.cons (EvE.var a1) (EvArgs.cons (EvE.var a10) (EvArgs.cons (EvE.var a7)
      (EvArgs.cons (EvE.var a4) (EvArgs.cons (EvE.var a5) (EvArgs.cons (EvE.var a6) EvArgs.nil)))))
  · rw [hro]; exact hN

section slide
variable (p : Position) (sb fr pc mb mo cb co cap row col : Nat) (cl : Color) (t : PieceType)
  (cp iz : Bool) (dr dc : Int)

/-- The loop invariant of `add_slide`. -/
structure SlideInv (s : State) (r c : Int) (L : List (List UInt8)) (n : Nat) : Prop where
  l0 : s.locals 0 = some posPtr
  l1 : s.locals 1 = some (.ptr sb 0)
  l2 : s.locals 2 = some (i32 dr)
  l3 : s.locals 3 = some (i32 dc)
  l4 : s.locals 4 = some (.ptr mb mo)
  l5 : s.locals 5 = some (.ptr cb co)
  l6 : s.locals 6 = some (.int IntTy.u64 cap)
  l7 : s.locals 7 = some (i32 r)
  l8 : s.locals 8 = some (i32 c)
  ro : s.ro = false
  hm : s.mem posBlock = some (encode p)
  hsb : s.mem sb = some (srcBytes fr pc cl t row col cp iz)
  buf : Buf s.mem mb mo cb co cap L
  fresh : Fresh s.mem n

end slide

section loop
variable {p : Position} {sb fr pc mb mo cb co cap row col : Nat} {cl : Color} {t : PieceType}
  {cp iz : Bool} {dr dc : Int}

theorem shift_ray (r dr : Int) (j : Nat) (hj : 1 ≤ j) : (r + dr) + ((j - 1 : Nat) : Int) * dr = r + (j : Int) * dr := by
  rw [Int.ofNat_sub hj, Int.sub_mul]; simp; omega

def slideS5 (p : Position) (s : State) (d : Square) : State :=
  { s with locals := ((((s.locals.upd 9 (bool8 true)).upd 11 (u8 d.val)).upd 10 (u8 d.val)).upd 12
      (.int IntTy.u8 (pieceByte (p.pieceAt d)).toNat)) }

/-- On a board square: `on_board`, `square_at` and the target load. -/
theorem slide_prefix {s : State} {r c : Int} {L : List (List UInt8)} {n : Nat}
    (hI : SlideInv p sb fr pc mb mo cb co cap row col cl t cp iz dr dc s r c L n) {d : Square}
    (hsq : Square.mk? r c = some d) (hr : -1 ≤ r ∧ r ≤ 9) (hc : -1 ≤ c ∧ c ≤ 9) :
    ∀ {o s'}, ExS Gen.prog (slideS5 p s d) (.seq slideTgt slideCall) o s' → ExS Gen.prog s slideBody o s' := by
  intro o s' hX
  have hdv := d.isLt
  obtain ⟨hin, hdeq⟩ : (0 ≤ r ∧ r < 9 ∧ 0 ≤ c ∧ c < 9) ∧ d.val = (r * 9 + c).toNat := by
    unfold Square.mk? at hsq; split at hsq
    · next h => simp only [Option.some.injEq] at hsq; subst hsq; exact ⟨h, rfl⟩
    · cases hsq
  have hob : run Gen.fid_on_board [i32 r, i32 c] = some (some (bool8 true)) := by
    have := on_board_refines ⟨(r + 9).toNat, by omega⟩ ⟨(c + 9).toNat, by omega⟩
    simp only at this
    rw [show ((r + 9).toNat : Int) - 9 = r by omega, show ((c + 9).toNat : Int) - 9 = c by omega, hsq] at this
    exact this
  let s3 : State := { s with locals := s.locals.upd 9 (bool8 true) }
  have e3 : ExS Gen.prog s (.call (some 9) 9 [(.var 7), (.var 8)]) .normal s3 :=
    call_pure rfl rfl rfl rfl hob (EvArgs.cons (EvE.var hI.l7) (EvArgs.cons (EvE.var hI.l8) EvArgs.nil))
  let R := r.toNat
  let C := c.toNat
  have hsqa : run Gen.fid_square_at [i32 r, i32 c] = some (some (u8 d.val)) := by
    rw [show r = ((R : Nat) : Int) by omega, show c = ((C : Nat) : Int) by omega,
      show d.val = R * 9 + C by omega]
    exact square_at_refines ⟨R, by omega⟩ ⟨C, by omega⟩
  let s4a : State := { s3 with locals := s3.locals.upd 11 (u8 d.val) }
  let s4 : State := { s4a with locals := s4a.locals.upd 10 (u8 d.val) }
  have e4 : ExS Gen.prog s3 slideSq .normal s4 :=
    ExS.seq (call_pure rfl rfl rfl rfl hsqa (EvArgs.cons (EvE.var (by simp [s3, Locals.upd]; exact hI.l7))
      (EvArgs.cons (EvE.var (by simp [s3, Locals.upd]; exact hI.l8)) EvArgs.nil)))
      (ExS.set (EvE.var (by simp [s4a, Locals.upd])))
  have hlen : (encode p).length = 114 := by simp [encode, Gen.off_side, Gen.off_king_square, le32]
  have hrd := readBoard hI.hm d.val hdv
  have e5 : ExS Gen.prog s4 slideLd .normal (slideS5 p s d) := by
    refine ExS.set (EvE.load (pa := .ptr posBlock (0 + 0 + d.val * 1)) (EvE.index (pb := .ptr posBlock (0 + 0))
      (EvE.field (EvE.var (v := posPtr) (by simp [s4, s4a, s3, Locals.upd]; exact hI.l0))
        (by simp [ptrAddN, posPtr, s4, s4a, s3, hI.hm, hlen]))
      (EvE.var (v := .int IntTy.u8 d.val) (by simp [s4, Locals.upd]; rfl)) ?_) ?_)
    · simp [IntTy.u8, ptrAddN, s4, s4a, s3, hI.hm, hlen]; omega
    · simp only [load, Ty.size, IntTy.bytes, show (8 : Nat) / 8 = 1 by rfl, s4, s4a, s3]
      simp [hrd, Res.bind, decodeLE]; rfl
  exact ExS.seq e3 (ExS.ite (bc := true) (EvE.var (by simp [s3, Locals.upd]; rfl)) rfl
    (ExS.seq e4 (ExS.seq e5 hX)))

theorem slide_off {s : State} {r c : Int} {L : List (List UInt8)} {n : Nat}
    (hI : SlideInv p sb fr pc mb mo cb co cap row col cl t cp iz dr dc s r c L n)
    (hsq : Square.mk? r c = none) (hr : -9 ≤ r ∧ r < 18) (hc : -9 ≤ c ∧ c < 18) :
    ExS Gen.prog s slideBody .brk { s with locals := s.locals.upd 9 (bool8 false) } := by
  have hob : run Gen.fid_on_board [i32 r, i32 c] = some (some (bool8 false)) := by
    have := on_board_refines ⟨(r + 9).toNat, by omega⟩ ⟨(c + 9).toNat, by omega⟩
    simp only at this
    rw [show ((r + 9).toNat : Int) - 9 = r by omega, show ((c + 9).toNat : Int) - 9 = c by omega, hsq] at this
    exact this
  exact ExS.seq (call_pure rfl rfl rfl rfl hob (EvArgs.cons (EvE.var hI.l7) (EvArgs.cons (EvE.var hI.l8) EvArgs.nil)))
    (ExS.ite (bc := false) (EvE.var (by simp [Locals.upd]; rfl)) rfl ExS.brk)

/-- Locals preserved by one iteration's scratch writes. -/
theorem SlideInv.locals {s s' : State} {r c : Int} {L : List (List UInt8)} {n : Nat}
    (hI : SlideInv p sb fr pc mb mo cb co cap row col cl t cp iz dr dc s r c L n)
    (hl : ∀ x, x ≤ 8 → s'.locals x = s.locals x) (hro : s'.ro = false)
    (hm : s'.mem posBlock = some (encode p)) (hsb : s'.mem sb = some (srcBytes fr pc cl t row col cp iz))
    {L' : List (List UInt8)} {n' : Nat} (hb : Buf s'.mem mb mo cb co cap L') (hf : Fresh s'.mem n') :
    SlideInv p sb fr pc mb mo cb co cap row col cl t cp iz dr dc s' r c L' n' :=
  ⟨by rw [hl 0 (by omega)]; exact hI.l0, by rw [hl 1 (by omega)]; exact hI.l1, by rw [hl 2 (by omega)]; exact hI.l2,
   by rw [hl 3 (by omega)]; exact hI.l3, by rw [hl 4 (by omega)]; exact hI.l4, by rw [hl 5 (by omega)]; exact hI.l5,
   by rw [hl 6 (by omega)]; exact hI.l6, by rw [hl 7 (by omega)]; exact hI.l7, by rw [hl 8 (by omega)]; exact hI.l8,
   hro, hm, hsb, hb, hf⟩

theorem slide_step {s : State} {r c : Int} {L : List (List UInt8)} {n : Nat}
    (hI : SlideInv p sb fr pc mb mo cb co cap row col cl t cp iz dr dc s r c L n)
    (hr : -9 ≤ r ∧ r < 18) (hc : -9 ≤ c ∧ c < 18) (hdr : -1 ≤ dr ∧ dr ≤ 1) (hdc : -1 ≤ dc ∧ dc ≤ 1) :
    ExS Gen.prog s slideStep .normal
      { s with locals := (s.locals.upd 7 (i32 (r + dr))).upd 8 (i32 (c + dc)) } := by
  refine ExS.seq (ExS.set (EvE.cast (EvE.bin (EvE.cast (EvE.var hI.l7) (cast_i32 r (by omega) (by omega)))
    (EvE.cast (EvE.var hI.l2) (cast_i32 dr (by omega) (by omega)))
    (add_i32 r dr (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)))
    (cast_i32 _ (by omega) (by omega)))) ?_
  exact ExS.set (EvE.cast (EvE.bin (EvE.cast (EvE.var (by simp [Locals.upd]; exact hI.l8)) (cast_i32 c (by omega) (by omega)))
    (EvE.cast (EvE.var (by simp [Locals.upd]; exact hI.l3)) (cast_i32 dc (by omega) (by omega)))
    (add_i32 c dc (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)))
    (cast_i32 _ (by omega) (by omega)))

theorem promoC_length (c : Color) (t : PieceType) (r : Nat) (cp iz : Bool) :
    (promoC c t r cp iz).length ≤ 2 := by
  unfold promoC; split
  · simp
  · split <;> simp

theorem Frame.pos {m m' : Mem} {mb cb : Nat} (h : Frame m m' mb cb) (hpm : posBlock ≠ mb)
    (hpc : posBlock ≠ cb) {blk : Block} (hm : m posBlock = some blk) : m' posBlock = some blk := by
  rw [h posBlock (by decide) hpm hpc (by rw [hm]; simp)]; exact hm

theorem slide_loop (hdr : -1 ≤ dr ∧ dr ≤ 1) (hdc : -1 ≤ dc ∧ dc ≤ 1) (hfr : fr < 256) (hpc : pc < 256)
    (hsb0 : sb ≠ 0) (hsbm : sb ≠ mb) (hsbc : sb ≠ cb) (hpm : posBlock ≠ mb) (hpc' : posBlock ≠ cb) :
    ∀ (k : Nat) (s : State) (r c : Int) (L : List (List UInt8)) (n : Nat),
      SlideInv p sb fr pc mb mo cb co cap row col cl t cp iz dr dc s r c L n →
      (-1 ≤ r ∧ r ≤ 9) → (-1 ≤ c ∧ c ≤ 9) →
      (∃ j : Nat, j ≤ k ∧ Square.mk? (r + j * dr) (c + j * dc) = none) → n + 4 * k < 2 ^ 64 →
      ∃ s', ExS Gen.prog s (.loop slideBody slideStep) .normal s' ∧
        Buf s'.mem mb mo cb co cap (L ++ slideC p cl t fr pc cp iz dr dc k r c) ∧
        Fresh s'.mem (n + 2 * (slideC p cl t fr pc cp iz dr dc k r c).length) ∧ Frame s.mem s'.mem mb cb := by
  intro k
  induction k with
  | zero =>
    intro s r c L n hI hr hc ⟨j, hj, hjn⟩ _
    have hj0 : j = 0 := by omega
    subst hj0
    simp at hjn
    exact ⟨_, ExS.loop_brk (slide_off hI hjn (by omega) (by omega)), by simpa [slideC] using hI.buf,
      by simpa [slideC] using hI.fresh, Frame.refl _ _ _⟩
  | succ k ih =>
    intro s r c L n hI hr hc ⟨j, hj, hjn⟩ h64
    cases hsq : Square.mk? r c with
    | none =>
      exact ⟨_, ExS.loop_brk (slide_off hI hsq (by omega) (by omega)), by simpa [slideC, hsq] using hI.buf,
        by simpa [slideC, hsq] using hI.fresh, Frame.refl _ _ _⟩
    | some d =>
      have hj1 : 1 ≤ j := by
        rcases Nat.eq_zero_or_pos j with h | h
        · subst h; simp at hjn; rw [hsq] at hjn; cases hjn
        · exact h
      obtain ⟨hin, hdeq⟩ : (0 ≤ r ∧ r < 9 ∧ 0 ≤ c ∧ c < 9) ∧ d.val = (r * 9 + c).toNat := by
        unfold Square.mk? at hsq; split at hsq
        · next h => simp only [Option.some.injEq] at hsq; subst hsq; exact ⟨h, rfl⟩
        · cases hsq
      have hdrow : d.row = r.toNat := by simp only [Square.row]; omega
      have hR : i32 r = i32 ((d.row : Nat) : Int) := by rw [hdrow]; congr 1; omega
      have hpre : ∀ {o s'}, ExS Gen.prog (slideS5 p s d) (.seq slideTgt slideCall) o s' →
          ExS Gen.prog s slideBody o s' := fun h => slide_prefix hI hsq hr hc h
      let s5 := slideS5 p s d
      have l5 : ∀ x, x ≤ 8 → s5.locals x = s.locals x := by
        intro x hx; simp [s5, slideS5, Locals.upd, show x ≠ 9 by omega, show x ≠ 10 by omega,
          show x ≠ 11 by omega, show x ≠ 12 by omega]
      have l10 : s5.locals 10 = some (u8 d.val) := by simp [s5, slideS5, Locals.upd]
      have l12 : s5.locals 12 = some (.int IntTy.u8 (pieceByte (p.pieceAt d)).toNat) := by
        simp [s5, slideS5, Locals.upd]
      have l7R : s5.locals 7 = some (i32 ((d.row : Nat) : Int)) := by rw [l5 7 (by omega), hI.l7, hR]
      have hbt := UInt8.toNat_lt (pieceByte (p.pieceAt d))
      cases hq : p.pieceAt d with
      | none =>
        have hbt0 : (pieceByte (p.pieceAt d)).toNat = 0 := by rw [hq]; rfl
        have eT : ExS Gen.prog s5 slideTgt .normal s5 :=
          ExS.ite (bc := false) (ev_ne0 hbt l12) (by rw [hbt0]; rfl) ExS.skip
        have hb5 : Buf s5.mem mb mo cb co cap L := hI.buf
        have hf5 : Fresh s5.mem n := hI.fresh
        obtain ⟨s6, e6, hl6, hro6, hb6, hf6, hfr6, hsb6⟩ := ncall_spec (s := s5) (R := d.row)
          (by simp [Square.row]; omega) (by omega) hb5 hf5 (by omega) hI.hsb hfr hpc hsb0 hsbm hsbc hI.ro
          (by rw [l5 1 (by omega)]; exact hI.l1) l10 l7R (by rw [l5 4 (by omega)]; exact hI.l4)
          (by rw [l5 5 (by omega)]; exact hI.l5) (by rw [l5 6 (by omega)]; exact hI.l6)
        let emit := (promoC cl t d.row cp iz).map (nmBytes fr d.val pc)
        have hI6 : SlideInv p sb fr pc mb mo cb co cap row col cl t cp iz dr dc s6 r c (L ++ emit)
            (n + 2 * (promoC cl t d.row cp iz).length) :=
          hI.locals (fun x hx => by rw [hl6]; exact l5 x hx) (by rw [hro6]; exact hI.ro)
            (hfr6.pos hpm hpc' hI.hm) (by rw [hsb6]; exact hI.hsb) hb6 hf6
        have e7 := slide_step hI6 (by omega) (by omega) hdr hdc
        let s7 : State := { s6 with locals := (s6.locals.upd 7 (i32 (r + dr))).upd 8 (i32 (c + dc)) }
        have hI7 : SlideInv p sb fr pc mb mo cb co cap row col cl t cp iz dr dc s7 (r + dr) (c + dc) (L ++ emit)
            (n + 2 * (promoC cl t d.row cp iz).length) :=
          ⟨by simp [s7, Locals.upd]; exact hI6.l0, by simp [s7, Locals.upd]; exact hI6.l1,
           by simp [s7, Locals.upd]; exact hI6.l2, by simp [s7, Locals.upd]; exact hI6.l3,
           by simp [s7, Locals.upd]; exact hI6.l4, by simp [s7, Locals.upd]; exact hI6.l5,
           by simp [s7, Locals.upd]; exact hI6.l6, by simp [s7, Locals.upd], by simp [s7, Locals.upd],
           hI6.ro, hI6.hm, hI6.hsb, hI6.buf, hI6.fresh⟩
        have hlen2 := promoC_length cl t d.row cp iz
        obtain ⟨s', e8, hb', hf', hfr'⟩ := ih s7 (r + dr) (c + dc) (L ++ emit) _ hI7 (by omega) (by omega)
          ⟨j - 1, by omega, by rw [shift_ray r dr j hj1, shift_ray c dc j hj1]; exact hjn⟩ (by omega)
        have hout : slideC p cl t fr pc cp iz dr dc (k + 1) r c = emit ++ slideC p cl t fr pc cp iz dr dc k (r + dr) (c + dc) := by
          simp [slideC, hsq, hq, emit]
        refine ⟨s', ExS.loop_next (hpre (ExS.seq eT e6)) (Or.inl rfl) e7 e8, ?_, ?_, ?_⟩
        · rw [hout, ← List.append_assoc]; exact hb'
        · rw [hout, List.length_append]
          have : emit.length = (promoC cl t d.row cp iz).length := by simp [emit]
          rw [this]; rw [show n + 2 * ((promoC cl t d.row cp iz).length + (slideC p cl t fr pc cp iz dr dc k (r + dr) (c + dc)).length)
            = n + 2 * (promoC cl t d.row cp iz).length + 2 * (slideC p cl t fr pc cp iz dr dc k (r + dr) (c + dc)).length by omega]
          exact hf'
        · exact Frame.trans hfr6 hfr'
      | some q =>
        have hbtq : (pieceByte (p.pieceAt d)).toNat = q.code := by rw [hq, pieceByte_toNat]
        have hcode1 : q.code ≠ 0 := by obtain ⟨qc, qt⟩ := q; cases qc <;> cases qt <;> decide
        have l12q : s5.locals 12 = some (.int IntTy.u8 (pieceByte (p.pieceAt d)).toNat) := l12
        have hpcol : run Gen.fid_shogi_piece_color [u8 (pieceByte (p.pieceAt d)).toNat]
            = some (some (u32 q.color.idx)) := by
          have := shogi_piece_color_total ⟨_, hbt⟩
          simp only at this; rw [this]
          have hb : (pieceByte (p.pieceAt d)).toNat / 16 % 2 = q.color.idx := by rw [hbtq]; exact byte_color q
          rw [hb]; obtain ⟨qc, qt⟩ := q; cases qc <;> rfl
        have hptyp : run Gen.fid_shogi_piece_type [u8 (pieceByte (p.pieceAt d)).toNat]
            = some (some (u32 q.type.code)) := by
          have := shogi_piece_type_total ⟨_, hbt⟩
          simp only at this; rw [this]
          have hb : (pieceByte (p.pieceAt d)).toNat % 16 = q.type.code := by rw [hbtq]; exact byte_type q
          rw [hb]
        have hci : q.color.idx < 2 := by cases q.color <;> decide
        have htc : q.type.code < 16 := by cases q.type <;> decide
        have hcl : cl.idx < 2 := by cases cl <;> decide
        let s6 : State := { s5 with locals := s5.locals.upd 13 (u32 q.color.idx) }
        have e6 : ExS Gen.prog s5 (.call (some 13) 1 [(.var 12)]) .normal s6 :=
          call_pure rfl rfl rfl rfl hpcol (EvArgs.cons (EvE.var l12) EvArgs.nil)
        have hsrc6 : EvE Gen.prog s6 (.cast ⟨32, false⟩ (.load (.int ⟨32, false⟩) (.field (.var 1) 4)))
            (.int IntTy.u32 cl.idx) := by
          have := load_u32_field (s := s6) (i := 4)
            (by simp [s6, Locals.upd]; rw [l5 1 (by omega)]; exact hI.l1) hI.hsb (by simp [srcBytes_length])
          rw [src_color] at this
          exact EvE.cast this (by simp [evalCast, IntTy.u32, IntTy.modulus,
            Nat.mod_eq_of_lt (show cl.idx < 4294967296 by omega)])
        have hcolE : EvE Gen.prog s6 (.bin .ne (some ⟨32, false⟩) (.cast ⟨32, false⟩ (.var 13))
            (.cast ⟨32, false⟩ (.load (.int ⟨32, false⟩) (.field (.var 1) 4))))
            (boolVal (decide (q.color.idx ≠ cl.idx))) :=
          ev_ne_u32 (cast_u32_var (by omega) (by simp [s6, Locals.upd]; rfl)) hsrc6
        have hout0 : slideC p cl t fr pc cp iz dr dc (k + 1) r c =
            if q.color != cl && q.type != .king then (promoC cl t d.row cp iz).map (nmBytes fr d.val pc) else [] := by
          simp [slideC, hsq, hq]
        by_cases hdiff : q.color.idx ≠ cl.idx
        · have hcne : (q.color != cl) = true := by
            cases hqc : q.color <;> cases cl <;> simp_all [Color.idx]
          let s7 : State := { s6 with locals := ((s6.locals.upd 14 (u32 q.type.code)).upd 15
              (boolVal (decide (q.type.code ≠ 8)))) }
          have e7 : ExS Gen.prog s6 (.ite (.bin .ne (some ⟨32, false⟩) (.cast ⟨32, false⟩ (.var 13))
              (.cast ⟨32, false⟩ (.load (.int ⟨32, false⟩) (.field (.var 1) 4)))) (.seq (.call (some 14) 2
              [(.var 12)]) (.set 15 (.land (.const (.int ⟨32, true⟩ 1)) (.bin .ne (some ⟨32, false⟩)
              (.cast ⟨32, false⟩ (.var 14)) (.cast ⟨32, false⟩ (.const (.int ⟨32, true⟩ 8)))))))
              (.set 15 (.const (.int ⟨32, true⟩ 0)))) .normal s7 :=
            ExS.ite (bc := true) hcolE (by simp [truthy_boolVal, hdiff])
              (ExS.seq (call_pure rfl rfl rfl rfl hptyp (EvArgs.cons (EvE.var (by simp [s6, Locals.upd]; exact l12))
                EvArgs.nil))
                (ExS.set (ev_land_ne (cast_u32_var (by omega) (by simp [Locals.upd]; rfl))
                  (EvE.cast (EvE.const _) rfl))))
          have l15 : s7.locals 15 = some (boolVal (decide (q.type.code ≠ 8))) := by simp [s7, Locals.upd]
          by_cases hnk : q.type.code ≠ 8
          · have hnk' : (q.type != PieceType.king) = true := by
              cases hqt : q.type <;> simp_all [PieceType.code]
            have hb7 : Buf s7.mem mb mo cb co cap L := hI.buf
            have hf7 : Fresh s7.mem n := hI.fresh
            have l7 : ∀ x, x ≤ 8 → s7.locals x = s.locals x := by
              intro x hx; simp [s7, s6, Locals.upd, show x ≠ 13 by omega, show x ≠ 14 by omega,
                show x ≠ 15 by omega]; exact l5 x hx
            obtain ⟨s8, e8, _, _, hb8, hf8, hfr8, _⟩ := ncall_spec (s := s7) (R := d.row) (to := d.val)
              (by simp [Square.row]; omega) (by omega) hb7 hf7 (by omega) hI.hsb hfr hpc hsb0 hsbm hsbc hI.ro
              (by rw [l7 1 (by omega)]; exact hI.l1) (by simp [s7, s6, Locals.upd]; exact l10)
              (by rw [l7 7 (by omega), hI.l7, hR]) (by rw [l7 4 (by omega)]; exact hI.l4)
              (by rw [l7 5 (by omega)]; exact hI.l5) (by rw [l7 6 (by omega)]; exact hI.l6)
            have eT : ExS Gen.prog s5 slideTgt .brk s8 :=
              ExS.ite (bc := true) (ev_ne0 hbt l12) (by simp [truthy_boolVal, hbtq, hcode1])
                (ExS.seq (ExS.seq e6 (ExS.seq e7 (ExS.ite (bc := true) (EvE.var l15)
                  (by simp [truthy_boolVal, hnk]) e8))) ExS.brk)
            refine ⟨s8, ExS.loop_brk (hpre (ExS.seq_brk eT)), ?_, ?_, hfr8⟩
            · rw [hout0, hcne, hnk']; exact hb8
            · rw [hout0, hcne, hnk']; simpa using hf8
          · have hk' : (q.type != PieceType.king) = false := by
              have : q.type.code = 8 := by omega
              cases hqt : q.type <;> simp_all [PieceType.code]
            have eT : ExS Gen.prog s5 slideTgt .brk s7 :=
              ExS.ite (bc := true) (ev_ne0 hbt l12) (by simp [truthy_boolVal, hbtq, hcode1])
                (ExS.seq (ExS.seq e6 (ExS.seq e7 (ExS.ite (bc := false) (EvE.var l15)
                  (by simp [truthy_boolVal, hnk]) ExS.skip))) ExS.brk)
            refine ⟨s7, ExS.loop_brk (hpre (ExS.seq_brk eT)), ?_, ?_, Frame.refl _ _ _⟩
            · rw [hout0, hcne, hk']; simpa [s7, s6, s5, slideS5] using hI.buf
            · rw [hout0, hcne, hk']; simpa [s7, s6, s5, slideS5] using hI.fresh
        · have hceq : (q.color != cl) = false := by
            cases hqc : q.color <;> cases cl <;> simp_all [Color.idx]
          let s7 : State := { s6 with locals := s6.locals.upd 15 (.int IntTy.i32 0) }
          have eT : ExS Gen.prog s5 slideTgt .brk s7 :=
            ExS.ite (bc := true) (ev_ne0 hbt l12) (by simp [truthy_boolVal, hbtq, hcode1])
              (ExS.seq (ExS.seq e6 (ExS.seq (ExS.ite (bc := false) hcolE
                (by simp [truthy_boolVal, hdiff]) (ExS.set (EvE.const _)))
                (ExS.ite (bc := false) (EvE.var (v := .int IntTy.i32 0) (by simp [s7, Locals.upd]; rfl)) rfl
                  ExS.skip))) ExS.brk)
          refine ⟨s7, ExS.loop_brk (hpre (ExS.seq_brk eT)), ?_, ?_, Frame.refl _ _ _⟩
          · rw [hout0, hceq]; simpa [s7, s6, s5, slideS5] using hI.buf
          · rw [hout0, hceq]; simpa [s7, s6, s5, slideS5] using hI.fresh

theorem add_slide_spec (hrow : row < 9) (hcol : col < 9) (hdr : -1 ≤ dr ∧ dr ≤ 1) (hdc : -1 ≤ dc ∧ dc ≤ 1)
    (hd0 : dr ≠ 0 ∨ dc ≠ 0) {m : Mem} {L : List (List UInt8)} {n : Nat}
    (hbuf : Buf m mb mo cb co cap L) (hf : Fresh m n) (h64 : n + 36 < 2 ^ 64)
    (hsb : m sb = some (srcBytes fr pc cl t row col cp iz)) (hfr : fr < 256) (hpc : pc < 256)
    (hm : m posBlock = some (encode p))
    (hsb0 : sb ≠ 0) (hsbm : sb ≠ mb) (hsbc : sb ≠ cb) (hpm : posBlock ≠ mb) (hpc' : posBlock ≠ cb) :
    ∃ s', ExS Gen.prog ⟨frameLocals Gen.add_slide.params
        [posPtr, .ptr sb 0, i32 dr, i32 dc, .ptr mb mo, .ptr cb co, .int IntTy.u64 cap], m, false⟩
      Gen.add_slide.body .normal s' ∧
      Buf s'.mem mb mo cb co cap (L ++ slideC p cl t fr pc cp iz dr dc 9 (row + dr) (col + dc)) ∧
      Fresh s'.mem (n + 2 * (slideC p cl t fr pc cp iz dr dc 9 (row + dr) (col + dc)).length) ∧
      Frame m s'.mem mb cb := by
  let s0 : State := ⟨frameLocals Gen.add_slide.params
    [posPtr, .ptr sb 0, i32 dr, i32 dc, .ptr mb mo, .ptr cb co, .int IntTy.u64 cap], m, false⟩
  have l1 : s0.locals 1 = some (.ptr sb 0) := rfl
  have hR : EvE Gen.prog s0 (.load (.int ⟨32, true⟩) (.field (.var 1) 12)) (i32 (row : Int)) := by
    have := load_i32_field (i := 12) l1 hsb (by simp [srcBytes_length])
    rw [src_row, decode_le32 row (by omega)] at this
    rw [i32_nat row (by omega)]; exact this
  let s1 : State := { s0 with locals := s0.locals.upd 7 (i32 ((row : Int) + dr)) }
  have hC : EvE Gen.prog s1 (.load (.int ⟨32, true⟩) (.field (.var 1) 16)) (i32 (col : Int)) := by
    have := load_i32_field (s := s1) (i := 16) (show s1.locals 1 = some (.ptr sb 0) from rfl) hsb
      (by simp [srcBytes_length])
    rw [src_col, decode_le32 col (by omega)] at this
    rw [i32_nat col (by omega)]; exact this
  let s2 : State := { s1 with locals := s1.locals.upd 8 (i32 ((col : Int) + dc)) }
  have e12 : ExS Gen.prog s0 (.seq (.set 7 (.bin .add (some ⟨32, true⟩) (.load (.int ⟨32, true⟩)
      (.field (.var 1) 12)) (.var 2))) (.set 8 (.bin .add (some ⟨32, true⟩) (.load (.int ⟨32, true⟩)
      (.field (.var 1) 16)) (.var 3)))) .normal s2 :=
    ExS.seq (ExS.set (EvE.bin hR (EvE.var rfl) (add_i32 _ _ (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega))))
      (ExS.set (EvE.bin hC (EvE.var rfl) (add_i32 _ _ (by omega) (by omega) (by omega) (by omega)
        (by omega) (by omega))))
  have hI : SlideInv p sb fr pc mb mo cb co cap row col cl t cp iz dr dc s2 (row + dr) (col + dc) L n :=
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, by simp [s2, s1, Locals.upd], by simp [s2, Locals.upd],
     rfl, hm, hsb, hbuf, hf⟩
  have hexit : ∃ j : Nat, j ≤ 9 ∧ Square.mk? (((row : Int) + dr) + j * dr) (((col : Int) + dc) + j * dc) = none := by
    refine ⟨9, by omega, ?_⟩
    unfold Square.mk?
    rw [dif_neg]
    intro h
    rcases hd0 with h0 | h0 <;> omega
  obtain ⟨s', e, hb, hf', hfr⟩ := slide_loop hdr hdc hfr hpc hsb0 hsbm hsbc hpm hpc' 9 s2 _ _ L n hI
    (by omega) (by omega) hexit (by omega)
  exact ⟨s', ExS.seq e12 e, hb, hf', hfr⟩

end loop

end Shogi.C.Proofs
