/-
  T7 generators, layer 3: `generate_pseudo_for_color`, part 1 — one
  `add_step`/`add_slide` call and a chain of them (a `switch` case body).
-/
import Shogi.C.Proofs.DropsSpec

namespace Shogi.C.Proofs
variable {posBlock : Nat}
open MiniC Shogi Shogi.C

inductive Op where
  | step (dr dc : Int)
  | slide (dr dc : Int)

def Op.fid : Op → Nat
  | .step .. => 24
  | .slide .. => 25

def Op.dr : Op → Int
  | .step a _ | .slide a _ => a

def Op.dc : Op → Int
  | .step _ b | .slide _ b => b

def Op.ok : Op → Prop
  | .step dr dc => -2 ≤ dr ∧ dr ≤ 2 ∧ -2 ≤ dc ∧ dc ≤ 2
  | .slide dr dc => -1 ≤ dr ∧ dr ≤ 1 ∧ -1 ≤ dc ∧ dc ≤ 1 ∧ (dr ≠ 0 ∨ dc ≠ 0)

/-- Bytes one call appends. -/
def opOut (p : Position) (c : Color) (t : PieceType) (fr pc row col : Nat) (cp iz : Bool) : Op → List (List UInt8)
  | .step dr dc => stepOut p c t fr pc row col cp iz dr dc
  | .slide dr dc => slideC p c t fr pc cp iz dr dc 9 (row + dr) (col + dc)

def opCall (o : Op) (edr edc : Expr) : Stmt :=
  .call none o.fid [(.var 0), (.var 16), edr, edc, (.var 2), (.var 3), (.var 4)]

theorem op_call {s : State} {p : Position} {sb fr pc mb mo cb co cap n row col : Nat} {c : Color}
    {t : PieceType} {cp iz : Bool} {L : List (List UInt8)} (o : Op) {edr edc : Expr} (hok : o.ok)
    (hrow : row < 9) (hcol : col < 9)
    (hbuf : Buf s.mem mb mo cb co cap L) (hf : Fresh s.mem n) (h64 : n + 36 < 2 ^ 64)
    (hsb : s.mem sb = some (srcBytes fr pc c t row col cp iz)) (hfr : fr < 256) (hpc : pc < 256)
    (hm : s.mem posBlock = some (encode p))
    (hsb0 : sb ≠ 0) (hsbm : sb ≠ mb) (hsbc : sb ≠ cb) (hpm : posBlock ≠ mb) (hpc' : posBlock ≠ cb)
    (hro : s.ro = false)
    (a0 : s.locals 0 = some (posPtr' posBlock)) (a16 : s.locals 16 = some (.ptr sb 0))
    (hdr : EvE Gen.prog s edr (i32 o.dr)) (hdc : EvE Gen.prog s edc (i32 o.dc))
    (a2 : s.locals 2 = some (.ptr mb mo)) (a3 : s.locals 3 = some (.ptr cb co))
    (a4 : s.locals 4 = some (.int IntTy.u64 cap)) :
    ∃ s', ExS Gen.prog s (opCall o edr edc) .normal s' ∧ s'.locals = s.locals ∧ s'.ro = s.ro ∧
      Buf s'.mem mb mo cb co cap (L ++ opOut p c t fr pc row col cp iz o) ∧
      Fresh s'.mem (n + 2 * (opOut p c t fr pc row col cp iz o).length) ∧ Frame s.mem s'.mem mb cb := by
  have hargs : EvArgs Gen.prog s [(.var 0), (.var 16), edr, edc, (.var 2), (.var 3), (.var 4)]
      [posPtr' posBlock, .ptr sb 0, i32 o.dr, i32 o.dc, .ptr mb mo, .ptr cb co, .int IntTy.u64 cap] :=
    EvArgs.cons (EvE.var a0) (EvArgs.cons (EvE.var a16) (EvArgs.cons hdr (EvArgs.cons hdc
      (EvArgs.cons (EvE.var a2) (EvArgs.cons (EvE.var a3) (EvArgs.cons (EvE.var a4) EvArgs.nil))))))
  cases o with
  | step dr dc =>
    obtain ⟨h1, h2, h3, h4⟩ := hok
    obtain ⟨oc, s', e, ho, hb, hf', hfr⟩ := add_step_spec (p := p) (c := c) (t := t) (cp := cp) (iz := iz)
      (dr := dr) (dc := dc) hrow hcol ⟨h1, h2⟩ ⟨h3, h4⟩ hbuf hf (by omega) hsb hfr hpc hm hsb0 hsbm hsbc hpm hpc'
    refine ⟨{ s with mem := s'.mem }, ExS.call hargs rfl rfl (by rw [hro]; exact e) ho, rfl, rfl, hb, hf', hfr⟩
  | slide dr dc =>
    obtain ⟨h1, h2, h3, h4, h5⟩ := hok
    obtain ⟨s', e, hb, hf', hfr⟩ := add_slide_spec (p := p) (cl := c) (t := t) (cp := cp) (iz := iz)
      (dr := dr) (dc := dc) hrow hcol ⟨h1, h2⟩ ⟨h3, h4⟩ h5 hbuf hf h64 hsb hfr hpc hm hsb0 hsbm hsbc hpm hpc'
    refine ⟨{ s with mem := s'.mem }, ExS.call hargs rfl rfl (by rw [hro]; exact e) (Or.inl rfl), rfl, rfl,
      hb, hf', hfr⟩

theorem Frame.keep {m m' : Mem} {mb cb x : Nat} (h : Frame m m' mb cb) (h0 : x ≠ 0) (hm : x ≠ mb)
    (hc : x ≠ cb) {blk : Block} (hx : m x = some blk) : m' x = some blk := by
  rw [h x h0 hm hc (by rw [hx]; simp)]; exact hx

theorem slideC_length (p : Position) (c : Color) (t : PieceType) (fr pc : Nat) (cp iz : Bool) (dr dc : Int) :
    ∀ k r cc, (slideC p c t fr pc cp iz dr dc k r cc).length ≤ 2 * k := by
  intro k; induction k with
  | zero => intro _ _; simp [slideC]
  | succ k ih =>
    intro r cc; simp only [slideC]
    split
    · simp
    · split
      · have := ih (r + dr) (cc + dc); have := promoC_length c t ‹Square›.row cp iz
        simp only [List.length_append, List.length_map]; omega
      · split
        · have := promoC_length c t ‹Square›.row cp iz; simp only [List.length_map]; omega
        · simp

theorem opOut_length (p : Position) (c : Color) (t : PieceType) (fr pc row col : Nat) (cp iz : Bool) (o : Op) :
    (opOut p c t fr pc row col cp iz o).length ≤ 18 := by
  cases o with
  | step dr dc =>
    simp only [opOut, stepOut]
    split
    · simp
    · split
      · split
        · simp
        · have := promoC_length c t ‹Square›.row cp iz; simp only [List.length_map]; omega
      · have := promoC_length c t ‹Square›.row cp iz; simp only [List.length_map]; omega
  | slide dr dc => exact slideC_length p c t fr pc cp iz dr dc 9 _ _

def chainStmt : List (Op × Expr × Expr) → Stmt
  | [] => .brk
  | (o, a, b) :: r => .seq (opCall o a b) (chainStmt r)

def ArgsOk (l : Locals) (ops : List (Op × Expr × Expr)) : Prop :=
  ∀ x ∈ ops, x.1.ok ∧ ∀ s : State, s.locals = l → EvE Gen.prog s x.2.1 (i32 x.1.dr) ∧ EvE Gen.prog s x.2.2 (i32 x.1.dc)

theorem chain_spec {p : Position} {sb fr pc mb mo cb co cap row col : Nat} {c : Color}
    {t : PieceType} {cp iz : Bool} (hrow : row < 9) (hcol : col < 9) (hfr : fr < 256) (hpc : pc < 256)
    (hsb0 : sb ≠ 0) (hsbm : sb ≠ mb) (hsbc : sb ≠ cb) (hpm : posBlock ≠ mb) (hpc' : posBlock ≠ cb) :
    ∀ (ops : List (Op × Expr × Expr)) (s : State) (L : List (List UInt8)) (n : Nat),
      ArgsOk s.locals ops →
      Buf s.mem mb mo cb co cap L → Fresh s.mem n → n + 36 * ops.length < 2 ^ 64 →
      s.mem sb = some (srcBytes fr pc c t row col cp iz) → s.mem posBlock = some (encode p) → s.ro = false →
      s.locals 0 = some (posPtr' posBlock) → s.locals 16 = some (.ptr sb 0) →
      s.locals 2 = some (.ptr mb mo) → s.locals 3 = some (.ptr cb co) →
      s.locals 4 = some (.int IntTy.u64 cap) →
      ∃ s', ExS Gen.prog s (chainStmt ops) .brk s' ∧ s'.locals = s.locals ∧ s'.ro = s.ro ∧
        Buf s'.mem mb mo cb co cap (L ++ ops.flatMap (fun x => opOut p c t fr pc row col cp iz x.1)) ∧
        Fresh s'.mem (n + 2 * (ops.flatMap (fun x => opOut p c t fr pc row col cp iz x.1)).length) ∧
        Frame s.mem s'.mem mb cb := by
  intro ops
  induction ops with
  | nil =>
    intro s L n _ hb hf _ _ _ _ _ _ _ _ _
    exact ⟨s, ExS.brk, rfl, rfl, by simpa using hb, by simpa using hf, Frame.refl _ _ _⟩
  | cons x r ih =>
    intro s L n ha hb hf h64 hsb hm hro a0 a16 a2 a3 a4
    obtain ⟨o, ea, eb⟩ := x
    obtain ⟨hok, hev⟩ := ha (o, ea, eb) (by simp)
    obtain ⟨hda, hdb⟩ := hev s rfl
    obtain ⟨s1, e1, hl1, hro1, hb1, hf1, hfr1⟩ := op_call (p := p) o hok hrow hcol hb hf
      (by simp at h64; omega) hsb hfr hpc hm hsb0 hsbm hsbc hpm hpc' hro a0 a16 hda hdb a2 a3 a4
    have hlen := opOut_length p c t fr pc row col cp iz o
    obtain ⟨s', e', hl', hro', hb', hf', hfr'⟩ := ih s1 _ _
      (fun y hy => by rw [hl1]; exact ha y (by simp [hy])) hb1 hf1 (by simp at h64; omega)
      (hfr1.keep hsb0 hsbm hsbc hsb) (hfr1.pos hpm hpc' hm (posBlock_ne_zero hf.1 hm)) (by rw [hro1]; exact hro)
      (by rw [hl1]; exact a0) (by rw [hl1]; exact a16) (by rw [hl1]; exact a2) (by rw [hl1]; exact a3)
      (by rw [hl1]; exact a4)
    refine ⟨s', ExS.seq e1 e', by rw [hl', hl1], by rw [hro', hro1], ?_, ?_, Frame.trans hfr1 hfr'⟩
    · simpa [List.flatMap_cons, List.append_assoc] using hb'
    · simp only [List.flatMap_cons, List.length_append]
      rw [show n + 2 * ((opOut p c t fr pc row col cp iz o).length +
        (r.flatMap (fun x => opOut p c t fr pc row col cp iz x.1)).length) =
        n + 2 * (opOut p c t fr pc row col cp iz o).length +
        2 * (r.flatMap (fun x => opOut p c t fr pc row col cp iz x.1)).length by omega]
      exact hf'

end Shogi.C.Proofs
