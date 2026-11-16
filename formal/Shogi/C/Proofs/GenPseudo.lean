/-
  T7/T8: `generate_pseudo(position, moves, count, capacity)` generates the
  pseudo-legal moves of the side to move.
-/
import Shogi.C.Proofs.LegalLoop

namespace Shogi.C.Proofs
open MiniC Shogi Shogi.C

theorem generate_pseudo_wrap {p : Position} {m : Mem} {mb mo cb co cap n : Nat}
    {L : List (List UInt8)} (hbuf : Buf m mb mo cb co cap L) (hf : Fresh m n) (h64 : n + 4000000100 < 2 ^ 64)
    (hm : m posBlock = some (encode p)) (hpm : posBlock ≠ mb) (hpc : posBlock ≠ cb) :
    ∃ s' n', ExS Gen.prog ⟨frameLocals Gen.generate_pseudo.params
        [posPtr, .ptr mb mo, .ptr cb co, .int IntTy.u64 cap], m, false⟩
      Gen.generate_pseudo.body .normal s' ∧
      Buf s'.mem mb mo cb co cap (L ++ pseudoC p p.side) ∧ Fresh s'.mem n' ∧ n' ≤ n + 40000 ∧
      Frame m s'.mem mb cb := by
  obtain ⟨sg, n', eg, hb, hf', hn', hfr⟩ := generate_pseudo_spec (p := p) (c := p.side) hbuf hf (by omega) hm hpm hpc
  let s0 : State := ⟨frameLocals Gen.generate_pseudo.params [posPtr, .ptr mb mo, .ptr cb co, .int IntTy.u64 cap], m, false⟩
  have hside : EvE Gen.prog s0 (.load (.int ⟨32, false⟩) (.field (.var 0) 96)) (u32 p.side.idx) := by
    refine EvE.load (pa := .ptr posBlock 96) (EvE.field (EvE.var rfl) (by simp [s0, ptrAddN, posPtr, hm, encode_length])) ?_
    simp only [load, readBytes, s0, hm, encode_length, Ty.size, IntTy.bytes]
    rw [if_pos (by omega), encode_enc, enc_side]
    simp only [Res.bind_eq, Res.bind_ok, pure]
    rw [decode_le32 _ (by cases p.side <;> decide)]; rfl
  refine ⟨{ s0 with mem := sg.mem }, n', ExS.call (vs := [posPtr, u32 p.side.idx, .ptr mb mo, .ptr cb co,
    .int IntTy.u64 cap]) (EvArgs.cons (EvE.var rfl) (EvArgs.cons hside (EvArgs.cons (EvE.var rfl)
      (EvArgs.cons (EvE.var rfl) (EvArgs.cons (EvE.var rfl) EvArgs.nil))))) rfl rfl eg (Or.inl rfl), hb, hf', hn', hfr⟩

end Shogi.C.Proofs

namespace Shogi.C.Proofs

theorem perm_map_inv {α β : Type} [DecidableEq α] (f : α → β) :
    ∀ (l : List β) (L : List α), l.Perm (L.map f) → ∃ M : List α, M.Perm L ∧ l = M.map f := by
  intro l; induction l with
  | nil =>
    intro L h
    have : L.map f = [] := List.Perm.nil_eq h |>.symm
    have hL : L = [] := List.map_eq_nil_iff.mp this
    exact ⟨[], by rw [hL], rfl⟩
  | cons a l ih =>
    intro L h
    have ha : a ∈ L.map f := h.subset (by simp)
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp ha
    have hL : L.Perm (x :: L.erase x) := List.perm_cons_erase hx
    have h2 : (f x :: l).Perm (f x :: (L.erase x).map f) := h.trans (by simpa using hL.map f)
    obtain ⟨M', hM', rfl⟩ := ih (L.erase x) (List.Perm.cons_inv h2)
    exact ⟨x :: M', (hM'.cons x).trans hL.symm, rfl⟩

/-- The C's pseudo-move bytes are the bytes of a list of moves that is a
    permutation of the spec's `pseudoMoves`. -/
theorem pseudoC_moves (p : Position) (hw : ∀ i, p.hand p.side i < 256) :
    ∃ Ms : List Move, Ms.Perm p.pseudoMoves ∧ pseudoC p p.side = Ms.map (moveBytes p) :=
  perm_map_inv (moveBytes p) _ _ (pseudoC_spec p hw)

end Shogi.C.Proofs

namespace Shogi.C.Proofs

/-- Filtering any permutation of `pseudoMoves` with the spec's test gives the
    spec's legal moves, up to order. -/
theorem keepBytes_perm (p : Position) (fuel : Nat) {Ms : List Move} (h : Ms.Perm p.pseudoMoves) :
    (keepBytes p fuel Ms).Perm ((Position.legalAux (fuel + 1) p).map (moveBytes p)) := by
  have e : (Position.legalAux (fuel + 1) p).map (moveBytes p) = keepBytes p fuel p.pseudoMoves := by
    simp only [Position.legalAux, keepBytes]
    rw [map_filter_eq_filterMap]; rfl
  rw [e]; unfold keepBytes; exact h.filterMap _

end Shogi.C.Proofs

namespace Shogi.C.Proofs
open MiniC Shogi Shogi.C

theorem buf_empty {m : Mem} {mb cb : Nat} {R C : Block} (hm : m mb = some R) (hc : m cb = some C)
    (hR : 36000 ≤ R.length) (hC : C = encodeLE 8 0) (hne : mb ≠ cb) (h1 : mb ≠ 0) (h2 : cb ≠ 0) :
    Buf m mb 0 cb 0 7200 [] :=
  ⟨⟨C, hc, by simp [hC, encodeLE_length], by rw [hC]; simp [List.take_of_length_le, encodeLE_length]⟩,
    ⟨R, hm, by omega, by simp⟩, by simp, hne, h1, h2, by decide⟩

/-- The prologue of `generate_legal_mut_internal`: `pseudo` (7200 moves) and
    `pseudo_count = 0` are allocated, giving an empty move buffer. -/
theorem legal_prologue {s : State} {n : Nat} (hf : Fresh s.mem n) (h64 : n + 4000000100 < 2 ^ 64) (hro : s.ro = false) :
    ∃ s1 s', ExS Gen.prog s (.alloc 4 36000) .normal s1 ∧ ExS Gen.prog s1 (.seq (.alloc 5 8)
        (.store (.int ⟨64, false⟩) (.var 5) (.cast ⟨64, false⟩ (.const (.int ⟨32, true⟩ 0))))) .normal s' ∧
      Buf s'.mem n 0 (n + 1) 0 7200 [] ∧ Fresh s'.mem (n + 2) ∧
      s'.locals 4 = some (.ptr n 0) ∧ s'.locals 5 = some (.ptr (n + 1) 0) ∧
      (∀ x, x ≠ 4 → x ≠ 5 → s'.locals x = s.locals x) ∧ s'.ro = s.ro ∧
      (∀ b, b ≠ 0 → b ≠ n → b ≠ n + 1 → s'.mem b = s.mem b) := by
  have e1 := exec_alloc (hf.allocAt (by omega)) 4 36000
  have hf1 := hf.after_alloc (List.replicate 36000 0)
  generalize hR : List.replicate 36000 (0 : UInt8) = R at e1 hf1
  have hRl : R.length = 36000 := by rw [← hR, List.length_replicate]
  have e2 := exec_alloc (s := { s with mem := (s.mem.upd 0 (encodeLE 8 (n + 1))).upd n R, locals := s.locals.upd 4 (.ptr n 0) }) (hf1.allocAt (by omega)) 5 8
  have hf2 := hf1.after_alloc (List.replicate 8 0)
  generalize hM2 : (((s.mem.upd 0 (encodeLE 8 (n + 1))).upd n R).upd 0 (encodeLE 8 (n + 1 + 1))).upd (n + 1)
    (List.replicate 8 0) = M2 at e2 hf2
  have g1 : M2 (n + 1) = some (List.replicate 8 0) := by rw [← hM2]; exact Mem.upd_eq
  have gn : M2 n = some R := by
    rw [← hM2, Mem.upd_ne (by omega), Mem.upd_ne hf.2.1, Mem.upd_eq]
  have gb : ∀ b, b ≠ 0 → b ≠ n → b ≠ n + 1 → M2 b = s.mem b := fun b a c d => by
    rw [← hM2, Mem.upd_ne d, Mem.upd_ne a, Mem.upd_ne c, Mem.upd_ne a]
  let L2 := (s.locals.upd 4 (.ptr n 0)).upd 5 (.ptr (n + 1) 0)
  have es : ExS Gen.prog ⟨L2, M2, s.ro⟩ (.store (.int ⟨64, false⟩) (.var 5)
      (.cast ⟨64, false⟩ (.const (.int ⟨32, true⟩ 0)))) .normal ⟨L2, M2.write (n + 1) 0 (encodeLE 8 0), s.ro⟩ := by
    refine ExS.store (pa := .ptr (n + 1) 0) (v := .int ⟨64, false⟩ 0) (EvE.var (by simp [L2, Locals.upd])) (EvE_of_eval (n := 2) ?_) hro ?_
    · simp [evalExpr, evalCast, IntTy.wrap, IntTy.toInt, IntTy.modulus]
    · simp only [store, Ty.size, IntTy.bytes]
      exact writeBytes_ok g1 (by simp [encodeLE_length])
  refine ⟨_, _, e1, ExS.seq e2 es, ?_, ?_, by simp [L2, Locals.upd], by simp [L2, Locals.upd],
    fun x a b => by simp [L2, Locals.upd, a, b], rfl, fun b a c d => ?_⟩
  · refine buf_empty (R := R) (C := encodeLE 8 0) ?_ ?_ (by omega) rfl (by omega) hf.2.1 (by omega)
    · show (M2.write (n + 1) 0 _) n = _
      rw [Mem.write_ne (by omega)]; exact gn
    · show (M2.write (n + 1) 0 _) (n + 1) = _
      rw [Mem.write_eq g1]; simp [encodeLE_length]
  · refine ⟨?_, by omega, fun x hx => ?_⟩
    · show (M2.write (n + 1) 0 _) 0 = _
      rw [Mem.write_ne (by omega)]; exact hf2.1
    · show (M2.write (n + 1) 0 _) x = _
      rw [Mem.write_ne (by omega)]; exact hf2.2.2 x (by omega)
  · show (M2.write (n + 1) 0 _) b = _
    rw [Mem.write_ne d]; exact gb b a c d

/-- The `generate_pseudo(position, pseudo, &pseudo_count, 7200)` call of
    `generate_legal_mut_internal`. -/
theorem legal_call_pseudo {s : State} {p : Position} {mb cb n : Nat}
    (h0 : s.locals 0 = some posPtr) (h4 : s.locals 4 = some (.ptr mb 0)) (h5 : s.locals 5 = some (.ptr cb 0))
    (hb : Buf s.mem mb 0 cb 0 7200 []) (hf : Fresh s.mem n) (h64 : n + 4000000100 < 2 ^ 64)
    (hm : s.mem posBlock = some (encode p)) (hpm : posBlock ≠ mb) (hpc : posBlock ≠ cb) (hro : s.ro = false) :
    ∃ s' n', ExS Gen.prog s (.call none 28 [(.var 0), (.var 4), (.var 5),
        (.cast ⟨64, false⟩ (.const (.int ⟨32, true⟩ 7200)))]) .normal s' ∧
      s'.locals = s.locals ∧ s'.ro = s.ro ∧
      Buf s'.mem mb 0 cb 0 7200 (pseudoC p p.side) ∧ Fresh s'.mem n' ∧ n' ≤ n + 40000 ∧
      Frame s.mem s'.mem mb cb := by
  obtain ⟨sg, n', eg, hb', hf', hn', hfr⟩ := generate_pseudo_wrap (L := []) hb hf h64 hm hpm hpc
  have hc : EvE Gen.prog s (.cast ⟨64, false⟩ (.const (.int ⟨32, true⟩ 7200))) (.int IntTy.u64 7200) :=
    EvE_of_eval (n := 2) (by simp [evalExpr, evalCast, IntTy.wrap, IntTy.toInt, IntTy.modulus, IntTy.u64])
  refine ⟨{ s with mem := sg.mem }, n', ExS.call (vs := [posPtr, .ptr mb 0, .ptr cb 0, .int IntTy.u64 7200])
    (EvArgs.cons (EvE.var h0) (EvArgs.cons (EvE.var h4) (EvArgs.cons (EvE.var h5) (EvArgs.cons hc EvArgs.nil))))
    rfl rfl (by rw [hro]; exact eg) (Or.inl rfl), rfl, rfl, by simpa using hb', hf', hn', hfr⟩

/-- `count = 0` in `generate_legal_mut_internal`: with the caller's move
    array this starts the empty output buffer. -/
theorem legal_count_init {s : State} {n mb mo cap : Nat} {blk : Block} (hf : Fresh s.mem n)
    (h64 : n + 4000000100 < 2 ^ 64) (hro : s.ro = false) (hmb : s.mem mb = some blk) (hlen : mo + 5 * cap ≤ blk.length)
    (hmb0 : mb ≠ 0) (hcap : cap < 2 ^ 64) :
    ∃ s', ExS Gen.prog s (.seq (.alloc 6 8)
        (.store (.int ⟨64, false⟩) (.var 6) (.cast ⟨64, false⟩ (.const (.int ⟨32, true⟩ 0))))) .normal s' ∧
      Buf s'.mem mb mo n 0 cap [] ∧ Fresh s'.mem (n + 1) ∧ s'.locals 6 = some (.ptr n 0) ∧
      (∀ x, x ≠ 6 → s'.locals x = s.locals x) ∧ s'.ro = s.ro ∧
      (∀ b, b ≠ 0 → b ≠ n → s'.mem b = s.mem b) := by
  have e1 := exec_alloc (hf.allocAt (by omega)) 6 8
  have hf1 := hf.after_alloc (List.replicate 8 0)
  generalize hM : (s.mem.upd 0 (encodeLE 8 (n + 1))).upd n (List.replicate 8 0) = M at e1 hf1
  have g1 : M n = some (List.replicate 8 0) := by rw [← hM]; exact Mem.upd_eq
  have gb : ∀ b, b ≠ 0 → b ≠ n → M b = s.mem b := fun b a c => by rw [← hM, Mem.upd_ne c, Mem.upd_ne a]
  have hmbn : mb ≠ n := fun e => by have := hf.2.2 n (Nat.le_refl _); rw [← e, hmb] at this; simp at this
  let L1 := s.locals.upd 6 (.ptr n 0)
  have es : ExS Gen.prog ⟨L1, M, s.ro⟩ (.store (.int ⟨64, false⟩) (.var 6)
      (.cast ⟨64, false⟩ (.const (.int ⟨32, true⟩ 0)))) .normal ⟨L1, M.write n 0 (encodeLE 8 0), s.ro⟩ := by
    refine ExS.store (pa := .ptr n 0) (v := .int ⟨64, false⟩ 0) (EvE.var (by simp [L1, Locals.upd]))
      (EvE_of_eval (n := 2) ?_) hro ?_
    · simp [evalExpr, evalCast, IntTy.wrap, IntTy.toInt, IntTy.modulus]
    · simp only [store, Ty.size, IntTy.bytes]
      exact writeBytes_ok g1 (by simp [encodeLE_length])
  refine ⟨_, ExS.seq e1 es, ?_, ?_, by simp [L1, Locals.upd], fun x a => by simp [L1, Locals.upd, a], rfl,
    fun b a c => ?_⟩
  · refine ⟨⟨encodeLE 8 0, ?_, by simp [encodeLE_length], by simp [List.take_of_length_le, encodeLE_length]⟩,
      ⟨blk, ?_, hlen, by simp⟩, by simp, hmbn, hmb0, hf.2.1, hcap⟩
    · show (M.write n 0 _) n = _
      rw [Mem.write_eq g1]; simp [encodeLE_length]
    · show (M.write n 0 _) mb = _
      rw [Mem.write_ne hmbn, gb mb hmb0 hmbn]; exact hmb
  · refine ⟨?_, by omega, fun x hx => ?_⟩
    · show (M.write n 0 _) 0 = _
      rw [Mem.write_ne hf.2.1.symm]; exact hf1.1
    · show (M.write n 0 _) x = _
      rw [Mem.write_ne (by omega)]; exact hf1.2.2 x hx
  · show (M.write n 0 _) b = _
    rw [Mem.write_ne c]; exact gb b a c

/-- `mover = position->side_to_move; king_safety_prepare(&safety, position, mover)`
    in `generate_legal_mut_internal`. -/
theorem legal_safety {s : State} {p : Position} {n : Nat} (h0 : s.locals 0 = some posPtr)
    (hm : s.mem posBlock = some (encode p)) (ht : TablesIn s.mem) (hf : Fresh s.mem n) (h64 : n + 4000000100 < 2 ^ 64)
    (hro : s.ro = false) :
    ∃ s1 s', ExS Gen.prog s (.set 7 (.load (.int ⟨32, false⟩) (.field (.var 0) 96))) .normal s1 ∧
      ExS Gen.prog s1 (.seq (.alloc 8 84) (.call none 31 [(.var 8), (.var 0), (.var 7)])) .normal s' ∧
      s'.mem n = some (ksRec p p.side) ∧ s'.locals 7 = some (u32 p.side.idx) ∧
      s'.locals 8 = some (.ptr n 0) ∧ (∀ x, x ≠ 7 → x ≠ 8 → s'.locals x = s.locals x) ∧ s'.ro = s.ro ∧
      (∀ b, b ≠ 0 → b ≠ n → b ≠ n + 1 → s'.mem b = s.mem b) ∧ Fresh s'.mem (n + 2) := by
  have hside : EvE Gen.prog s (.load (.int ⟨32, false⟩) (.field (.var 0) 96)) (u32 p.side.idx) := by
    refine EvE.load (pa := .ptr posBlock 96) (EvE.field (EvE.var h0) (by simp [ptrAddN, posPtr, hm, encode_length])) ?_
    simp only [load, readBytes, hm, encode_length, Ty.size, IntTy.bytes]
    rw [if_pos (by omega), encode_enc, enc_side]
    simp only [Res.bind_eq, Res.bind_ok, pure]
    rw [decode_le32 _ (by cases p.side <;> decide)]; rfl
  let s1 : State := { s with locals := s.locals.upd 7 (u32 p.side.idx) }
  have e1 : ExS Gen.prog s (.set 7 (.load (.int ⟨32, false⟩) (.field (.var 0) 96))) .normal s1 := ExS.set hside
  have e2 := exec_alloc (s := s1) (hf.allocAt (by omega)) 8 84
  have hn0 := hf.2.1
  have hnp : n ≠ posBlock := fun e => by rw [← e, hf.2.2 n (Nat.le_refl _)] at hm; cases hm
  have hgn : ∀ g, s.mem g ≠ none → g ≠ n := fun g hg e => by rw [e, hf.2.2 n (Nat.le_refl _)] at hg; exact hg rfl
  generalize hM : (s1.mem.upd 0 (encodeLE 8 (n + 1))).upd n (List.replicate 84 0) = M at e2
  have hMg : ∀ g, g ≠ 0 → g ≠ n → M g = s.mem g := fun g a c => by rw [← hM, Mem.upd_ne c, Mem.upd_ne a]
  have hMn : M n = some (List.replicate 84 0) := by rw [← hM]; exact Mem.upd_eq
  have hf1 : Fresh M (n + 1) := by rw [← hM]; exact hf.after_alloc _
  have hmM : M posBlock = some (encode p) := by rw [hMg _ (by decide) (Ne.symm hnp)]; exact hm
  have tg : ∀ g, 8192 ≤ g → g ≤ 8196 → M g = s.mem g := fun g a b => hMg g (by omega)
    (hgn g (by
      rcases (show g = 8192 ∨ g = 8193 ∨ g = 8194 ∨ g = 8195 ∨ g = 8196 by omega) with h | h | h | h | h <;>
        subst h <;> simp [ht.g1, ht.g2, ht.g3, ht.g4, ht.g5]))
  obtain ⟨sk, ek, hk, hkf, hk0⟩ := king_safety_spec p p.side hmM hMn (by simp) (by rw [tg _ (by decide) (by decide)]; exact ht.g1)
    (by rw [tg _ (by decide) (by decide)]; exact ht.g2) (by rw [tg _ (by decide) (by decide)]; exact ht.g3)
    (by rw [tg _ (by decide) (by decide)]; exact ht.g4) (by rw [tg _ (by decide) (by decide)]; exact ht.g5)
    hf1 (by omega) hn0 hnp
  let s2 : State := { s1 with mem := M, locals := s1.locals.upd 8 (.ptr n 0) }
  have h7 : s2.locals 7 = some (u32 p.side.idx) := by simp [s2, s1, Locals.upd]
  refine ⟨_, { s2 with mem := sk.mem }, e1, (ExS.seq e2 (ExS.call (vs := [.ptr n 0, posPtr, u32 p.side.idx])
    (EvArgs.cons (EvE.var (by simp [s2, Locals.upd])) (EvArgs.cons (EvE.var (by simp [s2, s1, Locals.upd, h0]))
      (EvArgs.cons (EvE.var h7) EvArgs.nil))) rfl rfl (by simp only [s2, s1]; rw [hro]; exact ek) (Or.inr rfl))),
    hk, h7, by simp [s2, Locals.upd], fun x a b => by simp [s2, s1, Locals.upd, a, b], rfl, fun b a c d => ?_,
    hk0, by omega, fun x hx => ?_⟩
  · show sk.mem b = _
    rw [hkf b a d c, hMg b a c]
  · show sk.mem x = _
    rw [hkf x (by omega) (by omega) (by omega), hMg x (by omega) (by omega)]; exact hf.2.2 x (by omega)

/-- `return count;` in `generate_legal_mut_internal` returns the number of
    stored moves. -/
theorem legal_return {s : State} {mb mo cb cap : Nat} {L : List (List UInt8)}
    (h6 : s.locals 6 = some (.ptr cb 0)) (hb : Buf s.mem mb mo cb 0 cap L) :
    EvE Gen.prog s (.load (.int ⟨64, false⟩) (.var 6)) (.int ⟨64, false⟩ (min L.length cap)) := by
  obtain ⟨cblk, hc, hl, ht⟩ := hb.cnt
  refine EvE.load (EvE.var h6) ?_
  have hr : readBytes s.mem cb 0 8 = .ok (encodeLE 8 (min L.length cap)) := by
    simp only [readBytes, hc]; rw [if_pos (by omega)]; simpa using congrArg Res.ok ht
  simp only [load, Ty.size, IntTy.bytes, show (64 : Nat) / 8 = 8 by rfl, hr]
  have := hb.cap64
  simp [Res.bind, pure]; exact decode_encode8 _ (by omega)

/-- `index = 0` before the legality loop. -/
theorem legal_index_init (s : State) :
    ExS Gen.prog s (.set 9 (.cast ⟨64, false⟩ (.const (.int ⟨32, true⟩ 0)))) .normal
      { s with locals := s.locals.upd 9 (.int IntTy.u64 0) } :=
  ExS.set (EvE_of_eval (n := 3) (by simp [evalExpr, evalCast, IntTy.u64, IntTy.toInt, IntTy.wrap, IntTy.modulus,
    Res.bind]))

theorem flatten5_get : ∀ (L : List (List UInt8)), (∀ x ∈ L, x.length = 5) →
    ∀ j (hj : j < L.length), (L.flatten.drop (5 * j)).take 5 = L[j]
  | [], _, j, hj => absurd hj (by simp)
  | x :: L, h, 0, _ => by
    simp only [List.flatten_cons, Nat.mul_zero, List.drop_zero, List.getElem_cons_zero]
    rw [List.take_append_of_le_length (by rw [h x (by simp)]; omega)]
    exact List.take_of_length_le (by rw [h x (by simp)]; omega)
  | x :: L, h, j + 1, hj => by
    simp only [List.flatten_cons, List.getElem_cons_succ]
    rw [show 5 * (j + 1) = x.length + 5 * j by rw [h x (by simp)]; omega, ← List.drop_drop,
      List.drop_left]
    exact flatten5_get L (fun y hy => h y (by simp [hy])) j (by simp at hj; omega)

/-- From the pseudo buffer filled with `Ms` (no truncation), the facts the
    legality loop reads: the count and the bytes of each move. -/
theorem buf_bridge {m : Mem} {mb cb : Nat} {p : Position} {Ms : List Move}
    (hb : Buf m mb 0 cb 0 7200 (Ms.map (moveBytes p))) (h600 : Ms.length ≤ 7200) :
    readBytes m cb 0 8 = .ok (encodeLE 8 Ms.length) ∧
    ∃ PB, m mb = some PB ∧ 5 * Ms.length ≤ PB.length ∧
      ∀ j (hj : j < Ms.length), (PB.drop (5 * j)).take 5 = moveBytes p Ms[j] := by
  obtain ⟨cblk, hc, hl, ht⟩ := hb.cnt
  obtain ⟨blk, hm, hbl, hbt⟩ := hb.buf
  simp only [List.length_map, Nat.min_eq_left h600, List.drop_zero] at ht hbt
  refine ⟨by simp only [readBytes, hc]; rw [if_pos (by omega)]; simpa using congrArg Res.ok ht, blk, hm, by omega,
    fun j hj => ?_⟩
  have hlen : ∀ x ∈ Ms.map (moveBytes p), x.length = 5 := hb.len
  have e : (blk.drop (5 * j)).take 5 = ((blk.take (5 * Ms.length)).drop (5 * j)).take 5 := by
    rw [List.drop_take, List.take_take]; congr 1; omega
  have h6 : (Ms.map (moveBytes p)).take 7200 = Ms.map (moveBytes p) := List.take_of_length_le (by simp; omega)
  rw [h6] at hbt
  rw [e, hbt, flatten5_get _ hlen j (by simpa using hj)]; simp

theorem TablesIn.of_eq {m m' : Mem} (h : TablesIn m) (he : ∀ g, 8192 ≤ g → g ≤ 8196 → m' g = m g) :
    TablesIn m' :=
  ⟨by rw [he _ (by decide) (by decide)]; exact h.g1, by rw [he _ (by decide) (by decide)]; exact h.g2,
    by rw [he _ (by decide) (by decide)]; exact h.g3, by rw [he _ (by decide) (by decide)]; exact h.g4,
    by rw [he _ (by decide) (by decide)]; exact h.g5⟩

/-- The tables survive any step whose frame excludes only blocks outside them. -/
theorem TablesIn.of_frame {m m' : Mem} {mb cb : Nat} (h : TablesIn m) (hf : Frame m m' mb cb)
    (hmb : mb < 8192 ∨ 8196 < mb) (hcb : cb < 8192 ∨ 8196 < cb) : TablesIn m' :=
  h.of_eq fun g a b => hf g (by omega) (by omega) (by omega) (by
    rcases (show g = 8192 ∨ g = 8193 ∨ g = 8194 ∨ g = 8195 ∨ g = 8196 by omega) with e | e | e | e | e <;>
      subst e <;> simp [h.g1, h.g2, h.g3, h.g4, h.g5])

end Shogi.C.Proofs
