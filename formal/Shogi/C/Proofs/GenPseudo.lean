/-
  T7/T8: `generate_pseudo(position, moves, count, capacity)` generates the
  pseudo-legal moves of the side to move.
-/
import Shogi.C.Proofs.LegalLoop

namespace Shogi.C.Proofs
open MiniC Shogi Shogi.C

theorem generate_pseudo_wrap {p : Position} {m : Mem} {mb mo cb co cap n : Nat}
    {L : List (List UInt8)} (hbuf : Buf m mb mo cb co cap L) (hf : Fresh m n) (h64 : n + 40000 < 2 ^ 64)
    (hm : m posBlock = some (encode p)) (hpm : posBlock ≠ mb) (hpc : posBlock ≠ cb) :
    ∃ s' n', ExS Gen.prog ⟨frameLocals Gen.generate_pseudo.params
        [posPtr, .ptr mb mo, .ptr cb co, .int IntTy.u64 cap], m, false⟩
      Gen.generate_pseudo.body .normal s' ∧
      Buf s'.mem mb mo cb co cap (L ++ pseudoC p p.side) ∧ Fresh s'.mem n' ∧ n' ≤ n + 40000 ∧
      Frame m s'.mem mb cb := by
  obtain ⟨sg, n', eg, hb, hf', hn', hfr⟩ := generate_pseudo_spec (p := p) (c := p.side) hbuf hf h64 hm hpm hpc
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
    (hR : 3000 ≤ R.length) (hC : C = encodeLE 8 0) (hne : mb ≠ cb) (h1 : mb ≠ 0) (h2 : cb ≠ 0) :
    Buf m mb 0 cb 0 600 [] :=
  ⟨⟨C, hc, by simp [hC, encodeLE_length], by rw [hC]; simp [List.take_of_length_le, encodeLE_length]⟩,
    ⟨R, hm, by omega, by simp⟩, by simp, hne, h1, h2, by decide⟩

/-- The prologue of `generate_legal_mut_internal`: `pseudo` (600 moves) and
    `pseudo_count = 0` are allocated, giving an empty move buffer. -/
theorem legal_prologue {s : State} {n : Nat} (hf : Fresh s.mem n) (h64 : n + 2 < 2 ^ 64) (hro : s.ro = false) :
    ∃ s', ExS Gen.prog s (.seq (.alloc 4 3000) (.seq (.alloc 5 8)
        (.store (.int ⟨64, false⟩) (.var 5) (.cast ⟨64, false⟩ (.const (.int ⟨32, true⟩ 0)))))) .normal s' ∧
      Buf s'.mem n 0 (n + 1) 0 600 [] ∧ Fresh s'.mem (n + 2) ∧
      s'.locals 4 = some (.ptr n 0) ∧ s'.locals 5 = some (.ptr (n + 1) 0) ∧
      (∀ x, x ≠ 4 → x ≠ 5 → s'.locals x = s.locals x) ∧ s'.ro = s.ro ∧
      (∀ b, b ≠ 0 → b ≠ n → b ≠ n + 1 → s'.mem b = s.mem b) := by
  have e1 := exec_alloc (hf.allocAt (by omega)) 4 3000
  have hf1 := hf.after_alloc (List.replicate 3000 0)
  generalize hR : List.replicate 3000 (0 : UInt8) = R at e1 hf1
  have hRl : R.length = 3000 := by rw [← hR, List.length_replicate]
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
  refine ⟨_, ExS.seq e1 (ExS.seq e2 es), ?_, ?_, by simp [L2, Locals.upd], by simp [L2, Locals.upd],
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

end Shogi.C.Proofs
