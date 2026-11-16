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
