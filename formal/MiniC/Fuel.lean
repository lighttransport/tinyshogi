/-
  Fuel monotonicity of the MiniC interpreter: once a run does not time out,
  more fuel gives the same result. With it, a single evaluation of
  `execStmt`/`callFunc` (e.g. by the kernel, `decide`) establishes the
  relational judgements `ExS`/`EvE` of `MiniC.Logic`, which quantify over all
  sufficiently large fuel.

  (tinyshogi addition; not part of the tinygltf original.)
-/
import MiniC.Logic

namespace MiniC

/-- `a` is a fuel-approximation of `b`: it timed out, or it is `b`. -/
def Res.Le {α} (a b : Res α) : Prop := a = .timeout ∨ a = b

theorem Res.Le.refl {α} (a : Res α) : Res.Le a a := Or.inr rfl

theorem Res.Le.bind {α β} {x x' : Res α} {f f' : α → Res β}
    (hx : Res.Le x x') (hf : ∀ a, Res.Le (f a) (f' a)) :
    Res.Le (x >>= f) (x' >>= f') := by
  rcases hx with h | h
  · subst h; exact Or.inl rfl
  · subst h
    cases x with
    | ok a => exact hf a
    | ub => exact Or.inr rfl
    | timeout => exact Or.inl rfl

section
variable (p : Prog)

theorem fuel_mono_step : ∀ n : Nat,
    (∀ s e, Res.Le (evalExpr p n s e) (evalExpr p (n + 1) s e)) ∧
    (∀ s es, Res.Le (evalArgs p n s es) (evalArgs p (n + 1) s es)) ∧
    (∀ s st, Res.Le (execStmt p n s st) (execStmt p (n + 1) s st)) := by
  intro n
  induction n with
  | zero =>
    refine ⟨?_, ?_, ?_⟩ <;> intros <;> exact Or.inl (by simp [evalExpr, evalArgs, execStmt])
  | succ n ih =>
    obtain ⟨ihe, iha, ihs⟩ := ih
    refine ⟨?_, ?_, ?_⟩
    · intro s e
      rw [evalExpr.eq_def p (n + 1), evalExpr.eq_def p (n + 1 + 1)]
      try simp only
      cases e <;> (try simp only) <;>
        repeat (first
          | exact Res.Le.refl _
          | apply Res.Le.bind
          | apply ihe | apply iha | apply ihs
          | intro _
          | split)
    · intro s es
      rw [evalArgs.eq_def p (n + 1), evalArgs.eq_def p (n + 1 + 1)]
      try simp only
      cases es <;> (try simp only) <;>
        repeat (first
          | exact Res.Le.refl _
          | apply Res.Le.bind
          | apply ihe | apply iha | apply ihs
          | intro _)
    · intro s st
      rw [execStmt.eq_def p (n + 1), execStmt.eq_def p (n + 1 + 1)]
      try simp only
      cases st <;> (try simp only) <;>
        repeat (first
          | exact Res.Le.refl _
          | apply Res.Le.bind
          | apply ihe | apply iha | apply ihs
          | intro _
          | split)
theorem execStmt_mono {s st} {n : Nat} (h : execStmt p n s st ≠ .timeout) :
    ∀ k, n ≤ k → execStmt p k s st = execStmt p n s st := by
  intro k hk
  obtain ⟨d, rfl⟩ : ∃ d, k = n + d := ⟨k - n, by omega⟩
  clear hk
  induction d with
  | zero => rfl
  | succ d ih =>
    rw [← Nat.add_assoc]
    rcases (fuel_mono_step p (n + d)).2.2 s st with h' | h'
    · rw [ih] at h'; exact absurd h' h
    · rw [← h', ih]

/-- One successful evaluation gives the relational judgement. -/
theorem ExS_of_execStmt {s st o s'} {n : Nat} (h : execStmt p n s st = .ok (o, s')) :
    ExS p s st o s' := by
  refine ⟨n, fun k hk => ?_⟩
  rw [execStmt_mono p (by rw [h]; intro e; cases e) k hk, h]

/-- Result value of a call (`none` for UB or time-out). -/
def retOf : Res (Option Val × Mem) → Option (Option Val)
  | .ok (v, _) => some v
  | _ => none

theorem callFunc_mono {f args m} {n : Nat} (h : retOf (callFunc p n f args m) = some v) :
    ∀ k, n ≤ k → retOf (callFunc p k f args m) = some v := by
  intro k hk
  unfold callFunc at *
  split at h
  · simp [retOf] at h
  · rename_i fn hf
    try simp only [hf]
    split at h
    · rename_i hl
      rw [if_pos hl]
      have hne : execStmt p n ⟨frameLocals fn.params args, m, false⟩ fn.body ≠ .timeout := by
        intro e; rw [e] at h; simp [retOf] at h
      rw [execStmt_mono p hne k hk]
      exact h
    · simp [retOf] at h
end
end MiniC
