/-
  Statements that cannot write memory: no store, call, allocation, memcpy or
  memset. Running one leaves memory (and the read-only flag) unchanged.
-/
import MiniC.Logic

namespace Shogi.C.Proofs
open MiniC

def noWrite : Stmt → Bool
  | .skip | .set .. | .eval _ | .brk | .cont | .ret _ => true
  | .seq a b | .ite _ a b | .loop a b => noWrite a && noWrite b
  | _ => false

theorem exec_noWrite (p : Prog) : ∀ (n : Nat) (s : State) (st : Stmt) (o : Outcome) (s' : State),
    noWrite st = true → execStmt p n s st = .ok (o, s') → s'.mem = s.mem ∧ s'.ro = s.ro := by
  intro n
  induction n with
  | zero => intro s st o s' _ h; simp [execStmt] at h
  | succ n ih =>
    intro s st o s' hw h
    cases st with
    | skip => simp [execStmt] at h; obtain ⟨_, rfl⟩ := h; exact ⟨rfl, rfl⟩
    | set i e =>
      simp only [execStmt] at h
      cases he : evalExpr p n s e <;> simp_all [Res.bind, pure]
      all_goals (try (obtain ⟨_, rfl⟩ := h; exact ⟨rfl, rfl⟩))
    | eval e =>
      simp only [execStmt] at h
      cases he : evalExpr p n s e <;> simp_all [Res.bind, pure]
      all_goals (try (obtain ⟨_, rfl⟩ := h; exact ⟨rfl, rfl⟩))
    | brk => simp [execStmt] at h; obtain ⟨_, rfl⟩ := h; exact ⟨rfl, rfl⟩
    | cont => simp [execStmt] at h; obtain ⟨_, rfl⟩ := h; exact ⟨rfl, rfl⟩
    | ret oe =>
      cases oe with
      | none => simp [execStmt] at h; obtain ⟨_, rfl⟩ := h; exact ⟨rfl, rfl⟩
      | some e =>
        simp only [execStmt] at h
        cases he : evalExpr p n s e <;> simp_all [Res.bind, pure]
        all_goals (try (obtain ⟨_, rfl⟩ := h; exact ⟨rfl, rfl⟩))
    | seq a b =>
      simp only [noWrite, Bool.and_eq_true] at hw
      simp only [execStmt] at h
      cases ha : execStmt p n s a with
      | ok r =>
        obtain ⟨o1, s1⟩ := r
        rw [ha] at h
        obtain ⟨m1, r1⟩ := ih s a o1 s1 hw.1 ha
        cases o1 <;> simp [Res.bind, pure] at h
        · obtain ⟨m2, r2⟩ := ih s1 b o s' hw.2 h; exact ⟨m2.trans m1, r2.trans r1⟩
        all_goals (obtain ⟨_, rfl⟩ := h; exact ⟨m1, r1⟩)
      | _ => rw [ha] at h; simp [Res.bind] at h
    | ite c a b =>
      simp only [noWrite, Bool.and_eq_true] at hw
      simp only [execStmt] at h
      cases hc : evalExpr p n s c with
      | ok v =>
        rw [hc] at h
        simp only [Res.bind_eq, Res.bind_ok] at h
        cases ht : truthy v with
        | ok bc =>
          rw [ht] at h; simp only [Res.bind_ok] at h
          cases bc
          · exact ih s b o s' hw.2 (by simpa using h)
          · exact ih s a o s' hw.1 (by simpa using h)
        | _ => rw [ht] at h; simp [Res.bind] at h
      | _ => rw [hc] at h; simp [Res.bind] at h
    | loop body step =>
      have hw' := hw
      simp only [noWrite, Bool.and_eq_true] at hw
      simp only [execStmt] at h
      cases ha : execStmt p n s body with
      | ok r =>
        obtain ⟨o1, s1⟩ := r
        rw [ha] at h
        obtain ⟨m1, r1⟩ := ih s body o1 s1 hw.1 ha
        cases o1 with
        | brk => simp [Res.bind, pure] at h; obtain ⟨_, rfl⟩ := h; exact ⟨m1, r1⟩
        | ret v => simp [Res.bind, pure] at h; obtain ⟨_, rfl⟩ := h; exact ⟨m1, r1⟩
        | normal | cont =>
          simp only [Res.bind_eq, Res.bind_ok] at h
          cases hs : execStmt p n s1 step with
          | ok r2 =>
            obtain ⟨o2, s2⟩ := r2
            rw [hs] at h
            obtain ⟨m2, r2⟩ := ih s1 step o2 s2 hw.2 hs
            cases o2 <;> simp at h
            obtain ⟨m3, r3⟩ := ih s2 (.loop body step) o s' hw' h
            exact ⟨m3.trans (m2.trans m1), r3.trans (r2.trans r1)⟩
          | _ => rw [hs] at h; simp at h
      | _ => rw [ha] at h; simp [Res.bind] at h
    | _ => simp [noWrite] at hw

theorem ExS_noWrite {p : Prog} {s s' : State} {st : Stmt} {o : Outcome} (hw : noWrite st = true)
    (h : ExS p s st o s') : s'.mem = s.mem ∧ s'.ro = s.ro := by
  obtain ⟨K, hK⟩ := h
  exact exec_noWrite p K s st o s' hw (hK K (Nat.le_refl _))

end Shogi.C.Proofs
