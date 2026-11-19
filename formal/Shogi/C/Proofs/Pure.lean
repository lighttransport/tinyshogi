/-
  Memory independence of pure expressions: an expression built only from
  constants, locals and arithmetic evaluates the same in every memory. Used
  to lift the kernel-checked helper refinements (`Helpers.lean`, run in the
  empty memory) to the memories the generators run in.
-/
import Shogi.C.Proofs.Helpers
import MiniC.Logic

namespace Shogi.C.Proofs
variable {posBlock : Nat}
open MiniC

def pureE : Expr → Bool
  | .const _ | .var _ => true
  | .bin _ _ a b | .land a b | .lor a b => pureE a && pureE b
  | .un _ _ a | .cast _ a => pureE a
  | .cond c a b => pureE c && pureE a && pureE b
  | _ => false

theorem evalExpr_pure (p : Prog) : ∀ (n : Nat) (e : Expr) (l : Locals) (m m' : Mem) (ro ro' : Bool),
    pureE e = true → evalExpr p n ⟨l, m, ro⟩ e = evalExpr p n ⟨l, m', ro'⟩ e := by
  intro n
  induction n with
  | zero => intro e l m m' ro ro' _; simp [evalExpr]
  | succ n ih =>
    intro e l m m' ro ro' h
    cases e with
    | const v => simp [evalExpr]
    | var i => simp [evalExpr]
    | bin op t a b =>
      simp only [pureE, Bool.and_eq_true] at h
      simp only [evalExpr, ih a l m m' ro ro' h.1, ih b l m m' ro ro' h.2]
    | un op t a => simp only [pureE] at h; simp only [evalExpr, ih a l m m' ro ro' h]
    | cast t a => simp only [pureE] at h; simp only [evalExpr, ih a l m m' ro ro' h]
    | land a b =>
      simp only [pureE, Bool.and_eq_true] at h
      simp only [evalExpr, ih a l m m' ro ro' h.1, ih b l m m' ro ro' h.2]
    | lor a b =>
      simp only [pureE, Bool.and_eq_true] at h
      simp only [evalExpr, ih a l m m' ro ro' h.1, ih b l m m' ro ro' h.2]
    | cond c a b =>
      simp only [pureE, Bool.and_eq_true] at h
      simp only [evalExpr, ih c l m m' ro ro' h.1.1, ih a l m m' ro ro' h.1.2, ih b l m m' ro ro' h.2]
    | _ => simp [pureE] at h

/-- A helper whose body is `return e;` with `e` pure, refined in the empty
    memory, returns the same value in any memory and leaves it unchanged. -/
theorem pure_ret {f : Nat} {fn : Func} {e : Expr} {args : List Val} {v : Val}
    (hf : Gen.prog f = some fn) (hb : fn.body = .ret (some e)) (hp : pureE e = true)
    (hlen : fn.params.length = args.length) (hrun : run f args = some (some v)) (m : Mem) (ro : Bool) :
    ExS Gen.prog ⟨frameLocals fn.params args, m, ro⟩ fn.body (.ret (some v))
      ⟨frameLocals fn.params args, m, ro⟩ := by
  have h63 : evalExpr Gen.prog 63 ⟨frameLocals fn.params args, m0, false⟩ e = .ok v := by
    unfold run callFunc at hrun
    rw [hf] at hrun; simp only [hlen, ite_true, hb] at hrun
    cases h : evalExpr Gen.prog 63 ⟨frameLocals fn.params args, m0, false⟩ e <;>
      simp [execStmt, h, Res.bind, retOf] at hrun
    rw [hrun]
  rw [hb]
  refine ExS.ret (EvE_of_eval (n := 63) ?_)
  rw [evalExpr_pure Gen.prog 63 e _ m m0 ro false hp]; exact h63

end Shogi.C.Proofs

namespace Shogi.C.Proofs
variable {posBlock : Nat}
open MiniC Shogi Shogi.C

/-- `if`/`return` trees over pure expressions. -/
def pureS : Stmt → Bool
  | .ret (some e) => pureE e
  | .ite c a b => pureE c && pureS a && pureS b
  | _ => false

theorem execStmt_pureS (p : Prog) : ∀ (n : Nat) (st : Stmt) (l : Locals) (m m' : Mem) (ro ro' : Bool)
    (o : Outcome) (s0 : State), pureS st = true →
    execStmt p n ⟨l, m, ro⟩ st = .ok (o, s0) → execStmt p n ⟨l, m', ro'⟩ st = .ok (o, ⟨l, m', ro'⟩) := by
  intro n
  induction n with
  | zero => intro st l m m' ro ro' o s0 _ h; simp [execStmt] at h
  | succ n ih =>
    intro st l m m' ro ro' o s0 h hx
    cases st with
    | ret oe =>
      cases oe with
      | none => simp [pureS] at h
      | some e =>
        simp only [pureS] at h
        simp only [execStmt] at hx ⊢
        rw [evalExpr_pure p n e l m' m ro' ro h]
        cases he : evalExpr p n ⟨l, m, ro⟩ e <;> simp_all [Res.bind, pure]
    | ite c a b =>
      simp only [pureS, Bool.and_eq_true] at h
      obtain ⟨⟨hc, ha⟩, hb⟩ := h
      simp only [execStmt] at hx ⊢
      rw [evalExpr_pure p n c l m' m ro' ro hc]
      cases hv : evalExpr p n ⟨l, m, ro⟩ c with
      | ok v =>
        rw [hv] at hx
        simp only [Res.bind_eq, Res.bind_ok] at hx ⊢
        cases ht : truthy v with
        | ok bc =>
          simp only [ht, Res.bind_ok] at hx ⊢
          cases bc
          · simp only [Bool.false_eq_true, ite_false] at hx ⊢; exact ih b l m m' ro ro' o s0 hb hx
          · simp only [ite_true] at hx ⊢; exact ih a l m m' ro ro' o s0 ha hx
        | _ => simp [Res.bind, ht] at hx
      | _ => rw [hv] at hx; simp [Res.bind] at hx
    | _ => simp [pureS] at h

/-- Calling a helper whose body is a pure `if`/`return` tree. -/
theorem pure_callS {f : Nat} {fn : Func} {args : List Val} {v : Val}
    (hf : Gen.prog f = some fn) (hp : pureS fn.body = true)
    (hlen : fn.params.length = args.length) (hrun : run f args = some (some v)) (m : Mem) (ro : Bool) :
    ExS Gen.prog ⟨frameLocals fn.params args, m, ro⟩ fn.body (.ret (some v))
      ⟨frameLocals fn.params args, m, ro⟩ := by
  unfold run callFunc at hrun
  rw [hf] at hrun; simp only [hlen, ite_true] at hrun
  cases h : execStmt Gen.prog 64 ⟨frameLocals fn.params args, m0, false⟩ fn.body with
  | ok r =>
    obtain ⟨o, s0⟩ := r
    rw [h] at hrun
    cases o <;> simp [retOf] at hrun
    rename_i ov
    cases ov <;> simp at hrun
    subst hrun
    exact ExS_of_execStmt (p := Gen.prog) (execStmt_pureS Gen.prog 64 fn.body _ m0 m false ro _ _ hp h)
  | _ => rw [h] at hrun; simp [retOf] at hrun

end Shogi.C.Proofs
