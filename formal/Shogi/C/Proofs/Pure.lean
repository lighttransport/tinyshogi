/-
  Memory independence of pure expressions: an expression built only from
  constants, locals and arithmetic evaluates the same in every memory. Used
  to lift the kernel-checked helper refinements (`Helpers.lean`, run in the
  empty memory) to the memories the generators run in.
-/
import Shogi.C.Proofs.Helpers
import MiniC.Logic

namespace Shogi.C.Proofs
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
