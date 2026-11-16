/-
  T7 generators, layer 3: `generate_pseudo_for_color`, part 2 — the shape
  of the per-square body: the `switch` on the piece type as a case list.
-/
import Shogi.C.Proofs.Pseudo1

namespace Shogi.C.Proofs
open MiniC Shogi Shogi.C

def swCond (k : Nat) : Expr :=
  .bin .eq (some ⟨32, false⟩) (.cast ⟨32, false⟩ (.var 10)) (.const (.int ⟨32, false⟩ k))

def switchStmt : List (Nat × Stmt) → Stmt → Stmt
  | [], d => d
  | (k, b) :: r, d => .ite (swCond k) b (switchStmt r d)

def ops1 (f : Int) : List (Op × Expr × Expr) := [
  (.step (f) (0), (.var 5), (.const (.int ⟨32, true⟩ 0)))]
def ops2 (f : Int) : List (Op × Expr × Expr) := [
  (.slide (f) (0), (.var 5), (.const (.int ⟨32, true⟩ 0)))]
def ops3 (f : Int) : List (Op × Expr × Expr) := [
  (.step (2 * f) (-1), (.bin .mul (some ⟨32, true⟩) (.const (.int ⟨32, true⟩ 2)) (.var 5)), (.un .neg ⟨32, true⟩ (.const (.int ⟨32, true⟩ 1)))),
  (.step (2 * f) (1), (.bin .mul (some ⟨32, true⟩) (.const (.int ⟨32, true⟩ 2)) (.var 5)), (.const (.int ⟨32, true⟩ 1)))]
def ops4 (f : Int) : List (Op × Expr × Expr) := [
  (.step (f) (-1), (.var 5), (.un .neg ⟨32, true⟩ (.const (.int ⟨32, true⟩ 1)))),
  (.step (f) (0), (.var 5), (.const (.int ⟨32, true⟩ 0))),
  (.step (f) (1), (.var 5), (.const (.int ⟨32, true⟩ 1))),
  (.step (-f) (-1), (.un .neg ⟨32, true⟩ (.var 5)), (.un .neg ⟨32, true⟩ (.const (.int ⟨32, true⟩ 1)))),
  (.step (-f) (1), (.un .neg ⟨32, true⟩ (.var 5)), (.const (.int ⟨32, true⟩ 1)))]
def ops5 (f : Int) : List (Op × Expr × Expr) := [
  (.step (f) (-1), (.var 5), (.un .neg ⟨32, true⟩ (.const (.int ⟨32, true⟩ 1)))),
  (.step (f) (0), (.var 5), (.const (.int ⟨32, true⟩ 0))),
  (.step (f) (1), (.var 5), (.const (.int ⟨32, true⟩ 1))),
  (.step (0) (-1), (.const (.int ⟨32, true⟩ 0)), (.un .neg ⟨32, true⟩ (.const (.int ⟨32, true⟩ 1)))),
  (.step (0) (1), (.const (.int ⟨32, true⟩ 0)), (.const (.int ⟨32, true⟩ 1))),
  (.step (-f) (0), (.un .neg ⟨32, true⟩ (.var 5)), (.const (.int ⟨32, true⟩ 0)))]
def ops9 (f : Int) : List (Op × Expr × Expr) := [
  (.step (f) (-1), (.var 5), (.un .neg ⟨32, true⟩ (.const (.int ⟨32, true⟩ 1)))),
  (.step (f) (0), (.var 5), (.const (.int ⟨32, true⟩ 0))),
  (.step (f) (1), (.var 5), (.const (.int ⟨32, true⟩ 1))),
  (.step (0) (-1), (.const (.int ⟨32, true⟩ 0)), (.un .neg ⟨32, true⟩ (.const (.int ⟨32, true⟩ 1)))),
  (.step (0) (1), (.const (.int ⟨32, true⟩ 0)), (.const (.int ⟨32, true⟩ 1))),
  (.step (-f) (0), (.un .neg ⟨32, true⟩ (.var 5)), (.const (.int ⟨32, true⟩ 0)))]
def ops10 (f : Int) : List (Op × Expr × Expr) := [
  (.step (f) (-1), (.var 5), (.un .neg ⟨32, true⟩ (.const (.int ⟨32, true⟩ 1)))),
  (.step (f) (0), (.var 5), (.const (.int ⟨32, true⟩ 0))),
  (.step (f) (1), (.var 5), (.const (.int ⟨32, true⟩ 1))),
  (.step (0) (-1), (.const (.int ⟨32, true⟩ 0)), (.un .neg ⟨32, true⟩ (.const (.int ⟨32, true⟩ 1)))),
  (.step (0) (1), (.const (.int ⟨32, true⟩ 0)), (.const (.int ⟨32, true⟩ 1))),
  (.step (-f) (0), (.un .neg ⟨32, true⟩ (.var 5)), (.const (.int ⟨32, true⟩ 0)))]
def ops11 (f : Int) : List (Op × Expr × Expr) := [
  (.step (f) (-1), (.var 5), (.un .neg ⟨32, true⟩ (.const (.int ⟨32, true⟩ 1)))),
  (.step (f) (0), (.var 5), (.const (.int ⟨32, true⟩ 0))),
  (.step (f) (1), (.var 5), (.const (.int ⟨32, true⟩ 1))),
  (.step (0) (-1), (.const (.int ⟨32, true⟩ 0)), (.un .neg ⟨32, true⟩ (.const (.int ⟨32, true⟩ 1)))),
  (.step (0) (1), (.const (.int ⟨32, true⟩ 0)), (.const (.int ⟨32, true⟩ 1))),
  (.step (-f) (0), (.un .neg ⟨32, true⟩ (.var 5)), (.const (.int ⟨32, true⟩ 0)))]
def ops12 (f : Int) : List (Op × Expr × Expr) := [
  (.step (f) (-1), (.var 5), (.un .neg ⟨32, true⟩ (.const (.int ⟨32, true⟩ 1)))),
  (.step (f) (0), (.var 5), (.const (.int ⟨32, true⟩ 0))),
  (.step (f) (1), (.var 5), (.const (.int ⟨32, true⟩ 1))),
  (.step (0) (-1), (.const (.int ⟨32, true⟩ 0)), (.un .neg ⟨32, true⟩ (.const (.int ⟨32, true⟩ 1)))),
  (.step (0) (1), (.const (.int ⟨32, true⟩ 0)), (.const (.int ⟨32, true⟩ 1))),
  (.step (-f) (0), (.un .neg ⟨32, true⟩ (.var 5)), (.const (.int ⟨32, true⟩ 0)))]
def case8 : Stmt := (.seq (.seq (.set 19 (.un .neg ⟨32, true⟩ (.const (.int ⟨32, true⟩ 1)))) Gen.generate_pseudo_for_color_loop1) .brk)
def ops6 (f : Int) : List (Op × Expr × Expr) := [
  (.slide (-1) (-1), (.un .neg ⟨32, true⟩ (.const (.int ⟨32, true⟩ 1))), (.un .neg ⟨32, true⟩ (.const (.int ⟨32, true⟩ 1)))),
  (.slide (-1) (1), (.un .neg ⟨32, true⟩ (.const (.int ⟨32, true⟩ 1))), (.const (.int ⟨32, true⟩ 1))),
  (.slide (1) (-1), (.const (.int ⟨32, true⟩ 1)), (.un .neg ⟨32, true⟩ (.const (.int ⟨32, true⟩ 1)))),
  (.slide (1) (1), (.const (.int ⟨32, true⟩ 1)), (.const (.int ⟨32, true⟩ 1)))]
def ops7 (f : Int) : List (Op × Expr × Expr) := [
  (.slide (-1) (0), (.un .neg ⟨32, true⟩ (.const (.int ⟨32, true⟩ 1))), (.const (.int ⟨32, true⟩ 0))),
  (.slide (1) (0), (.const (.int ⟨32, true⟩ 1)), (.const (.int ⟨32, true⟩ 0))),
  (.slide (0) (-1), (.const (.int ⟨32, true⟩ 0)), (.un .neg ⟨32, true⟩ (.const (.int ⟨32, true⟩ 1)))),
  (.slide (0) (1), (.const (.int ⟨32, true⟩ 0)), (.const (.int ⟨32, true⟩ 1)))]
def ops13 (f : Int) : List (Op × Expr × Expr) := [
  (.slide (-1) (-1), (.un .neg ⟨32, true⟩ (.const (.int ⟨32, true⟩ 1))), (.un .neg ⟨32, true⟩ (.const (.int ⟨32, true⟩ 1)))),
  (.slide (-1) (1), (.un .neg ⟨32, true⟩ (.const (.int ⟨32, true⟩ 1))), (.const (.int ⟨32, true⟩ 1))),
  (.slide (1) (-1), (.const (.int ⟨32, true⟩ 1)), (.un .neg ⟨32, true⟩ (.const (.int ⟨32, true⟩ 1)))),
  (.slide (1) (1), (.const (.int ⟨32, true⟩ 1)), (.const (.int ⟨32, true⟩ 1))),
  (.step (-1) (0), (.un .neg ⟨32, true⟩ (.const (.int ⟨32, true⟩ 1))), (.const (.int ⟨32, true⟩ 0))),
  (.step (1) (0), (.const (.int ⟨32, true⟩ 1)), (.const (.int ⟨32, true⟩ 0))),
  (.step (0) (-1), (.const (.int ⟨32, true⟩ 0)), (.un .neg ⟨32, true⟩ (.const (.int ⟨32, true⟩ 1)))),
  (.step (0) (1), (.const (.int ⟨32, true⟩ 0)), (.const (.int ⟨32, true⟩ 1)))]
def ops14 (f : Int) : List (Op × Expr × Expr) := [
  (.slide (-1) (0), (.un .neg ⟨32, true⟩ (.const (.int ⟨32, true⟩ 1))), (.const (.int ⟨32, true⟩ 0))),
  (.slide (1) (0), (.const (.int ⟨32, true⟩ 1)), (.const (.int ⟨32, true⟩ 0))),
  (.slide (0) (-1), (.const (.int ⟨32, true⟩ 0)), (.un .neg ⟨32, true⟩ (.const (.int ⟨32, true⟩ 1)))),
  (.slide (0) (1), (.const (.int ⟨32, true⟩ 0)), (.const (.int ⟨32, true⟩ 1))),
  (.step (-1) (-1), (.un .neg ⟨32, true⟩ (.const (.int ⟨32, true⟩ 1))), (.un .neg ⟨32, true⟩ (.const (.int ⟨32, true⟩ 1)))),
  (.step (-1) (1), (.un .neg ⟨32, true⟩ (.const (.int ⟨32, true⟩ 1))), (.const (.int ⟨32, true⟩ 1))),
  (.step (1) (-1), (.const (.int ⟨32, true⟩ 1)), (.un .neg ⟨32, true⟩ (.const (.int ⟨32, true⟩ 1)))),
  (.step (1) (1), (.const (.int ⟨32, true⟩ 1)), (.const (.int ⟨32, true⟩ 1)))]
def swCases (f : Int) : List (Nat × Stmt) := [(1, chainStmt (ops1 f)), (2, chainStmt (ops2 f)), (3, chainStmt (ops3 f)), (4, chainStmt (ops4 f)), (5, chainStmt (ops5 f)), (9, chainStmt (ops9 f)), (10, chainStmt (ops10 f)), (11, chainStmt (ops11 f)), (12, chainStmt (ops12 f)), (8, case8), (6, chainStmt (ops6 f)), (7, chainStmt (ops7 f)), (13, chainStmt (ops13 f)), (14, chainStmt (ops14 f))]

def ldPiece : Stmt := (.set 7 (.load (.int ⟨8, false⟩) (.index (.field (.var 0) 0) (.var 6) 1)))
def skipOther : Stmt := (.seq (.ite (.bin .eq (some ⟨32, true⟩) (.cast ⟨32, true⟩ (.var 7)) (.const (.int ⟨32, true⟩ 0))) (.set 9 (.const (.int ⟨32, true⟩ 1))) (.seq (.call (some 8) 1 [(.var 7)]) (.set 9 (.lor (.const (.int ⟨32, true⟩ 0)) (.bin .ne (some ⟨32, false⟩) (.cast ⟨32, false⟩ (.var 8)) (.cast ⟨32, false⟩ (.var 1))))))) (.ite (.var 9) .cont .skip))
def ldType : Stmt := (.seq (.call (some 11) 2 [(.var 7)]) (.set 10 (.var 11)))
def ldRow : Stmt := (.seq (.call (some 13) 7 [(.var 6)]) (.set 12 (.var 13)))
def ldCol : Stmt := (.seq (.call (some 15) 8 [(.var 6)]) (.set 14 (.var 15)))
def mkSrc : Stmt := (.seq (.alloc 16 24) (.seq (.store (.int ⟨8, false⟩) (.field (.var 16) 0) (.var 6)) (.seq (.store (.int ⟨8, false⟩) (.field (.var 16) 1) (.var 7)) (.seq (.store (.int ⟨32, false⟩) (.field (.var 16) 4) (.var 1)) (.seq (.store (.int ⟨32, false⟩) (.field (.var 16) 8) (.var 10)) (.seq (.store (.int ⟨32, true⟩) (.field (.var 16) 12) (.var 12)) (.seq (.store (.int ⟨32, true⟩) (.field (.var 16) 16) (.var 14)) (.seq (.call (some 17) 5 [(.var 10)]) (.seq (.store (.int ⟨8, false⟩) (.field (.var 16) 20) (.var 17)) (.seq (.call (some 18) 11 [(.var 1), (.var 12)]) (.store (.int ⟨8, false⟩) (.field (.var 16) 21) (.var 18))))))))))))
def sqCond : Expr := (.bin .lt (some ⟨32, true⟩) (.cast ⟨32, true⟩ (.var 6)) (.const (.int ⟨32, true⟩ 81)))
def sqStep : Stmt := (.set 6 (.cast ⟨8, false⟩ (.bin .add (some ⟨32, true⟩) (.cast ⟨32, true⟩ (.var 6)) (.const (.int ⟨32, true⟩ 1)))))
def swLoop (f : Int) : Stmt := .loop (.seq (switchStmt (swCases f) .brk) .brk) .skip
def sqBody (f : Int) : Stmt :=
  .ite sqCond (.seq ldPiece (.seq skipOther (.seq ldType (.seq ldRow (.seq ldCol (.seq mkSrc (swLoop f))))))) .brk

theorem loop2_eq (f : Int) : Gen.generate_pseudo_for_color_loop2 = .loop (sqBody f) sqStep := rfl

theorem swCond_ev {s : State} {k0 : Nat} (k : Nat) (hk0 : k0 < 2 ^ 32) (hk : k < 2 ^ 32)
    (h10 : s.locals 10 = some (.int IntTy.u32 k0)) :
    EvE Gen.prog s (swCond k) (boolVal (decide (k0 = k))) := by
  apply EvE_of_eval (n := 4)
  simp [swCond, evalExpr, h10, evalCast, evalBin, isPtr, evalBinInt, binInt, intOf, IntTy.u32, IntTy.modulus,
    Res.bind, Nat.mod_eq_of_lt hk0]

theorem switch_sel {s s' : State} {k0 : Nat} (hk0 : k0 < 2 ^ 32)
    (h10 : s.locals 10 = some (.int IntTy.u32 k0)) {o : Outcome} :
    ∀ (cs : List (Nat × Stmt)) (d b : Stmt), (∀ x ∈ cs, x.1 < 2 ^ 32) →
      ((cs.lookup k0 = some b ∧ ExS Gen.prog s b o s') ∨ (cs.lookup k0 = none ∧ ExS Gen.prog s d o s')) →
      ExS Gen.prog s (switchStmt cs d) o s' := by
  intro cs; induction cs with
  | nil => intro d b _ h; rcases h with ⟨h, _⟩ | ⟨_, h⟩
           · simp at h
           · exact h
  | cons x r ih =>
    intro d b hb h
    obtain ⟨k, st⟩ := x
    have hk : k < 2 ^ 32 := hb (k, st) (by simp)
    have hc := swCond_ev (s := s) k hk0 hk h10
    by_cases e : k0 = k
    · subst e
      have : st = b ∨ (False) := by
        rcases h with ⟨h, _⟩ | ⟨h, _⟩ <;> simp [List.lookup] at h; exact Or.inl h
      rcases this with rfl | f
      · rcases h with ⟨_, h⟩ | ⟨h, _⟩
        · exact ExS.ite (bc := true) hc (by simp [truthy_boolVal]) h
        · simp [List.lookup] at h
      · exact f.elim
    · have hl : (List.lookup k0 ((k, st) :: r)) = r.lookup k0 := by
        simp [List.lookup, show (k0 == k) = false by simp [e]]
      rw [hl] at h
      exact ExS.ite (bc := false) hc (by simp [truthy_boolVal, e]) (ih d b (fun y hy => hb y (by simp [hy])) h)

section args
variable {s : State} {f : Int} (h5 : s.locals 5 = some (i32 f)) (hf : -1 ≤ f ∧ f ≤ 1)
include h5 hf

theorem ev_f : EvE Gen.prog s (.var 5) (i32 f) := EvE.var h5
theorem ev_c0 : EvE Gen.prog s (.const (.int ⟨32, true⟩ 0)) (i32 0) := EvE.const _
theorem ev_c1 : EvE Gen.prog s (.const (.int ⟨32, true⟩ 1)) (i32 1) := EvE.const _
theorem ev_m1 : EvE Gen.prog s (.un .neg ⟨32, true⟩ (.const (.int ⟨32, true⟩ 1))) (i32 (-1)) := by
  apply EvE_of_eval (n := 3); simp [evalExpr, evalUn, intOf, IntTy.toInt, Res.bind, i32, IntTy.wrap, IntTy.modulus, arith,
    IntTy.inRange, IntTy.i32]; decide
theorem ev_2f : EvE Gen.prog s (.bin .mul (some ⟨32, true⟩) (.const (.int ⟨32, true⟩ 2)) (.var 5)) (i32 (2 * f)) := by
  apply EvE_of_eval (n := 3)
  rcases (show f = -1 ∨ f = 0 ∨ f = 1 by omega) with rfl | rfl | rfl <;>
    simp [evalExpr, h5, evalBin, isPtr, evalBinInt, binInt, intOf, IntTy.toInt, Res.bind, i32, IntTy.wrap,
      IntTy.modulus, IntTy.i32, arith, IntTy.inRange] <;> decide
theorem ev_nf : EvE Gen.prog s (.un .neg ⟨32, true⟩ (.var 5)) (i32 (-f)) := by
  apply EvE_of_eval (n := 3)
  rcases (show f = -1 ∨ f = 0 ∨ f = 1 by omega) with rfl | rfl | rfl <;>
    simp [evalExpr, h5, evalUn, intOf, IntTy.toInt, Res.bind, i32, IntTy.wrap, IntTy.modulus, IntTy.i32, arith, IntTy.inRange] <;> decide

end args

theorem swOps_ok {l : Locals} {f : Int} (hf : f = -1 ∨ f = 1) (h5 : l 5 = some (i32 f)) (k : Nat)
    (hk : k ∈ ([1, 2, 3, 4, 5, 9, 10, 11, 12, 6, 7, 13, 14] : List Nat)) :
    ArgsOk l (match k with | 1 => ops1 f | 2 => ops2 f | 3 => ops3 f | 4 => ops4 f | 5 => ops5 f | 9 => ops9 f | 10 => ops10 f | 11 => ops11 f | 12 => ops12 f | 6 => ops6 f | 7 => ops7 f | 13 => ops13 f | 14 => ops14 f | _ => []) := by
  have hf' : -1 ≤ f ∧ f ≤ 1 := by omega
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
  simp only [ArgsOk, ops1, ops2, ops3, ops4, ops5, ops9, ops10, ops11, ops12, ops6, ops7, ops13, ops14, List.forall_mem_cons, List.not_mem_nil, implies_true, and_true,
    false_implies, forall_const] <;>
  and_intros <;>
  first
    | omega
    | (simp only [Op.ok]; omega)
    | (intro s hs; have h5s : s.locals 5 = some (i32 f) := by rw [hs]; exact h5
       exact ⟨by first | exact ev_f h5s hf' | exact ev_c0 h5s hf' | exact ev_c1 h5s hf' | exact ev_m1 h5s hf'
                       | exact ev_2f h5s hf' | exact ev_nf h5s hf',
              by first | exact ev_f h5s hf' | exact ev_c0 h5s hf' | exact ev_c1 h5s hf' | exact ev_m1 h5s hf'
                       | exact ev_2f h5s hf' | exact ev_nf h5s hf'⟩)

end Shogi.C.Proofs
