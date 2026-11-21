import Shogi.C.Proofs.Fid18Guard
namespace Shogi.C.Proofs
open MiniC Shogi Shogi.C Shogi.C.Proofs

theorem piece_code_color (q : Piece) : q.code / 16 % 2 = q.color.idx := by
  obtain ⟨c, ty⟩ := q
  cases c <;> cases ty <;> decide +kernel

theorem piece_code_mod16 (q : Piece) : q.code % 16 = q.type.code := by
  obtain ⟨c, ty⟩ := q
  cases c <;> cases ty <;> decide +kernel

theorem piece_code_lt256 (q : Piece) : q.code < 256 := by
  obtain ⟨c, ty⟩ := q
  cases c <;> cases ty <;> decide +kernel

theorem piece_code_ne_zero (q : Piece) : q.code ≠ 0 := by
  obtain ⟨c, ty⟩ := q
  cases c <;> cases ty <;> decide

set_option maxRecDepth 100000 in
theorem slide_geom_finite : ∀ (f t : Square), f ≠ t →
  ((if (t.row : Int) - f.row < 0 then -((t.row : Int) - f.row) else (t.row : Int) - f.row) =
   (if (t.col : Int) - f.col < 0 then -((t.col : Int) - f.col) else (t.col : Int) - f.col) ∧
   (t.row : Int) - f.row ≠ 0) ∨
  ((t.row : Int) - f.row = 0 ∧ (t.col : Int) - f.col ≠ 0) ∨
  ((t.col : Int) - f.col = 0 ∧ (t.row : Int) - f.row ≠ 0) →
  let dr : Int := (t.row : Int) - f.row
  let dc : Int := (t.col : Int) - f.col
  let rs : Int := if dr > 0 then 1 else if dr < 0 then -1 else 0
  let cs : Int := if dc > 0 then 1 else if dc < 0 then -1 else 0
  let k : Nat := max dr.natAbs dc.natAbs
  let d : Nat := k - 1
  let row : Int := (f.row : Int) + rs
  let col : Int := (f.col : Int) + cs
  (t.row : Int) = row + (d : Int) * rs ∧
  (t.col : Int) = col + (d : Int) * cs ∧
  (∀ i, i ≤ d → 0 ≤ row + (i : Int) * rs ∧ row + (i : Int) * rs < 9 ∧
                  0 ≤ col + (i : Int) * cs ∧ col + (i : Int) * cs < 9) ∧
  (rs ≠ 0 ∨ cs ≠ 0) ∧
  1 ≤ k ∧ k ≤ 8
:= by decide +kernel



def guardExpr : Expr := (.un .lnot ⟨32, true⟩ (.lor (.lor (.land (.cast ⟨32, true⟩ (.var 15)) (.lor (.bin .eq (some ⟨32, false⟩) (.cast ⟨32, false⟩ (.var 4)) (.cast ⟨32, false⟩ (.const (.int ⟨32, true⟩ 6)))) (.bin .eq (some ⟨32, false⟩) (.cast ⟨32, false⟩ (.var 4)) (.cast ⟨32, false⟩ (.const (.int ⟨32, true⟩ 13)))))) (.land (.cast ⟨32, true⟩ (.var 16)) (.lor (.bin .eq (some ⟨32, false⟩) (.cast ⟨32, false⟩ (.var 4)) (.cast ⟨32, false⟩ (.const (.int ⟨32, true⟩ 7)))) (.bin .eq (some ⟨32, false⟩) (.cast ⟨32, false⟩ (.var 4)) (.cast ⟨32, false⟩ (.const (.int ⟨32, true⟩ 14))))))) (.land (.land (.bin .eq (some ⟨32, true⟩) (.var 9) (.const (.int ⟨32, true⟩ 0))) (.bin .gt (some ⟨32, true⟩) (.bin .mul (some ⟨32, true⟩) (.var 6) (.var 12)) (.const (.int ⟨32, true⟩ 0)))) (.bin .eq (some ⟨32, false⟩) (.cast ⟨32, false⟩ (.var 4)) (.cast ⟨32, false⟩ (.const (.int ⟨32, true⟩ 2)))))))

def guardState (ty : Nat) (dr dc fwd : Int) (diag straight : Nat) : State :=
  ⟨(fun i => match i with
      | 4 => some (u32 ty) | 6 => some (i32 dr) | 9 => some (i32 dc)
      | 12 => some (i32 fwd) | 15 => some (u8 diag) | 16 => some (u8 straight)
      | _ => none), (fun _ => none), false⟩

def evalSig (r : Res Val) : Option (IntTy × Nat) := match r with | .ok (.int t n) => some (t,n) | _ => none

def guardSpec (ty : Nat) (dr dc fwd : Int) (diag straight : Nat) : Nat :=
  let v := (decide (diag != 0) && decide (ty = 6 ∨ ty = 13)) ||
           (decide (straight != 0) && decide (ty = 7 ∨ ty = 14)) ||
           (decide (dc = 0) && decide (dr * fwd > 0) && decide (ty = 2))
  if v then 0 else 1


set_option maxRecDepth 100000 in
theorem guard_eval_finite : ∀ (ty : Fin 16) (dr' dc' : Fin 17) (fwdb : Fin 2) (diagb : Fin 2) (straightb : Fin 2),
  evalSig (evalExpr Gen.prog 12 (guardState ty.val ((dr'.val:Int)-8) ((dc'.val:Int)-8) (if fwdb.val=0 then 1 else -1) diagb.val straightb.val) guardExpr) =
    some (IntTy.i32, guardSpec ty.val ((dr'.val:Int)-8) ((dc'.val:Int)-8) (if fwdb.val=0 then 1 else -1) diagb.val straightb.val) := by
  decide +kernel

#eval evalSig (evalExpr Gen.prog 12 (guardState 6 1 1 1 1 1) guardExpr)
#eval guardSpec 6 1 1 1 1 1
#eval evalSig (evalExpr Gen.prog 12 (guardState 0 1 1 1 1 1) guardExpr)
#eval guardSpec 0 1 1 1 1 1

def absI (z : Int) : Int := if z < 0 then -z else z

def set15expr : Expr := .cast ⟨8,false⟩ (.bin .ne (some ⟨32,true⟩)
  (.bin .eq (some ⟨32,true⟩)
    (.cond (.bin .lt (some ⟨32,true⟩) (.var 6) (.const (.int ⟨32,true⟩ 0))) (.un .neg ⟨32,true⟩ (.var 6)) (.var 6))
    (.cond (.bin .lt (some ⟨32,true⟩) (.var 9) (.const (.int ⟨32,true⟩ 0))) (.un .neg ⟨32,true⟩ (.var 9)) (.var 9)))
  (.const (.int ⟨32,true⟩ 0)))

def sTest (dr dc : Int) : State :=
  ⟨fun i => if i = 6 then some (i32 dr) else if i = 9 then some (i32 dc) else none, (fun _ => none), false⟩

set_option maxRecDepth 100000 in
theorem set15_eval_finite : ∀ (dr' dc' : Fin 17),
  evalSig (evalExpr Gen.prog 10 (sTest ((dr'.val : Int) - 8) ((dc'.val : Int) - 8)) set15expr) =
    some (IntTy.u8, if absI ((dr'.val : Int) - 8) = absI ((dc'.val : Int) - 8) then 1 else 0) := by
  decide +kernel

end Shogi.C.Proofs
