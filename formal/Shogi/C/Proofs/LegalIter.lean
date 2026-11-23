/-
  T8: one iteration of the legality loop of `generate_legal_mut_internal`.
-/
import Shogi.C.Proofs.NeedsProbe

namespace Shogi.C.Proofs
variable {posBlock : Nat}
open MiniC Shogi Shogi.C Shogi.Tables

def lp0 : Stmt := (.seq (.alloc 10 5) (.memcpy (.var 10) (.index (.var 4) (.var 9) 5) (.const (.int ⟨64, false⟩ 5))))
def lp1 : Stmt := (.seq (.ite (.lor (.lor (.un .lnot ⟨32, true⟩ (.load (.int ⟨8, false⟩) (.field (.var 8) 1))) (.cast ⟨32, true⟩ (.load (.int ⟨8, false⟩) (.field (.var 8) 2)))) (.bin .eq (some ⟨32, true⟩) (.cast ⟨32, true⟩ (.load (.int ⟨8, false⟩) (.field (.var 10) 0))) (.const (.int ⟨32, true⟩ 255)))) (.set 13 (.const (.int ⟨32, true⟩ 1))) (.seq (.call (some 12) 2 [(.load (.int ⟨8, false⟩) (.index (.field (.var 0) 0) (.load (.int ⟨8, false⟩) (.field (.var 10) 0)) 1))]) (.set 13 (.lor (.const (.int ⟨32, true⟩ 0)) (.bin .eq (some ⟨32, false⟩) (.cast ⟨32, false⟩ (.var 12)) (.cast ⟨32, false⟩ (.const (.int ⟨32, true⟩ 8)))))))) (.seq (.ite (.var 13) (.set 16 (.const (.int ⟨32, true⟩ 1))) (.seq (.ite (.cast ⟨32, true⟩ (.load (.int ⟨8, false⟩) (.index (.field (.var 8) 3) (.load (.int ⟨8, false⟩) (.field (.var 10) 0)) 1))) (.seq (.call (some 14) 20 [(.load (.int ⟨8, false⟩) (.field (.var 8) 0)), (.load (.int ⟨8, false⟩) (.field (.var 10) 0)), (.load (.int ⟨8, false⟩) (.field (.var 10) 1))]) (.set 15 (.land (.const (.int ⟨32, true⟩ 1)) (.un .lnot ⟨32, true⟩ (.var 14))))) (.set 15 (.const (.int ⟨32, true⟩ 0)))) (.set 16 (.lor (.const (.int ⟨32, true⟩ 0)) (.var 15))))) (.set 11 (.cast ⟨8, false⟩ (.bin .ne (some ⟨32, true⟩) (.var 16) (.const (.int ⟨32, true⟩ 0)))))))
def lp2 : Stmt := (.set 17 (.cast ⟨8, false⟩ (.bin .ne (some ⟨32, true⟩) (.land (.bin .eq (some ⟨32, true⟩) (.cast ⟨32, true⟩ (.load (.int ⟨8, false⟩) (.field (.var 10) 0))) (.const (.int ⟨32, true⟩ 255))) (.bin .eq (some ⟨32, true⟩) (.cast ⟨32, true⟩ (.load (.int ⟨8, false⟩) (.field (.var 10) 4))) (.const (.int ⟨32, true⟩ 1)))) (.const (.int ⟨32, true⟩ 0)))))
def lp3 : Stmt := (.ite (.land (.un .lnot ⟨32, true⟩ (.var 11)) (.un .lnot ⟨32, true⟩ (.var 17))) (.seq (.call none 22 [(.var 1), (.var 6), (.var 2), (.var 10)]) .cont) .skip)
def lp4 : Stmt := (.alloc 18 20)
def lp5 : Stmt := (.call none 33 [(.var 0), (.var 10), (.var 18)])
def lp6 : Stmt := (.seq (.call (some 20) 21 [(.var 0), (.var 7)]) (.set 19 (.cast ⟨8, false⟩ (.bin .ne (some ⟨32, true⟩) (.un .lnot ⟨32, true⟩ (.var 20)) (.const (.int ⟨32, true⟩ 0))))))
def lp7 : Stmt := (.seq (.ite (.land (.land (.land (.cast ⟨32, true⟩ (.var 19)) (.cast ⟨32, true⟩ (.var 3))) (.bin .eq (some ⟨32, true⟩) (.cast ⟨32, true⟩ (.load (.int ⟨8, false⟩) (.field (.var 10) 0))) (.const (.int ⟨32, true⟩ 255)))) (.bin .eq (some ⟨32, true⟩) (.cast ⟨32, true⟩ (.load (.int ⟨8, false⟩) (.field (.var 10) 4))) (.const (.int ⟨32, true⟩ 1)))) (.seq (.call (some 21) 21 [(.var 0), (.load (.int ⟨32, false⟩) (.field (.var 0) 96))]) (.set 22 (.land (.const (.int ⟨32, true⟩ 1)) (.cast ⟨32, true⟩ (.var 21))))) (.set 22 (.const (.int ⟨32, true⟩ 0)))) (.ite (.var 22) (.seq (.alloc 23 36000) (.seq (.seq (.call (some 25) 35 [(.var 0), (.var 23), (.cast ⟨64, false⟩ (.const (.int ⟨32, true⟩ 7200))), (.cast ⟨8, false⟩ (.bin .ne (some ⟨32, true⟩) (.const (.int ⟨32, true⟩ 1)) (.const (.int ⟨32, true⟩ 0))))]) (.set 24 (.var 25))) (.set 19 (.cast ⟨8, false⟩ (.bin .ne (some ⟨32, true⟩) (.bin .ne (some ⟨64, false⟩) (.var 24) (.cast ⟨64, false⟩ (.const (.int ⟨32, true⟩ 0)))) (.const (.int ⟨32, true⟩ 0))))))) .skip))
def lp8 : Stmt := (.call none 34 [(.var 0), (.var 18)])
def lp9 : Stmt := (.ite (.var 19) (.call none 22 [(.var 1), (.var 6), (.var 2), (.var 10)]) .skip)
def lpCond : Expr := (.bin .lt (some ⟨64, false⟩) (.var 9) (.load (.int ⟨64, false⟩) (.var 5)))
def lpStep : Stmt := (.set 9 (.cast ⟨64, false⟩ (.bin .add (some ⟨64, false⟩) (.cast ⟨64, false⟩ (.var 9)) (.const (.int ⟨64, false⟩ 1)))))
def lpBody : Stmt := .ite lpCond (.seq lp0 (.seq lp1 (.seq lp2 (.seq lp3 (.seq lp4 (.seq lp5 (.seq lp6 (.seq lp7 (.seq lp8 lp9))))))))) .brk
theorem lp_loop_eq : Gen.generate_legal_mut_internal_loop0 = .loop lpBody lpStep := rfl
theorem lp1_eq : lp1 = npSeg := rfl
theorem lp2_eq : lp2 = pdSeg := rfl

/-- `ShogiMove move = pseudo[index];` -/
theorem lp0_spec {s : State} {pb i n : Nat} {PB MV : List UInt8} (hl4 : s.locals 4 = some (.ptr pb 0))
    (hl9 : s.locals 9 = some (.int IntTy.u64 i)) (hpb : s.mem pb = some PB) (hi : 5 * i + 5 ≤ PB.length)
    (hmv : (PB.drop (5 * i)).take 5 = MV) (hf : Fresh s.mem n) (h64 : n + 1 < 2 ^ 64) (hro : s.ro = false)
    (hpb0 : pb ≠ 0) :
    ExS Gen.prog s lp0 .normal
      { s with mem := ((s.mem.upd 0 (encodeLE 8 (n + 1))).upd n (List.replicate 5 0)).write n 0 MV,
               locals := s.locals.upd 10 (.ptr n 0) } := by
  have hnpb : n ≠ pb := fun e => by rw [← e, hf.2.2 n (Nat.le_refl _)] at hpb; cases hpb
  let m1 := (s.mem.upd 0 (encodeLE 8 (n + 1))).upd n (List.replicate 5 0)
  let s1 : State := { s with mem := m1, locals := s.locals.upd 10 (.ptr n 0) }
  have ea : ExS Gen.prog s (.alloc 10 5) .normal s1 := exec_alloc (hf.allocAt (by omega)) 10 5
  have hm1pb : m1 pb = some PB := by simp only [m1]; rw [Mem.upd_ne (Ne.symm hnpb), Mem.upd_ne hpb0]; exact hpb
  have hm1n : m1 n = some (List.replicate 5 0) := Mem.upd_eq
  have hMVl : MV.length = 5 := by rw [← hmv]; simp; omega
  refine ExS.seq ea (ExS.memcpy (bd := n) (od := 0) (bs := pb) (os := 0 + i * 5) (t := ⟨64, false⟩) (k := 5)
    (bytes := MV) (EvE.var (by simp [s1, Locals.upd]))
    (EvE.index (EvE.var (by simp [s1, Locals.upd]; exact hl4)) (EvE.var (by simp [s1, Locals.upd]; exact hl9))
      (by simp [IntTy.u64, ptrAddN, s1, hm1pb]; omega))
    (EvE.const _) hro (by simp [hnpb]) ?_ (writeBytes_ok hm1n (by simp [hMVl])))
  simp only [readBytes, s1, hm1pb]
  rw [if_pos (by omega), show 0 + i * 5 = 5 * i by omega, hmv]

/-- **Fast-path iteration**: for a pseudo-legal move with `needsProbeC = false`
    that is not a pawn drop, the iteration appends the move and continues. -/
theorem iter_fast {s : State} {p : Position} {m : Move} {pb i n Sb mb mo cb co cap : Nat} {PB : List UInt8}
    {L : List (List UInt8)} (rest : Stmt) (hm : m ∈ p.pseudoMoves)
    (hl0 : s.locals 0 = some (posPtr' posBlock)) (hl1 : s.locals 1 = some (.ptr mb mo)) (hl2 : s.locals 2 = some (.int IntTy.u64 cap))
    (hl4 : s.locals 4 = some (.ptr pb 0)) (hl6 : s.locals 6 = some (.ptr cb co))
    (hl8 : s.locals 8 = some (.ptr Sb 0)) (hl9 : s.locals 9 = some (.int IntTy.u64 i))
    (hpos : s.mem posBlock = some (encode p)) (hpb : s.mem pb = some PB) (hi : 5 * i + 5 ≤ PB.length)
    (hmv : (PB.drop (5 * i)).take 5 = moveBytes p m) (hSb : s.mem Sb = some (ksRec p p.side))
    (hbuf : Buf s.mem mb mo cb co cap L) (hf : Fresh s.mem n) (h64 : n + 2 < 2 ^ 64) (hro : s.ro = false)
    (hpb0 : pb ≠ 0) (hS0 : Sb ≠ 0) (hnp : needsProbeC (ksRec p p.side) p m = false)
    (hpd : Position.isPawnDrop m = false) :
    ∃ s', ExS Gen.prog s (.seq lp0 (.seq lp1 (.seq lp2 (.seq lp3 rest)))) .cont s' ∧
      Buf s'.mem mb mo cb co cap (L ++ [moveBytes p m]) ∧ Fresh s'.mem (n + 2) ∧
      (∀ x, x < 10 → s'.locals x = s.locals x) ∧ Frame s.mem s'.mem mb cb ∧ s'.ro = false := by
  have hnpb : n ≠ pb := fun e => by rw [← e, hf.2.2 n (Nat.le_refl _)] at hpb; cases hpb
  have hnS : n ≠ Sb := fun e => by rw [← e, hf.2.2 n (Nat.le_refl _)] at hSb; cases hSb
  have hnp' : n ≠ posBlock := fun e => by rw [← e, hf.2.2 n (Nat.le_refl _)] at hpos; cases hpos
  have hnb := hbuf.ne_fresh hf
  have e0 := lp0_spec hl4 hl9 hpb hi hmv hf (by omega) hro hpb0
  let m1 := ((s.mem.upd 0 (encodeLE 8 (n + 1))).upd n (List.replicate 5 0)).write n 0 (moveBytes p m)
  let s1 : State := { s with mem := m1, locals := s.locals.upd 10 (.ptr n 0) }
  have hm1o : ∀ x, x ≠ 0 → x ≠ n → m1 x = s.mem x := fun x a b => by
    simp only [m1]; rw [Mem.write_ne b, Mem.upd_ne b, Mem.upd_ne a]
  have hMl : (moveBytes p m).length = 5 := by cases m <;> rfl
  have hm1n : m1 n = some (moveBytes p m) := by
    simp only [m1]; rw [write_some Mem.upd_eq]; simp [wrb, hMl]
  have hP0 : posBlock ≠ 0 := posBlock_ne_zero hf.1 hpos
  obtain ⟨s2, e1, hm2, hro2, l11, hl2'⟩ := np_spec (s := s1) hm (by simp [s1, Locals.upd]; exact hl0)
    (by simp [s1, Locals.upd]; exact hl8) (by show m1 Sb = _; rw [hm1o Sb hS0 (Ne.symm hnS)]; exact hSb)
    (by simp [s1, Locals.upd]) hm1n (by show m1 posBlock = _; rw [hm1o _ hP0 (Ne.symm hnp')]; exact hpos)
  have e2 := pd_spec (s := s2) (p := p) (m := m) (n := n) (by rw [hl2' 10 (by omega)]; simp [s1, Locals.upd])
    (by rw [hm2]; exact hm1n)
  let s3 : State := { s2 with locals := s2.locals.upd 17 (u8 (if Position.isPawnDrop m then 1 else 0)) }
  have l11' : s3.locals 11 = some (u8 0) := by simp [s3, Locals.upd, l11, hnp]
  have l17 : s3.locals 17 = some (u8 0) := by simp [s3, Locals.upd, hpd]
  have hc3 : EvE Gen.prog s3 (.land (.un .lnot ⟨32, true⟩ (.var 11)) (.un .lnot ⟨32, true⟩ (.var 17))) (boolVal true) := by
    have := evB_and' (evB_not (EvE.var l11') (truthy_u8 _)) (truthy_boolVal _)
      (evB_not (EvE.var l17) (truthy_u8 _)) (truthy_boolVal _)
    simpa using this
  have hl3 : ∀ x, x < 10 → s3.locals x = s.locals x := fun x hx => by
    simp [s3, Locals.upd, show x ≠ 17 by omega]; rw [hl2' x (by omega)]; simp [s1, Locals.upd, show x ≠ 10 by omega]
  have hm3 : s3.mem = m1 := hm2
  have hbuf3 : Buf s3.mem mb mo cb co cap L := by
    rw [hm3]; exact hbuf.frame (hm1o mb hbuf.mb0 (Ne.symm hnb.1)) (hm1o cb hbuf.cb0 (Ne.symm hnb.2))
  have hf3 : Fresh s3.mem (n + 1) := by
    rw [hm3]; exact (hf.after_alloc _).write hf.2.1
  have hrd : readBytes s3.mem n 0 5 = .ok (moveBytes p m) := by
    rw [hm3]; simp [readBytes, hm1n, hMl, List.take_of_length_le]
  obtain ⟨sA, eA, hbA, hfA, hfrA⟩ := add_move_spec hbuf3 hrd hf3 (by omega) hf.2.1
  have hcall : ExS Gen.prog s3 (.call none 22 [(.var 1), (.var 6), (.var 2), (.var 10)]) .normal
      { s3 with mem := sA.mem } := by
    refine ExS.call (vs := [.ptr mb mo, .ptr cb co, .int IntTy.u64 cap, .ptr n 0]) ?_ rfl rfl
      (by rw [show s3.ro = false by show s2.ro = false; rw [hro2]; exact hro]; exact eA) (Or.inl rfl)
    exact EvArgs.cons (EvE.var (by rw [hl3 1 (by omega)]; exact hl1)) (EvArgs.cons (EvE.var (by rw [hl3 6 (by omega)]; exact hl6))
      (EvArgs.cons (EvE.var (by rw [hl3 2 (by omega)]; exact hl2)) (EvArgs.cons (EvE.var (by
        simp [s3, Locals.upd]; rw [hl2' 10 (by omega)]; simp [s1, Locals.upd])) EvArgs.nil)))
  refine ⟨{ s3 with mem := sA.mem }, ExS.seq e0 (ExS.seq (by rw [lp1_eq]; exact e1) (ExS.seq (by rw [lp2_eq]; exact e2)
    (ExS.seq_cont (ExS.ite (bc := true) hc3 rfl (ExS.seq hcall ExS.cont))))), hbA, hfA, fun x hx => hl3 x hx, ?_,
    by show s2.ro = false; rw [hro2]; exact hro⟩
  intro x a b c d
  have hxn : x ≠ n := fun e => by subst e; exact d (hf.2.2 _ (Nat.le_refl _))
  show sA.mem x = _
  rw [hfrA x a b c (by rw [hm3, hm1o x a hxn]; exact d), hm3, hm1o x a hxn]

end Shogi.C.Proofs
