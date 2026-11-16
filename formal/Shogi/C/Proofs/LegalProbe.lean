/-
  T8: probe-path iteration of the legality loop, for moves that are not pawn
  drops (no uchifuzume recursion): probe, test check, unprobe, keep if legal.
-/
import Shogi.C.Proofs.NoWrite
import Shogi.C.Proofs.LegalIter

namespace Shogi.C.Proofs
open MiniC Shogi Shogi.C Shogi.Tables

structure PInv (s : State) (p : Position) (mb mo cb co cap n : Nat) (L : List (List UInt8)) : Prop where
  l0 : s.locals 0 = some posPtr
  l1 : s.locals 1 = some (.ptr mb mo)
  l2 : s.locals 2 = some (.int IntTy.u64 cap)
  l6 : s.locals 6 = some (.ptr cb co)
  l7 : s.locals 7 = some (.int IntTy.u32 p.side.idx)
  l10 : s.locals 10 = some (.ptr n 0)
  mp : s.mem posBlock = some (encode p)
  buf : Buf s.mem mb mo cb co cap L
  tab : TablesIn s.mem
  ro : s.ro = false

theorem probe_path (p : Position) (hS : p.Shaped) (hK : KingsUnique p) (mv : Move) (hm : mv ∈ p.pseudoMoves)
    (hpd : Position.isPawnDrop mv = false)
    {s : State} {mb mo cb co cap n e3 : Nat} {L : List (List UInt8)}
    (hI : PInv s p mb mo cb co cap n L) (hn : s.mem n = some (moveBytes p mv)) (hf : Fresh s.mem (n + 1))
    (h64 : n + 8 < 2 ^ 64) (hn0 : n ≠ 0) (hl3 : s.locals 3 = some (.int IntTy.u8 e3))
    (hl11 : s.locals 11 = some (u8 1)) (hl17 : s.locals 17 = some (u8 0)) (hnmb : n ≠ mb) (hncb : n ≠ cb) (he3 : e3 < 256)
    (hpm : posBlock ≠ mb) (hpc : posBlock ≠ cb) :
    ∃ s', ExS Gen.prog s (.seq lp3 (.seq lp4 (.seq lp5 (.seq lp6 (.seq lp7 (.seq lp8 lp9)))))) .normal s' ∧
      Buf s'.mem mb mo cb co cap (L ++ (if (p.play mv).inCheck p.side then [] else [moveBytes p mv])) ∧
      s'.mem posBlock = some (encode p) := by
  have hMl : (moveBytes p mv).length = 5 := by cases mv <;> rfl
  have hnp : n ≠ posBlock := fun e => by rw [e, hI.mp] at hn; have := congrArg (Option.map List.length) hn; simp [encode_length, hMl] at this
  -- lp3: the fast path is not taken
  have hc3 : EvE Gen.prog s (.land (.un .lnot ⟨32, true⟩ (.var 11)) (.un .lnot ⟨32, true⟩ (.var 17))) (boolVal false) := by
    have := evB_and' (evB_not (EvE.var hl11) (truthy_u8 _)) (truthy_boolVal _)
      (evB_not (EvE.var hl17) (truthy_u8 _)) (truthy_boolVal _)
    simpa using this
  have ex3 : ExS Gen.prog s lp3 .normal s := ExS.ite (bc := false) hc3 rfl ExS.skip
  -- lp4: the undo record
  let ub := n + 1
  let m1 := (s.mem.upd 0 (encodeLE 8 (n + 2))).upd ub (List.replicate 20 0)
  let s4 : State := { s with mem := m1, locals := s.locals.upd 18 (.ptr ub 0) }
  have e4 : ExS Gen.prog s lp4 .normal s4 := exec_alloc (hf.allocAt (by omega)) 18 20
  have hm1 : ∀ x, x ≠ 0 → x ≠ ub → m1 x = s.mem x := fun x a b => by
    simp only [m1]; rw [Mem.upd_ne b, Mem.upd_ne a]
  have hf4 : Fresh m1 (n + 2) := hf.after_alloc _
  have hub0 : ub ≠ 0 := by omega
  have hpu : posBlock ≠ ub := fun e => by
    have := hf.2.2 ub (Nat.le_refl _); rw [← e, hI.mp] at this; cases this
  -- lp5: make_legal_probe
  obtain ⟨s5p, e5p, hp5, ho5, hro5, ⟨U, hU, hR⟩, hf5⟩ := make_probe_spec p hS hK mv hm (M := m1) (mvb := n) (ub := ub)
    (UB := List.replicate 20 0) (by rw [hm1 _ (by decide) hpu]; exact hI.mp)
    (by rw [hm1 _ hn0 (by omega)]; exact hn) Mem.upd_eq (by simp) hf4 (by omega) hn0 hub0 hpu
  let s5 : State := { s4 with mem := s5p.mem }
  have e5 : ExS Gen.prog s4 lp5 .normal s5 :=
    ExS.call (vs := [posPtr, .ptr n 0, .ptr ub 0])
      (EvArgs.cons (EvE.var (by simp [s4, Locals.upd]; exact hI.l0)) (EvArgs.cons (EvE.var (by simp [s4, Locals.upd]; exact hI.l10))
        (EvArgs.cons (EvE.var (by simp [s4, Locals.upd])) EvArgs.nil))) rfl rfl (by rw [show s4.ro = false from hI.ro]; exact e5p)
      (Or.inl rfl)
  have hkeep5 : ∀ x, x ≠ 0 → x ≠ posBlock → s.mem x ≠ none → s5.mem x = s.mem x := by
    intro x a b c
    have hxu : x ≠ ub := fun e => c (by rw [e]; exact hf.2.2 _ (Nat.le_refl _))
    have hx2 : x ≠ n + 2 := fun e => c (by rw [e]; exact hf.2.2 _ (by omega))
    show s5p.mem x = _; rw [ho5 x a hx2 hxu b, hm1 x a hxu]
  have htab5 : TablesIn s5.mem := by
    have ht := hI.tab
    exact ⟨by rw [hkeep5 _ (by decide) (by decide) (by rw [ht.g1]; simp)]; exact ht.g1,
      by rw [hkeep5 _ (by decide) (by decide) (by rw [ht.g2]; simp)]; exact ht.g2,
      by rw [hkeep5 _ (by decide) (by decide) (by rw [ht.g3]; simp)]; exact ht.g3,
      by rw [hkeep5 _ (by decide) (by decide) (by rw [ht.g4]; simp)]; exact ht.g4,
      by rw [hkeep5 _ (by decide) (by decide) (by rw [ht.g5]; simp)]; exact ht.g5⟩
  obtain ⟨s6p, e6p, ho6, h06, hn6⟩ := shogi_is_in_check_refines (p.play mv) p.side s5.mem (n + 3) hp5 htab5
    (hf5.allocAt (by omega))
  let ic := (p.play mv).inCheck p.side
  let v20 := if ic then true8 else false8
  let s6a : State := { s5 with mem := s6p.mem, locals := s5.locals.upd 20 v20 }
  have e6a : ExS Gen.prog s5 (.call (some 20) 21 [(.var 0), (.var 7)]) .normal s6a :=
    ExS.call_dst (EvArgs.cons (EvE.var (by show s4.locals 0 = _; simp [s4, Locals.upd]; exact hI.l0))
      (EvArgs.cons (EvE.var (by show s4.locals 7 = _; simp [s4, Locals.upd]; exact hI.l7)) EvArgs.nil)) rfl rfl
      (by rw [show s5.ro = false from hI.ro]; exact e6p)
  have h19v : EvE Gen.prog s6a (.cast ⟨8, false⟩ (.bin .ne (some ⟨32, true⟩) (.un .lnot ⟨32, true⟩ (.var 20))
      (.const (.int ⟨32, true⟩ 0)))) (u8 (if !ic then 1 else 0)) := by
    have hv : s6a.locals 20 = some v20 := by simp [s6a, Locals.upd]
    have ht : truthy v20 = .ok ic := by simp only [v20]; cases ic <;> rfl
    exact evB_u8 (evB_not (EvE.var hv) ht)
  let s6 : State := { s6a with locals := s6a.locals.upd 19 (u8 (if !ic then 1 else 0)) }
  have e6 : ExS Gen.prog s5 lp6 .normal s6 := ExS.seq e6a (ExS.set h19v)
  have hkeep6 : ∀ x, x ≠ 0 → x ≠ posBlock → s.mem x ≠ none → s6.mem x = s.mem x := by
    intro x a b c
    have hx3 : x ≠ n + 3 := fun e => c (by rw [e]; exact hf.2.2 _ (by omega))
    show s6p.mem x = _; rw [ho6 x a hx3]; exact hkeep5 x a b c
  have hn6' : s6.mem n = some (moveBytes p mv) := by rw [hkeep6 n hn0 hnp (by rw [hn]; simp)]; exact hn
  have l10 : s6.locals 10 = some (.ptr n 0) := by
    simp [s6, s6a, s5, s4, Locals.upd]; exact hI.l10
  have l3 : s6.locals 3 = some (.int IntTy.u8 e3) := by simp [s6, s6a, s5, s4, Locals.upd]; exact hl3
  have l19 : s6.locals 19 = some (u8 (if !ic then 1 else 0)) := by simp [s6, Locals.upd]
  have o1 : EvE Gen.prog s6 (.cast ⟨32, true⟩ (.var 19)) (.int IntTy.i32 (if !ic then 1 else 0)) :=
    EvE.cast (EvE.var l19) (truthy_i32c _ (by split <;> decide))
  have o2 : EvE Gen.prog s6 (.cast ⟨32, true⟩ (.var 3)) (.int IntTy.i32 e3) := EvE.cast (EvE.var l3) (truthy_i32c _ he3)
  have o3 := ev_cmp255 l10 hn6' (k := 0) (by omega) .eq (Or.inl rfl)
  simp only [if_true] at o3
  have h4v := ev_blk_u8 l10 hn6' (k := 4) (by omega)
  have hb4 := UInt8.toNat_lt ((moveBytes p mv).getD 4 0)
  have o4 : EvE Gen.prog s6 (.bin .eq (some ⟨32, true⟩) (.cast ⟨32, true⟩ (.load (.int ⟨8, false⟩) (.field (.var 10) 4)))
      (.const (.int ⟨32, true⟩ 1))) (boolVal (decide (((moveBytes p mv).getD 4 0).toNat = 1))) := by
    generalize hx : ((moveBytes p mv).getD 4 0).toNat = x at h4v hb4 ⊢
    refine EvE.bin (EvE.cast h4v (truthy_i32c x hb4)) (EvE.const _) ?_
    simp [evalBin, isPtr, evalBinInt, binInt, intOf, IntTy.i32, IntTy.toInt, Res.bind,
      show ¬ (2147483648 ≤ x) by omega]
    have e : ((x : Int) = 1) = (x = 1) := propext (by omega)
    simp only [e]
  have hc7 := evB_and' (evB_and' (evB_and' o1 rfl o2 rfl) (truthy_boolVal _) o3 (truthy_boolVal _))
    (truthy_boolVal _) o4 (truthy_boolVal _)
  have hval : (decide (((moveBytes p mv).getD 0 0).toNat = 255) && decide (((moveBytes p mv).getD 4 0).toNat = 1)) =
      false := by
    rw [← hpd]
    cases mv with
    | drop t d => cases t <;> rfl
    | normal sq d pr =>
      have := sq.isLt
      simp [moveBytes, Position.isPawnDrop, toNat_toUInt8_lt sq.val (by omega)]
  have hc7f : EvE Gen.prog s6 (.land (.land (.land (.cast ⟨32, true⟩ (.var 19)) (.cast ⟨32, true⟩ (.var 3))) (.bin .eq (some ⟨32, true⟩) (.cast ⟨32, true⟩ (.load (.int ⟨8, false⟩) (.field (.var 10) 0))) (.const (.int ⟨32, true⟩ 255)))) (.bin .eq (some ⟨32, true⟩) (.cast ⟨32, true⟩ (.load (.int ⟨8, false⟩) (.field (.var 10) 4))) (.const (.int ⟨32, true⟩ 1)))) (boolVal false) := by
    have hfalse : ((((if !ic then 1 else 0 : Nat) != 0) && (e3 != 0)) &&
        decide (((moveBytes p mv).getD 0 0).toNat = 255) && decide (((moveBytes p mv).getD 4 0).toNat = 1)) = false := by
      rw [Bool.and_assoc, hval, Bool.and_false]
    rw [hfalse] at hc7; exact hc7
  let s7 : State := { s6 with locals := s6.locals.upd 22 (.int ⟨32, true⟩ 0) }
  have e7 : ExS Gen.prog s6 lp7 .normal s7 :=
    ExS.seq (ExS.ite (bc := false) hc7f rfl (ExS.set (EvE.const _)))
      (ExS.ite (bc := false) (EvE.var (v := .int ⟨32, true⟩ 0) (by simp [s7, Locals.upd])) rfl ExS.skip)
  have hm7 : s7.mem = s6p.mem := rfl
  have hp7 : s7.mem posBlock = some (encode (p.play mv)) := by
    rw [hm7, ho6 _ (by decide) (by simp only [posBlock]; omega)]; exact hp5
  have hu7 : s7.mem ub = some U := by rw [hm7, ho6 _ hub0 (by omega)]; exact hU
  have hf7 : Fresh s7.mem (n + 4) := by
    refine ⟨by rw [hm7]; exact h06, by omega, fun x hx => ?_⟩
    rw [hm7, ho6 x (by omega) (by omega)]; exact hf5.2.2 x (by omega)
  obtain ⟨su, eu, hpu8, hou, hfu⟩ := unmake_spec p hS hK mv hm hp7 hu7 hR hf7 (by omega) hub0 hpu
  let s8 : State := { s7 with mem := su.mem }
  have e8 : ExS Gen.prog s7 lp8 .normal s8 :=
    ExS.call (vs := [posPtr, .ptr ub 0])
      (EvArgs.cons (EvE.var (by simp [s7, s6, s6a, s5, s4, Locals.upd]; exact hI.l0))
        (EvArgs.cons (EvE.var (by simp [s7, s6, s6a, s5, s4, Locals.upd])) EvArgs.nil)) rfl rfl
      (by rw [show s7.ro = false from hI.ro]; exact eu) (Or.inl rfl)
  have hkeep8 : ∀ x, x ≠ 0 → x ≠ posBlock → s.mem x ≠ none → s8.mem x = s.mem x := by
    intro x a b c
    have hx4 : x ≠ n + 4 := fun e => c (by rw [e]; exact hf.2.2 _ (by omega))
    show su.mem x = _; rw [hou x a hx4 b, hm7]; exact hkeep6 x a b c
  have hbuf8 : Buf s8.mem mb mo cb co cap L :=
    hI.buf.frame (hkeep8 mb hI.buf.mb0 (Ne.symm hpm) (by obtain ⟨blk, h, _⟩ := hI.buf.buf; rw [h]; simp))
      (hkeep8 cb hI.buf.cb0 (Ne.symm hpc) (by obtain ⟨blk, h, _⟩ := hI.buf.cnt; rw [h]; simp))
  have hpre : ∀ {o t}, ExS Gen.prog s8 lp9 o t →
      ExS Gen.prog s (.seq lp3 (.seq lp4 (.seq lp5 (.seq lp6 (.seq lp7 (.seq lp8 lp9)))))) o t :=
    fun h => ExS.seq ex3 (ExS.seq e4 (ExS.seq e5 (ExS.seq e6 (ExS.seq e7 (ExS.seq e8 h)))))
  have l19e : s8.locals 19 = s6.locals 19 := by simp [s8, s7, Locals.upd]
  have l19' : s8.locals 19 = some (u8 (if !ic then 1 else 0)) := by rw [l19e]; exact l19
  cases hic : ic
  · -- legal: keep the move
    have hn8 : s8.mem n = some (moveBytes p mv) := by rw [hkeep8 n hn0 hnp (by rw [hn]; simp)]; exact hn
    have hrd : readBytes s8.mem n 0 5 = .ok (moveBytes p mv) := by
      simp [readBytes, hn8, hMl, List.take_of_length_le]
    obtain ⟨sA, eA, hbA, _, hfrA⟩ := add_move_spec hbuf8 hrd hfu (by omega) hn0
    refine ⟨{ s8 with mem := sA.mem }, hpre (ExS.ite (bc := true) (EvE.var l19') (by simp [hic]; rfl)
      (ExS.call (vs := [.ptr mb mo, .ptr cb co, .int IntTy.u64 cap, .ptr n 0]) ?_ rfl rfl
        (by rw [show s8.ro = false from hI.ro]; exact eA) (Or.inl rfl))), ?_, ?_⟩
    · exact EvArgs.cons (EvE.var (by simp [s8, s7, s6, s6a, s5, s4, Locals.upd]; exact hI.l1))
        (EvArgs.cons (EvE.var (by simp [s8, s7, s6, s6a, s5, s4, Locals.upd]; exact hI.l6))
        (EvArgs.cons (EvE.var (by simp [s8, s7, s6, s6a, s5, s4, Locals.upd]; exact hI.l2))
        (EvArgs.cons (EvE.var l10) EvArgs.nil)))
    · simp only [ic] at hic; rw [hic]; simpa using hbA
    · exact hfrA.pos hpm hpc hpu8
  · -- in check: drop the move
    refine ⟨s8, hpre (ExS.ite (bc := false) (EvE.var l19') (by simp [hic]; rfl) ExS.skip), ?_, hpu8⟩
    simp only [ic] at hic; rw [hic]; simpa using hbuf8

end Shogi.C.Proofs
