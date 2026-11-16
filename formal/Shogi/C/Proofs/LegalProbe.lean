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
      s'.mem posBlock = some (encode p) ∧ s'.ro = false ∧ (∀ x, x < 10 → s'.locals x = s.locals x) ∧
      (∀ x, x ≠ 0 → x ≠ mb → x ≠ cb → s.mem x ≠ none → s'.mem x = s.mem x) ∧
      ∃ f, Fresh s'.mem f ∧ f ≤ n + 6 := by
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
    obtain ⟨sA, eA, hbA, hfA, hfrA⟩ := add_move_spec hbuf8 hrd hfu (by omega) hn0
    refine ⟨{ s8 with mem := sA.mem }, hpre (ExS.ite (bc := true) (EvE.var l19') (by simp [hic]; rfl)
      (ExS.call (vs := [.ptr mb mo, .ptr cb co, .int IntTy.u64 cap, .ptr n 0]) ?_ rfl rfl
        (by rw [show s8.ro = false from hI.ro]; exact eA) (Or.inl rfl))), ?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact EvArgs.cons (EvE.var (by simp [s8, s7, s6, s6a, s5, s4, Locals.upd]; exact hI.l1))
        (EvArgs.cons (EvE.var (by simp [s8, s7, s6, s6a, s5, s4, Locals.upd]; exact hI.l6))
        (EvArgs.cons (EvE.var (by simp [s8, s7, s6, s6a, s5, s4, Locals.upd]; exact hI.l2))
        (EvArgs.cons (EvE.var l10) EvArgs.nil)))
    · simp only [ic] at hic; rw [hic]; simpa using hbA
    · exact hfrA.pos hpm hpc hpu8
    · exact hI.ro
    · intro x hx; simp [s8, s7, s6, s6a, s5, s4, Locals.upd, show x ≠ 22 by omega, show x ≠ 19 by omega,
        show x ≠ 20 by omega, show x ≠ 18 by omega]
    · intro x a b c d
      show sA.mem x = _
      have h8 : s8.mem x = s.mem x := by
        by_cases hxp : x = posBlock
        · subst hxp; rw [hpu8, hI.mp]
        · exact hkeep8 x a hxp d
      rw [hfrA x a b c (by rw [h8]; exact d), h8]
    · exact ⟨_, hfA, by omega⟩
  · -- in check: drop the move
    refine ⟨s8, hpre (ExS.ite (bc := false) (EvE.var l19') (by simp [hic]; rfl) ExS.skip), ?_, hpu8, hI.ro,
      fun x hx => ?_, fun x a b c d => ?_, ?_⟩
    · simp only [ic] at hic; rw [hic]; simpa using hbuf8
    · simp [s8, s7, s6, s6a, s5, s4, Locals.upd, show x ≠ 22 by omega, show x ≠ 19 by omega,
        show x ≠ 20 by omega, show x ≠ 18 by omega]
    · by_cases hxp : x = posBlock
      · subst hxp; rw [hpu8, hI.mp]
      · exact hkeep8 x a hxp d
    · exact ⟨_, hfu, by omega⟩

/-- The reply buffer the recursive call writes into: a block of at least
    3000 bytes (600 five-byte moves) at offset 0, distinct from the allocator
    block, the position block and the attack-table blocks. -/
def ReplyBuf (M : Mem) (rb : Nat) : Prop :=
  ∃ blk, M rb = some blk ∧ 3000 ≤ blk.length ∧ rb ≠ 0 ∧ rb ≠ posBlock ∧ (rb < 8192 ∨ 8196 < rb)

/-- Per-call allocation budget of the recursive call.  Discharging `RecSpec`
    (M4) replaces this fixed bound by one that grows with the pawn count;
    until then it keeps the current shape. -/
def recBudget : Nat := 1000000000

/-- What the recursive `generate_legal_mut_internal(position, replies, 600, true)`
    call must do (the induction hypothesis of the eventual loop proof): from a
    memory holding `encode q`, it returns a count that is nonzero exactly when
    the spec's `legalAux fuel q` is nonempty, restores the position, and only
    allocates.  Only demanded for checking pawn drops (the C recurses exactly
    there), which is what makes it dischargeable: the spec's fuel only runs
    out on moves that never enter the recursion. -/
def RecSpec (fuel : Nat) (q : Position) : Prop :=
  ∀ (M : Mem) (rb k : Nat), M posBlock = some (encode q) → TablesIn M → Fresh M k → ReplyBuf M rb →
    k + recBudget < 2 ^ 64 →
    ∃ s' cnt k', ExS Gen.prog ⟨frameLocals Gen.generate_legal_mut_internal.params
        [posPtr, .ptr rb 0, .int IntTy.u64 600, .int IntTy.u8 1], M, false⟩
      Gen.generate_legal_mut_internal.body (.ret (some (.int IntTy.u64 cnt))) s' ∧
      (cnt ≠ 0 ↔ !(Position.legalAux fuel q).isEmpty) ∧ s'.mem posBlock = some (encode q) ∧
      Fresh s'.mem k' ∧ k ≤ k' ∧ k' ≤ k + recBudget ∧
      (∀ x, x ≠ 0 → x ≠ rb → x < k → x ≠ posBlock → s'.mem x = M x)

/-- A freshly allocated block number cannot be one of the attack-table blocks:
    `Fresh` says everything at or above `k` is empty, `TablesIn` says the five
    table blocks are not. -/
theorem fresh_not_table {M : Mem} {k b : Nat} (hf : Fresh M k) (ht : TablesIn M) (hk : k ≤ b) :
    b < 8192 ∨ 8196 < b := by
  have hnone : M b = none := hf.2.2 b hk
  have hne := ht.fresh hnone
  rcases Nat.lt_or_ge b 8192 with h | h
  · exact Or.inl h
  rcases Nat.lt_or_ge b 8197 with h | h
  · exfalso
    rcases Nat.lt_or_ge b 8193 with h3 | h3
    · have hb : b = 8192 := by omega
      rw [hb] at hne
      omega
    rcases Nat.lt_or_ge b 8194 with h4 | h4
    · have hb : b = 8193 := by omega
      rw [hb] at hne
      omega
    rcases Nat.lt_or_ge b 8195 with h5 | h5
    · have hb : b = 8194 := by omega
      rw [hb] at hne
      omega
    rcases Nat.lt_or_ge b 8196 with h6 | h6
    · have hb : b = 8195 := by omega
      rw [hb] at hne
      omega
    · have hb : b = 8196 := by omega
      rw [hb] at hne
      omega
  · exact Or.inr (by omega)

theorem probe_path_drop (p : Position) (hS : p.Shaped) (hK : KingsUnique p) (mv : Move) (hm : mv ∈ p.pseudoMoves)
    (hpd : Position.isPawnDrop mv = true) (fuel : Nat)
    (hrec : (p.play mv).inCheck (p.play mv).side → RecSpec fuel (p.play mv))
    {s : State} {mb mo cb co cap n e3 : Nat} {L : List (List UInt8)}
    (hI : PInv s p mb mo cb co cap n L) (hn : s.mem n = some (moveBytes p mv)) (hf : Fresh s.mem (n + 1))
    (h64 : n + 4000000100 < 2 ^ 64) (hn0 : n ≠ 0) (hl3 : s.locals 3 = some (.int IntTy.u8 e3))
    {a11 : Nat} (hl11 : s.locals 11 = some (u8 a11)) (hl17 : s.locals 17 = some (u8 1)) (hnmb : n ≠ mb) (hncb : n ≠ cb) (he3 : e3 = 1)
    (hpm : posBlock ≠ mb) (hpc : posBlock ≠ cb) :
    ∃ s', ExS Gen.prog s (.seq lp3 (.seq lp4 (.seq lp5 (.seq lp6 (.seq lp7 (.seq lp8 lp9)))))) .normal s' ∧
      Buf s'.mem mb mo cb co cap (L ++ (if specKeep p fuel mv then [moveBytes p mv] else [])) ∧
      s'.mem posBlock = some (encode p) ∧ s'.ro = false ∧ (∀ x, x < 10 → s'.locals x = s.locals x) ∧
      (∀ x, x ≠ 0 → x ≠ mb → x ≠ cb → s.mem x ≠ none → s'.mem x = s.mem x) ∧
      ∃ f, Fresh s'.mem f ∧ f ≤ n + 1000000020 := by
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
  have o2 : EvE Gen.prog s6 (.cast ⟨32, true⟩ (.var 3)) (.int IntTy.i32 e3) := EvE.cast (EvE.var l3) (truthy_i32c _ (by omega))
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
      true := by
    rw [← hpd]
    cases mv with
    | drop t d => cases t <;> rfl
    | normal sq d pr => simp [Position.isPawnDrop] at hpd
  have hcv : ((((if !ic then 1 else 0 : Nat) != 0) && (e3 != 0)) &&
      decide (((moveBytes p mv).getD 0 0).toNat = 255) && decide (((moveBytes p mv).getD 4 0).toNat = 1)) = !ic := by
    rw [Bool.and_assoc, hval, Bool.and_true, he3]; cases ic <;> rfl
  rw [hcv] at hc7
  -- the unmake / keep tail, shared by all outcomes of `lp7`
  have tail : ∀ (s7 : State) (U' : List UInt8) (kf : Nat) (keep : Bool), ExS Gen.prog s6 lp7 .normal s7 →
      s7.locals 19 = some (u8 (if keep then 1 else 0)) → (∀ x, x < 19 → s7.locals x = s6.locals x) →
      s7.mem posBlock = some (encode (p.play mv)) → s7.mem ub = some U → Fresh s7.mem kf → kf + 100000 < 2 ^ 64 →
      (∀ x, x ≠ 0 → x ≠ posBlock → s.mem x ≠ none → s7.mem x = s.mem x) → s7.ro = false →
      ∃ s', ExS Gen.prog s (.seq lp3 (.seq lp4 (.seq lp5 (.seq lp6 (.seq lp7 (.seq lp8 lp9)))))) .normal s' ∧
        Buf s'.mem mb mo cb co cap (L ++ (if keep then [moveBytes p mv] else [])) ∧
        s'.mem posBlock = some (encode p) ∧ s'.ro = false ∧ (∀ x, x < 10 → s'.locals x = s.locals x) ∧
        (∀ x, x ≠ 0 → x ≠ mb → x ≠ cb → s.mem x ≠ none → s'.mem x = s.mem x) ∧
        ∃ f, Fresh s'.mem f ∧ f ≤ kf + 2 := by
    intro s7 U' kf keep e7 l19k hl7 hp7 hu7 hf7 hkf hk7 hro7
    obtain ⟨su, eu, hpu8, hou, hfu⟩ := unmake_spec p hS hK mv hm hp7 hu7 hR hf7 (by omega) hub0 hpu
    let s8 : State := { s7 with mem := su.mem }
    have l0_7 : s7.locals 0 = some posPtr := by rw [hl7 0 (by omega)]; simp [s6, s6a, s5, s4, Locals.upd]; exact hI.l0
    have e8 : ExS Gen.prog s7 lp8 .normal s8 :=
      ExS.call (vs := [posPtr, .ptr ub 0])
        (EvArgs.cons (EvE.var l0_7)
          (EvArgs.cons (EvE.var (by rw [hl7 18 (by omega)]; simp [s6, s6a, s5, s4, Locals.upd])) EvArgs.nil)) rfl rfl
        (by rw [hro7]; exact eu) (Or.inl rfl)
    have hkeep8 : ∀ x, x ≠ 0 → x ≠ posBlock → s.mem x ≠ none → s8.mem x = s.mem x := by
      intro x a b c
      have hxk : x ≠ kf := fun e => by
        have := hf7.2.2 x (by omega); rw [hk7 x a b c] at this; exact c this
      show su.mem x = _; rw [hou x a hxk b]; exact hk7 x a b c
    have hbuf8 : Buf s8.mem mb mo cb co cap L :=
      hI.buf.frame (hkeep8 mb hI.buf.mb0 (Ne.symm hpm) (by obtain ⟨blk, h, _⟩ := hI.buf.buf; rw [h]; simp))
        (hkeep8 cb hI.buf.cb0 (Ne.symm hpc) (by obtain ⟨blk, h, _⟩ := hI.buf.cnt; rw [h]; simp))
    have hpre : ∀ {o t}, ExS Gen.prog s8 lp9 o t →
        ExS Gen.prog s (.seq lp3 (.seq lp4 (.seq lp5 (.seq lp6 (.seq lp7 (.seq lp8 lp9)))))) o t :=
      fun h => ExS.seq ex3 (ExS.seq e4 (ExS.seq e5 (ExS.seq e6 (ExS.seq e7 (ExS.seq e8 h)))))
    have l19' : s8.locals 19 = some (u8 (if keep then 1 else 0)) := l19k
    have lx : ∀ x, x < 19 → s8.locals x = s6.locals x := hl7
    cases hk : keep
    · refine ⟨s8, hpre (ExS.ite (bc := false) (EvE.var l19') (by simp [hk]; rfl) ExS.skip), ?_, hpu8, hro7,
        fun x hx => ?_, fun x a b c d => ?_, ⟨_, hfu, by omega⟩⟩
      · simpa using hbuf8
      · rw [show s8.locals x = s7.locals x from rfl, lx x (by omega)]
        simp [s6, s6a, s5, s4, Locals.upd, show x ≠ 19 by omega, show x ≠ 20 by omega, show x ≠ 18 by omega]
      · by_cases hxp : x = posBlock
        · subst hxp; rw [hpu8, hI.mp]
        · exact hkeep8 x a hxp d
    · have hn8 : s8.mem n = some (moveBytes p mv) := by rw [hkeep8 n hn0 hnp (by rw [hn]; simp)]; exact hn
      have hrd : readBytes s8.mem n 0 5 = .ok (moveBytes p mv) := by
        simp [readBytes, hn8, hMl, List.take_of_length_le]
      obtain ⟨sA, eA, hbA, hfA, hfrA⟩ := add_move_spec hbuf8 hrd hfu (by omega) hn0
      refine ⟨{ s8 with mem := sA.mem }, hpre (ExS.ite (bc := true) (EvE.var l19') (by simp [hk]; rfl)
        (ExS.call (vs := [.ptr mb mo, .ptr cb co, .int IntTy.u64 cap, .ptr n 0]) ?_ rfl rfl
          (by rw [show s8.ro = false from hro7]; exact eA) (Or.inl rfl))), by simpa using hbA, hfrA.pos hpm hpc hpu8,
          hro7, fun x hx => ?_, fun x a b c d => ?_, ⟨_, hfA, by omega⟩⟩
      rotate_left
      · rw [show ({ s8 with mem := sA.mem } : State).locals x = s7.locals x from rfl, lx x (by omega)]
        simp [s6, s6a, s5, s4, Locals.upd, show x ≠ 19 by omega, show x ≠ 20 by omega, show x ≠ 18 by omega]
      · show sA.mem x = _
        have h8 : s8.mem x = s.mem x := by
          by_cases hxp : x = posBlock
          · subst hxp; rw [hpu8, hI.mp]
          · exact hkeep8 x a hxp d
        rw [hfrA x a b c (by rw [h8]; exact d), h8]
      exact EvArgs.cons (EvE.var (by rw [lx 1 (by omega)]; simp [s6, s6a, s5, s4, Locals.upd]; exact hI.l1))
        (EvArgs.cons (EvE.var (by rw [lx 6 (by omega)]; simp [s6, s6a, s5, s4, Locals.upd]; exact hI.l6))
        (EvArgs.cons (EvE.var (by rw [lx 2 (by omega)]; simp [s6, s6a, s5, s4, Locals.upd]; exact hI.l2))
        (EvArgs.cons (EvE.var (by rw [lx 10 (by omega)]; exact l10)) EvArgs.nil)))
  have hm6 : s6.mem = s6p.mem := rfl
  have hp6 : s6.mem posBlock = some (encode (p.play mv)) := by
    rw [hm6, ho6 _ (by decide) (by simp only [posBlock]; omega)]; exact hp5
  have hu6 : s6.mem ub = some U := by rw [hm6, ho6 _ hub0 (by omega)]; exact hU
  have hf6 : Fresh s6.mem (n + 4) := by
    refine ⟨by rw [hm6]; exact h06, by omega, fun x hx => ?_⟩
    rw [hm6, ho6 x (by omega) (by omega)]; exact hf5.2.2 x (by omega)
  have hl6x : ∀ x, x < 19 → s6.locals x = s6.locals x := fun _ _ => rfl
  let q := p.play mv
  cases hic : ic
  · -- the drop does not leave the own king in check: test whether it gives check
    rw [hic] at hc7
    have hqs : EvE Gen.prog s6 (.load (.int ⟨32, false⟩) (.field (.var 0) 96)) (.int IntTy.u32 q.side.idx) := by
      have l0 : s6.locals 0 = some posPtr := by simp [s6, s6a, s5, s4, Locals.upd]; exact hI.l0
      refine EvE.load (pa := .ptr posBlock 96) (EvE.field (EvE.var l0) (by simp [ptrAddN, posPtr, hp6, encode_length])) ?_
      simp only [load, readBytes, hp6, encode_length, Ty.size, IntTy.bytes]
      rw [if_pos (by omega), encode_enc, enc_side]
      simp only [Res.bind_eq, Res.bind_ok, pure]
      rw [decode_le32 _ (by cases q.side <;> decide)]; rfl
    have htab6 : TablesIn s6.mem := by
      have ht := htab5
      have k : ∀ g, g ≠ 0 → s5.mem g ≠ none → g ≠ n + 3 → s6.mem g = s5.mem g := fun g a _ c => by
        rw [hm6, ho6 g a c]
      have ne3 : ∀ g, s5.mem g ≠ none → g ≠ n + 3 := fun g hg e => hg (by rw [e]; exact hf5.2.2 _ (Nat.le_refl _))
      exact ⟨by rw [k _ (by decide) (by rw [ht.g1]; simp) (ne3 _ (by rw [ht.g1]; simp))]; exact ht.g1,
        by rw [k _ (by decide) (by rw [ht.g2]; simp) (ne3 _ (by rw [ht.g2]; simp))]; exact ht.g2,
        by rw [k _ (by decide) (by rw [ht.g3]; simp) (ne3 _ (by rw [ht.g3]; simp))]; exact ht.g3,
        by rw [k _ (by decide) (by rw [ht.g4]; simp) (ne3 _ (by rw [ht.g4]; simp))]; exact ht.g4,
        by rw [k _ (by decide) (by rw [ht.g5]; simp) (ne3 _ (by rw [ht.g5]; simp))]; exact ht.g5⟩
    obtain ⟨sc, ecp, hoc, h0c, _⟩ := shogi_is_in_check_refines q q.side s6.mem (n + 4) hp6 htab6
      (hf6.allocAt (by omega))
    let icq := q.inCheck q.side
    let sc1 : State := { s6 with mem := sc.mem, locals := s6.locals.upd 21 (if icq then true8 else false8) }
    have ec : ExS Gen.prog s6 (.call (some 21) 21 [(.var 0), (.load (.int ⟨32, false⟩) (.field (.var 0) 96))]) .normal sc1 :=
      ExS.call_dst (EvArgs.cons (EvE.var (by simp [s6, s6a, s5, s4, Locals.upd]; exact hI.l0))
        (EvArgs.cons hqs EvArgs.nil)) rfl rfl (by rw [show s6.ro = false from hI.ro]; exact ecp)
    have h22 : EvE Gen.prog sc1 (.land (.const (.int ⟨32, true⟩ 1)) (.cast ⟨32, true⟩ (.var 21))) (boolVal icq) := by
      have hv : sc1.locals 21 = some (if icq then true8 else false8) := by simp [sc1, Locals.upd]
      have := evB_and' (b1 := true) (b2 := icq) (e2 := .cast ⟨32, true⟩ (.var 21)) (EvE.const (.int ⟨32, true⟩ 1)) rfl
        (EvE.cast (EvE.var hv) (by cases icq <;> rfl)) (v2 := .int IntTy.i32 (if icq then 1 else 0))
        (by cases icq <;> rfl)
      simpa using this
    let sc2 : State := { sc1 with locals := sc1.locals.upd 22 (boolVal icq) }
    have ec2 : ExS Gen.prog s6 (.ite (.land (.land (.land (.cast ⟨32, true⟩ (.var 19)) (.cast ⟨32, true⟩ (.var 3))) (.bin .eq (some ⟨32, true⟩) (.cast ⟨32, true⟩ (.load (.int ⟨8, false⟩) (.field (.var 10) 0))) (.const (.int ⟨32, true⟩ 255)))) (.bin .eq (some ⟨32, true⟩) (.cast ⟨32, true⟩ (.load (.int ⟨8, false⟩) (.field (.var 10) 4))) (.const (.int ⟨32, true⟩ 1)))) (.seq (.call (some 21) 21 [(.var 0), (.load (.int ⟨32, false⟩) (.field (.var 0) 96))]) (.set 22 (.land (.const (.int ⟨32, true⟩ 1)) (.cast ⟨32, true⟩ (.var 21))))) (.set 22 (.const (.int ⟨32, true⟩ 0)))) .normal sc2 :=
      ExS.ite (bc := true) hc7 rfl (ExS.seq ec (ExS.set h22))
    have hmc : ∀ x, x ≠ 0 → x ≠ n + 4 → sc2.mem x = s6.mem x := fun x a b => hoc x a b
    have hkc : ∀ x, x ≠ 0 → x ≠ posBlock → s.mem x ≠ none → sc2.mem x = s.mem x := fun x a b c => by
      rw [hmc x a (fun e => c (by rw [e]; exact hf.2.2 _ (by omega)))]; exact hkeep6 x a b c
    have hlc' : ∀ x, x < 21 → sc2.locals x = s6.locals x := fun x hx => by
      simp [sc2, sc1, Locals.upd, show x ≠ 22 by omega, show x ≠ 21 by omega]
    have hlc : ∀ x, x < 19 → sc2.locals x = s6.locals x := fun x hx => hlc' x (by omega)
    have l19c : sc2.locals 19 = some (u8 (if !ic then 1 else 0)) := by
      rw [hlc' 19 (by omega)]; exact l19
    have hpc2 : sc2.mem posBlock = some (encode q) := by rw [hmc _ (by decide) (by simp only [posBlock]; omega)]; exact hp6
    have huc2 : sc2.mem ub = some U := by rw [hmc _ hub0 (by omega)]; exact hu6
    have hfc2 : Fresh sc2.mem (n + 5) := by
      refine ⟨h0c, by omega, fun x hx => ?_⟩
      rw [hmc x (by omega) (by omega)]; exact hf6.2.2 x (by omega)
    cases hicq : icq
    · -- no check: the drop is legal
      have e7 : ExS Gen.prog s6 lp7 .normal sc2 :=
        ExS.seq ec2 (ExS.ite (bc := false) (vc := boolVal false) (EvE.var (by simp [sc2, Locals.upd, hicq]))
          (truthy_boolVal _) ExS.skip)
      obtain ⟨s', e', hb', hp', hx1, hx2, hx3, hx4⟩ := tail sc2 U (n + 5) true e7 (by rw [l19c, hic]; rfl) hlc hpc2 huc2 hfc2 (by omega) hkc hI.ro
      refine ⟨s', e', ?_, hp', hx1, hx2, hx3, by obtain ⟨f, hf1, hf2⟩ := hx4; exact ⟨f, hf1, by omega⟩⟩
      have hk : specKeep p fuel mv = true := by
        simp only [specKeep, Position.isPawnDrop, hpd, if_true, ic, icq, q] at hic hicq ⊢
        simp [hic, hicq]
      rw [hk]; exact hb'
    · -- check: the drop is legal exactly when the opponent has a legal reply
      have htc2 : TablesIn sc2.mem := by
        have ht := htab6
        have k : ∀ g, g ≠ 0 → s6.mem g ≠ none → sc2.mem g = s6.mem g := fun g a b =>
          hmc g a (fun e => b (by rw [e]; exact hf6.2.2 _ (Nat.le_refl _)))
        exact ⟨by rw [k _ (by decide) (by rw [ht.g1]; simp)]; exact ht.g1, by rw [k _ (by decide) (by rw [ht.g2]; simp)]; exact ht.g2,
          by rw [k _ (by decide) (by rw [ht.g3]; simp)]; exact ht.g3, by rw [k _ (by decide) (by rw [ht.g4]; simp)]; exact ht.g4,
          by rw [k _ (by decide) (by rw [ht.g5]; simp)]; exact ht.g5⟩
      let rb := n + 5
      let ma := (sc2.mem.upd 0 (encodeLE 8 (n + 6))).upd rb (List.replicate 3000 0)
      let sa : State := { sc2 with mem := ma, locals := sc2.locals.upd 23 (.ptr rb 0) }
      have ea : ExS Gen.prog sc2 (.alloc 23 3000) .normal sa := exec_alloc (hfc2.allocAt (by omega)) 23 3000
      have hma : ∀ x, x ≠ 0 → x ≠ rb → ma x = sc2.mem x := fun x a b => by
        simp only [ma]; rw [Mem.upd_ne b, Mem.upd_ne a]
      have hfa : Fresh ma (n + 6) := hfc2.after_alloc _
      have hta : TablesIn ma := (htc2.upd0 _).upd _ (by rw [Mem.upd_ne (by omega)]; exact hfc2.2.2 _ (Nat.le_refl _))
      have hpa : ma posBlock = some (encode q) := by rw [hma _ (by decide) (by simp only [posBlock, rb]; omega)]; exact hpc2
      have hrb : ReplyBuf ma rb := by
        refine ⟨List.replicate 3000 0, Mem.upd_eq, by simp only [List.length_replicate]; omega, ?_, ?_, ?_⟩
        · simp only [rb]; omega
        · simp only [rb, posBlock]; omega
        · exact fresh_not_table hfc2 htc2 (by simp only [rb]; omega)
      obtain ⟨sr, cnt, kf, er, hcnt, hpr, hfr, hkk, hkb, hor⟩ := hrec hicq ma rb (n + 6) hpa hta hfa hrb
        (by simp only [recBudget]; omega)
      have hkb2 : kf ≤ n + 6 + 1000000000 := by
        have h := hkb
        simp only [recBudget] at h
        omega
      let sb1 : State := { sa with mem := sr.mem, locals := sa.locals.upd 25 (.int IntTy.u64 cnt) }
      have ecr : ExS Gen.prog sa (.call (some 25) 35 [(.var 0), (.var 23), (.cast ⟨64, false⟩ (.const (.int ⟨32, true⟩ 600))),
          (.cast ⟨8, false⟩ (.bin .ne (some ⟨32, true⟩) (.const (.int ⟨32, true⟩ 1)) (.const (.int ⟨32, true⟩ 0))))]) .normal sb1 :=
        ExS.call_dst (EvArgs.cons (EvE.var (by simp [sa, sc2, sc1, s6, s6a, s5, s4, Locals.upd]; exact hI.l0))
          (EvArgs.cons (EvE.var (v := .ptr rb 0) (by simp [sa, Locals.upd]))
          (EvArgs.cons (EvE_of_eval (n := 3) (by rfl))
          (EvArgs.cons (EvE_of_eval (n := 3) (by rfl)) EvArgs.nil)))) rfl rfl
          (by rw [show sa.ro = false from hI.ro]; exact er)
      let sb2 : State := { sb1 with locals := sb1.locals.upd 24 (.int IntTy.u64 cnt) }
      have e24 : ExS Gen.prog sb1 (.set 24 (.var 25)) .normal sb2 := ExS.set (EvE.var (by simp [sb1, Locals.upd]))
      let keep := decide (cnt ≠ 0)
      let sb3 : State := { sb2 with locals := sb2.locals.upd 19 (u8 (if keep then 1 else 0)) }
      have e19 : ExS Gen.prog sb2 (.set 19 (.cast ⟨8, false⟩ (.bin .ne (some ⟨32, true⟩) (.bin .ne (some ⟨64, false⟩)
          (.var 24) (.cast ⟨64, false⟩ (.const (.int ⟨32, true⟩ 0)))) (.const (.int ⟨32, true⟩ 0))))) .normal sb3 := by
        apply ExS.set
        have hne : EvE Gen.prog sb2 (.bin .ne (some ⟨64, false⟩) (.var 24) (.cast ⟨64, false⟩ (.const (.int ⟨32, true⟩ 0))))
            (boolVal keep) := by
          apply EvE_of_eval (n := 4)
          have h24 : sb2.locals 24 = some (.int IntTy.u64 cnt) := by simp [sb2, Locals.upd]
          simp [evalExpr, h24, evalCast, evalBin, isPtr, evalBinInt, binInt, intOf, IntTy.u64, IntTy.toInt, IntTy.wrap,
            IntTy.modulus, Res.bind, keep]
        exact evB_u8 hne
      have e7 : ExS Gen.prog s6 lp7 .normal sb3 :=
        ExS.seq ec2 (ExS.ite (bc := true) (vc := boolVal true) (EvE.var (by simp [sc2, Locals.upd, hicq]))
          (truthy_boolVal _) (ExS.seq ea (ExS.seq (ExS.seq ecr e24) e19)))
      have hl7 : ∀ x, x < 19 → sb3.locals x = s6.locals x := fun x hx => by
        simp [sb3, sb2, sb1, sa, Locals.upd, show x ≠ 19 by omega, show x ≠ 24 by omega, show x ≠ 25 by omega,
          show x ≠ 23 by omega]
        exact hlc x hx
      have hm7 : ∀ x, x ≠ 0 → x ≠ rb → x < n + 6 → x ≠ posBlock → sb3.mem x = sc2.mem x := fun x a b c d => by
        show sr.mem x = _; rw [hor x a b c d, hma x a b]
      have hk7 : ∀ x, x ≠ 0 → x ≠ posBlock → s.mem x ≠ none → sb3.mem x = s.mem x := fun x a b c => by
        have hlt : x < n + 1 := Nat.lt_of_not_le (fun h => c (hf.2.2 x h))
        rw [hm7 x a (by omega) (by omega) b]; exact hkc x a b c
      obtain ⟨s', e', hb', hp', hx1, hx2, hx3, hx4⟩ := tail sb3 U kf keep e7 (by simp [sb3, Locals.upd]) hl7 hpr
        (by rw [hm7 _ hub0 (by omega) (by omega) (Ne.symm hpu)]; exact huc2) hfr (by omega) hk7 hI.ro
      refine ⟨s', e', ?_, hp', hx1, hx2, hx3, by obtain ⟨f, hf1, hf2⟩ := hx4; exact ⟨f, hf1, by omega⟩⟩
      have hk : specKeep p fuel mv = keep := by
        have hsk : specKeep p fuel mv = (!(p.play mv).inCheck p.side &&
            !((p.play mv).inCheck (p.play mv).side &&
              (Position.legalAux fuel (p.play mv)).isEmpty)) := by
          simp [specKeep, hpd]
        rw [hsk]
        simp only [ic, icq, q] at hic hicq
        rw [hic, hicq]
        simp only [Bool.not_true, Bool.true_and, Bool.not_false, Bool.true_and, Bool.not_not]
        cases hX : (Position.legalAux fuel (p.play mv)).isEmpty
        · have hne : cnt ≠ 0 := hcnt.2 (by rw [hX]; simp)
          simp [hX, hne, keep]
        · have hz : cnt = 0 := by
            cases hb : cnt with
            | zero => rfl
            | succ m => exact absurd (hcnt.1 (by omega)) (by rw [hX]; simp)
          simp [hX, hz, keep]
      rw [hk]; exact hb'
  · -- the drop leaves the own king in check: dropped, no recursion
    rw [hic] at hc7
    let s7 : State := { s6 with locals := s6.locals.upd 22 (.int ⟨32, true⟩ 0) }
    have e7 : ExS Gen.prog s6 lp7 .normal s7 :=
      ExS.seq (ExS.ite (bc := false) hc7 rfl (ExS.set (EvE.const _)))
        (ExS.ite (bc := false) (EvE.var (v := .int ⟨32, true⟩ 0) (by simp [s7, Locals.upd])) rfl ExS.skip)
    have hl7 : ∀ x, x < 19 → s7.locals x = s6.locals x := fun x hx => by
      simp [s7, Locals.upd, show x ≠ 22 by omega]
    have l19s : s7.locals 19 = s6.locals 19 := by simp [s7, Locals.upd]
    have l19f : s7.locals 19 = some (u8 (if false then 1 else 0)) := by rw [l19s, l19, hic]; rfl
    obtain ⟨s', e', hb', hp', hx1, hx2, hx3, hx4⟩ := tail s7 U (n + 4) false e7 l19f hl7 hp6 hu6 hf6 (by omega) hkeep6 hI.ro
    refine ⟨s', e', ?_, hp', hx1, hx2, hx3, by obtain ⟨f, hf1, hf2⟩ := hx4; exact ⟨f, hf1, by omega⟩⟩
    have hk : specKeep p fuel mv = false := by
      simp only [specKeep, ic, q] at hic ⊢
      rw [hic]; simp
    rw [hk]; exact hb'

end Shogi.C.Proofs
