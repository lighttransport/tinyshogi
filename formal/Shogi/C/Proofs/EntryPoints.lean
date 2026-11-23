/-
  M6, proof half: the public entry points of `src/shogi.c`.

  `shogi_generate_legal_mut` (fid 36): the non-copying move generator the
  search calls directly. The wrapper is thin (two null checks and one call
  to `generate_legal_mut_internal`); the content is in
  `generate_legal_refines`, which this theorem wraps. `hrec` is the
  uchifuzume sub-spec hypothesis — the recursive reply counts are assumed,
  not derived (see PLAN.md, M4).

  `shogi_position_copy_active` (fid 37) copies a full 41088-byte
  `ShogiPosition` into a caller-invisible `work` block.
  `shogi_position_copy_active_spec` proves that execution: the 14-step `ExS`
  chain, the frame property (every block other than `dst` is unchanged), and
  the bytes at every field the rules core reads (board, hand, side,
  move_number, hash, king squares, clamped history length, history keys,
  mover/check bytes and the stored length).

  `shogi_generate_legal` (fid 38) copies the same way and then calls the
  internal generator on the copied block. It remains out of scope here:
  `generate_legal_refines` assumes `m posBlock = some (encode p)`, the
  114-byte encoded *prefix*, whereas the copy writes a full 41088-byte
  struct, so the copy spec cannot yet be composed with the internal theorem
  (see PLAN.md, M6).
-/
import Shogi.C.Proofs.LegalMain

namespace Shogi.C.Proofs
variable {posBlock : Nat}
open MiniC Shogi Shogi.C
variable {m : Mem} {b o o' n : Nat} {bs : List UInt8} {blk : Block}

theorem write_some2 (b o : Nat) (bs : List UInt8) (hb : m b = some blk) :
    (m.write b o bs) b = some (blk.take o ++ bs ++ blk.drop (o + bs.length)) := by
  cases hb' : m b with
  | none => rw [hb'] at hb; cases hb
  | some blk' =>
      have : blk' = blk := Option.some.inj (hb'.symm.trans hb)
      subst this; simp [Mem.write, hb', Mem.upd_eq]

theorem hlen2 (hfit : o + bs.length ≤ blk.length) :
    (blk.take o ++ bs ++ blk.drop (o + bs.length)).length = blk.length := by
  simp [List.length_take, List.length_append, List.length_drop,
    Nat.min_eq_left (show o ≤ blk.length by omega)]
  omega

theorem readBytes_write_disjoint (hb : m b = some blk) (hfit : o + bs.length ≤ blk.length)
    (h : o' + n ≤ o ∨ o + bs.length ≤ o') :
    readBytes (m.write b o bs) b o' n = readBytes m b o' n := by
  have hw := write_some2 b o bs hb
  have hlen := hlen2 hfit
  have hlo : (blk.take o).length = o := by
    simp [List.length_take, Nat.min_eq_left (show o ≤ blk.length by omega)]
  have hr1 : readBytes (m.write b o bs) b o' n =
      if o' + n ≤ (blk.take o ++ bs ++ blk.drop (o + bs.length)).length then
        .ok ((blk.take o ++ bs ++ blk.drop (o + bs.length)).drop o' |>.take n) else .ub := by
    rw [MiniC.readBytes.eq_def, hw]
  have hr2 : readBytes m b o' n =
      if o' + n ≤ blk.length then .ok ((blk.drop o').take n) else .ub := by
    rw [MiniC.readBytes.eq_def, hb]
  rw [hr1, hr2, hlen]
  split
  · rcases h with h | h
    · have ho : o' ≤ o := by omega
      have drop1 : (blk.take o ++ bs ++ blk.drop (o + bs.length)).drop o'
          = (blk.drop o').take (o - o') ++ bs ++ blk.drop (o + bs.length) := by
        rw [List.drop_append, List.length_append, hlo]
        rw [List.drop_append]
        rw [List.drop_take, hlo, show o' - o = 0 by omega, List.drop_zero,
          show o' - (o + List.length bs) = 0 by omega, List.drop_zero]
      rw [drop1]
      have htn : n ≤ o - o' := by omega
      have htn' : ((blk.drop o').take (o - o')).length = o - o' := by
        simp [List.length_take, Nat.min_eq_left (show o - o' ≤ blk.length - o' by omega)]
      have htk : n ≤ ((blk.drop o').take (o - o') ++ bs).length := by
        rw [List.length_append, htn']; omega
      rw [List.take_append_of_le_length htk]
      rw [List.take_append_of_le_length (show n ≤ ((blk.drop o').take (o - o')).length by
        rw [htn']; exact htn)]
      rw [List.take_take, Nat.min_eq_left htn]
    · have ho : o + bs.length ≤ o' := h
      have drop2 : (blk.take o ++ bs ++ blk.drop (o + bs.length)).drop o' = blk.drop o' := by
        rw [List.drop_append]
        rw [List.length_append, hlo]
        rw [List.drop_of_length_le (show (List.take o blk ++ bs).length ≤ o' by
          rw [List.length_append, hlo]; omega)]
        rw [List.nil_append]
        rw [List.drop_drop, show o + bs.length + (o' - (o + bs.length)) = o' by omega]
      rw [drop2]
  · rfl

theorem readBytes_write_window (hb : m b = some blk) (hfit : o + bs.length ≤ blk.length)
    (h : o ≤ o' ∧ o' + k ≤ o + bs.length) :
    readBytes (m.write b o bs) b o' k = .ok ((bs.drop (o' - o)).take k) := by
  have hw := write_some2 b o bs hb
  have hlen := hlen2 hfit
  have hlo : (blk.take o).length = o :=
    by simp [List.length_take, Nat.min_eq_left (show o ≤ blk.length by omega)]
  have hdrop : (blk.take o ++ bs ++ blk.drop (o + bs.length)).drop o'
      = bs.drop (o' - o) ++ blk.drop (o + bs.length) := by
    rw [List.drop_append, List.length_append, hlo]
    rw [show o' - (o + List.length bs) = 0 by omega, List.drop_zero]
    rw [List.drop_append, hlo]
    rw [List.drop_of_length_le (show List.length (List.take o blk) ≤ o' by rw [hlo]; omega)]
    rw [List.nil_append]
  rw [MiniC.readBytes.eq_def, hw]
  split
  · rename_i heq; cases heq
  rename_i blk' heq
  rw [Option.some.inj heq] at hlen
  rw [hlen]
  rw [Option.some.inj heq] at hdrop
  have hin : o' + k ≤ blk.length := by
    omega
  rw [ite_eq_left hin, hdrop]
  congr 1
  have hk : k ≤ (bs.drop (o' - o)).length := by
    set_option linter.unusedSimpArgs false in
    simp [List.length_drop, Nat.min_eq_left (show o' - o ≤ bs.length by omega)]; omega
  rw [List.take_append_of_le_length hk]
/-- **`shogi_generate_legal_mut` refines `Position.legalAux`** (M6).  With an
    output array of at least 7200 moves, `shogi_generate_legal_mut(position, moves, capacity)`
    writes the bytes of a reordering of `legalAux (fuel + 1) p`, returns its length, and
    leaves the position block unchanged.  The recursive uchifuzume replies are assumed
    via `hrec`. -/
theorem shogi_generate_legal_mut_spec (p : Position) (hS : p.Shaped) (hK : KingsUnique p)
    (hw : ∀ i, p.hand p.side i < 256) (fuel : Nat)
    (rem : Nat)
    (hrec : ∀ mv ∈ p.pseudoMoves, Position.isPawnDrop mv →
      (p.play mv).inCheck (p.play mv).side → RecSpec (posBlock := posBlock) fuel (rem - recDelta) (p.play mv))
    {m : Mem} {n cap mb mo : Nat} {blk : Block}
    (hm : m posBlock = some (encode p)) (ht : TablesIn m) (hf : Fresh m n)
    (hnc : p.inCheck p.side.opp = false)
    (h64 : n + rem + 2000000 < 2 ^ 64)
    (hglobal : n + 401 * rem < 2 ^ 64)
    (hrembig : recDelta ≤ rem) (hremub : rem ≤ 200 * recDelta)
    (hmb : m mb = some blk) (hlen : mo + 5 * cap ≤ blk.length) (hmb0 : mb ≠ 0)
    (hcap : cap < 2 ^ 64) (hpm : posBlock ≠ mb) (hmbt : mb < 8192 ∨ 8196 < mb)
    (hcap7200 : 7200 ≤ cap) :
    ∃ K : List (List UInt8), K.Perm ((Position.legalAux (fuel + 1) p).map (moveBytes p)) ∧ ∃ s' cb,
      ExS Gen.prog ⟨frameLocals Gen.shogi_generate_legal_mut.params
          [posPtr' posBlock, .ptr mb mo, .int IntTy.u64 cap], m, false⟩
        Gen.shogi_generate_legal_mut.body (.ret (some (.int ⟨64, false⟩ K.length))) s' ∧
      Buf s'.mem mb mo cb 0 cap K ∧ s'.mem posBlock = some (encode p) ∧
      (∀ x, x ≠ 0 → x ≠ mb → x < n → x ≠ posBlock → m x ≠ none → s'.mem x = m x) ∧
      ∃ f, Fresh s'.mem f ∧ f ≤ n + rem := by
  let s0 : State := ⟨frameLocals Gen.shogi_generate_legal_mut.params
    [posPtr' posBlock, .ptr mb mo, .int IntTy.u64 cap], m, false⟩
  -- argument guard: neither pointer is null, so the early return is not taken
  have hguard : EvE Gen.prog s0 (.lor (.bin .eq none (.var 0) (.const .null))
      (.bin .eq none (.var 1) (.const .null))) (boolVal false) := by
    refine EvE_of_eval (n := 4) ?_
    rfl
  have e0 : ExS Gen.prog s0 (.ite (.lor (.bin .eq none (.var 0) (.const .null))
      (.bin .eq none (.var 1) (.const .null))) (.ret (some (.cast ⟨64, false⟩ (.const (.int ⟨32, true⟩ 0)))))
      .skip) .normal s0 := ExS.ite (bc := false) hguard rfl ExS.skip
  -- the enforce_uchifuzume argument evaluates to u8 1
  have hne : EvE Gen.prog s0 (.cast ⟨8, false⟩ (.bin .ne (some ⟨32, true⟩) (.const (.int ⟨32, true⟩ 1))
      (.const (.int ⟨32, true⟩ 0)))) (u8 1) := by
    refine EvE_of_eval (n := 4) ?_
    rfl
  have hargs : EvArgs Gen.prog s0 [(.var 0), (.var 1), (.var 2),
      (.cast ⟨8, false⟩ (.bin .ne (some ⟨32, true⟩) (.const (.int ⟨32, true⟩ 1)) (.const (.int ⟨32, true⟩ 0))))]
      [(.ptr posBlock 0), (.ptr mb mo), (.int IntTy.u64 cap), (.int IntTy.u8 1)] :=
    EvArgs.cons (EvE.var rfl)
      (EvArgs.cons (EvE.var rfl)
        (EvArgs.cons (EvE.var rfl)
          (EvArgs.cons hne EvArgs.nil)))
  obtain ⟨K, hperm, s', cb, e, hb, hp, hframe, f, hf, hfl⟩ :=
    generate_legal_refines (fuel := fuel) (mb := mb) (mo := mo) (cap := cap)
      hS hK hw hcap7200 rem hrec hm ht hf hnc h64 hglobal hrembig hremub hmb hlen hmb0 hcap hpm hmbt
  have e1 : ExS Gen.prog s0
      (.call (some 3) Gen.fid_generate_legal_mut_internal
        [(.var 0), (.var 1), (.var 2),
         (.cast ⟨8, false⟩ (.bin .ne (some ⟨32, true⟩) (.const (.int ⟨32, true⟩ 1)) (.const (.int ⟨32, true⟩ 0))))])
      .normal { s0 with mem := s'.mem, locals := s0.locals.upd 3 (.int IntTy.u64 K.length) } := by
    have hf2 : Gen.prog Gen.fid_generate_legal_mut_internal = some Gen.generate_legal_mut_internal := rfl
    have hlen2 : Gen.generate_legal_mut_internal.params.length = 4 := rfl
    have hro0 : s0.ro = false := rfl
    exact ExS.call_dst hargs hf2 hlen2 (by rw [hro0]; exact e)
  have e2 : ExS Gen.prog { s0 with mem := s'.mem, locals := s0.locals.upd 3 (.int IntTy.u64 K.length) }
      (.ret (some (.var 3))) (.ret (some (.int ⟨64, false⟩ K.length)))
      { s0 with mem := s'.mem, locals := s0.locals.upd 3 (.int IntTy.u64 K.length) } :=
    ExS.ret (EvE.var rfl)
  refine ⟨K, hperm, { s0 with mem := s'.mem, locals := s0.locals.upd 3 (.int IntTy.u64 K.length) }, cb,
    ?_, hb, hp, hframe, f, hf, hfl⟩
  · refine ExS.seq e0 (ExS.seq e1 e2)

/-- A `memcpy` from `[src, soff+k)` into `[dst, off+k)`. -/
theorem memcpy_spec {s : State} {dst src off soff k : Nat}
    {SB DB : Block} {len : Expr}
    (hd0 : s.locals 0 = some (.ptr dst 0)) (hs0 : s.locals 1 = some (.ptr src 0))
    (hd : s.mem dst = some DB) (hs : s.mem src = some SB)
    (hdst : off + k ≤ DB.length) (hsrc : soff + k ≤ SB.length)
    (hov : (dst ≠ src || off + k ≤ soff || soff + k ≤ off) = true)
    (hro : s.ro = false) (hlen : EvE Gen.prog s len (.int ⟨64, false⟩ k)) :
    ExS Gen.prog s (.memcpy (.field (.var 0) off) (.field (.var 1) soff) len)
      .normal { s with mem := s.mem.write dst off ((SB.drop soff).take k) } := by
  have hfd : EvE Gen.prog s (.field (.var 0) off) (.ptr dst off) :=
    EvE.field (EvE.var hd0) (by simp [ptrAddN, hd]; omega)
  have hfs : EvE Gen.prog s (.field (.var 1) soff) (.ptr src soff) :=
    EvE.field (EvE.var hs0) (by simp [ptrAddN, hs]; omega)
  have hr : readBytes s.mem src soff k = .ok ((SB.drop soff).take k) := by
    simp only [readBytes, hs, if_pos hsrc]
  have hw : writeBytes s.mem dst off ((SB.drop soff).take k) = .ok (s.mem.write dst off ((SB.drop soff).take k)) :=
    writeBytes_ok hd (by simp [List.length_take, List.length_drop]; omega)
  exact ExS.memcpy hfd hfs hlen hro hov hr hw

theorem take_length_of_le {α : Type _} {l : List α} {n : Nat} (h : n ≤ l.length) :
    (l.take n).length = n := by
  simp [List.length_take, Nat.min_eq_left h]

/-! ## `shogi_position_copy_active` (fid 37) -/

/-- `encodeLE` after `decodeLE` is the identity on length-`n` blocks. -/
theorem encodeLE_decodeLE (bs : List UInt8) : encodeLE bs.length (decodeLE bs) = bs := by
  induction bs with
  | nil => rfl
  | cons b bs ih =>
      have hb : b.toNat < 256 := b.toNat_lt
      simp only [encodeLE, decodeLE, List.length_cons]
      have hq : (b.toNat + 256 * decodeLE bs) / 256 = decodeLE bs := by omega
      have hm : (b.toNat + 256 * decodeLE bs) % 256 = b.toNat := by omega
      rw [hq, hm]
      have hbi : b.toNat.toUInt8 = b := by simp
      rw [hbi, ih]

/-- `.take n` is the identity on an `encodeLE n` block. -/
theorem List.take_encodeLE {v : Nat} (n : Nat) : (encodeLE n v).take n = encodeLE n v :=
  List.take_of_length_le (by rw [encodeLE_length]; exact Nat.le_refl _)

/-- Writing into a block yields a block of the same length. -/
theorem block_len_after_write {m : Mem} {b o : Nat} {bs : List UInt8} {blk : Block}
    (hb : m b = some blk) (hfit : o + bs.length ≤ blk.length) :
    ∃ blk', (m.write b o bs) b = some blk' ∧ blk'.length = blk.length :=
  ⟨blk.take o ++ bs ++ blk.drop (o + bs.length), write_some2 b o bs hb, hlen2 hfit⟩

theorem shogi_position_copy_active_spec {M : Mem} {src dst : Nat} {SB DB : Block}
    (hsrc : M src = some SB) (hlen : SB.length = 41088)
    (hd : M dst = some DB) (hlen' : DB.length = 41088) (hne : dst ≠ src) (hd0 : dst ≠ 0) :
    ∃ s', ExS Gen.prog ⟨frameLocals Gen.shogi_position_copy_active.params [.ptr dst 0, .ptr src 0], M, false⟩
        Gen.shogi_position_copy_active.body .normal s' ∧
      (∀ x, x ≠ dst → s'.mem x = M x) ∧
      readBytes s'.mem dst 0 81 = .ok (SB.take 81) ∧
      readBytes s'.mem dst 81 14 = .ok ((SB.drop 81).take 14) ∧
      readBytes s'.mem dst 96 4 = .ok ((SB.drop 96).take 4) ∧
      readBytes s'.mem dst 100 4 = .ok ((SB.drop 100).take 4) ∧
      readBytes s'.mem dst 104 8 = .ok ((SB.drop 104).take 8) ∧
      readBytes s'.mem dst 112 1 = .ok ((SB.drop 112).take 1) ∧
      readBytes s'.mem dst 113 1 = .ok ((SB.drop 113).take 1) ∧
      readBytes s'.mem dst 120 (8 * min (decodeLE ((SB.drop 41080).take 8)) 4096) =
        .ok ((SB.drop 120).take (8 * min (decodeLE ((SB.drop 41080).take 8)) 4096)) ∧
      readBytes s'.mem dst 32888 (min (decodeLE ((SB.drop 41080).take 8)) 4096) =
        .ok ((SB.drop 32888).take (min (decodeLE ((SB.drop 41080).take 8)) 4096)) ∧
      readBytes s'.mem dst 36984 (min (decodeLE ((SB.drop 41080).take 8)) 4096) =
        .ok ((SB.drop 36984).take (min (decodeLE ((SB.drop 41080).take 8)) 4096)) ∧
      readBytes s'.mem dst 41080 8 = .ok (encodeLE 8 (min (decodeLE ((SB.drop 41080).take 8)) 4096)) ∧
      ∃ WB', s'.mem dst = some WB' ∧ WB'.length = 41088 := by
  let hl : Nat := decodeLE ((SB.drop 41080).take 8)
  let h' := min hl 4096
  have h'_le : h' ≤ 4096 := Nat.min_le_right hl 4096
  let s0 : State := ⟨frameLocals Gen.shogi_position_copy_active.params [.ptr dst 0, .ptr src 0], M, false⟩
  -- argument guard: neither pointer is null, so the early return is not taken
  have hguard : EvE Gen.prog s0 (.lor (.bin .eq none (.var 0) (.const .null))
      (.bin .eq none (.var 1) (.const .null))) (boolVal false) := by
    refine EvE_of_eval (n := 4) ?_
    rfl
  have e0 : ExS Gen.prog s0 (.ite (.lor (.bin .eq none (.var 0) (.const .null))
      (.bin .eq none (.var 1) (.const .null))) (.ret none) .skip) .normal s0 :=
    ExS.ite (bc := false) hguard rfl ExS.skip
  -- memcpy board
  let m1 := s0.mem.write dst 0 (SB.take 81)
  have e1 : ExS Gen.prog s0 (.memcpy (.field (.var 0) 0) (.field (.var 1) 0) (.const (.int ⟨64, false⟩ 81)))
      .normal { s0 with mem := m1 } :=
    memcpy_spec (by rfl) (by rfl) hd hsrc (by omega) (by omega) (by simp [hne]) rfl (EvE.const _)
  have hd1 : m1 dst = some (SB.take 81 ++ DB.drop 81) := by
    show M.write dst 0 (SB.take 81) dst = some (SB.take 81 ++ DB.drop 81)
    rw [Mem.write_eq (o := 0) (bs := SB.take 81) hd]
    simp [List.length_take, hlen]
  -- memcpy hand
  let m2 := m1.write dst 81 ((SB.drop 81).take 14)
  have hsrc1 : m1 src = some SB := by
    show s0.mem.write dst 0 (SB.take 81) src = some SB
    rw [Mem.write_ne hne.symm]; exact hsrc
  have e2 : ExS Gen.prog { s0 with mem := m1 } (.memcpy (.field (.var 0) 81) (.field (.var 1) 81) (.const (.int ⟨64, false⟩ 14)))
      .normal { s0 with mem := m2 } :=
    memcpy_spec (by rfl) (by rfl) hd1 hsrc1
      (by have htk : (SB.take 81).length = 81 := by simp [List.length_take, hlen]
          simp [List.length_append, htk, List.length_drop, hlen'])
      (by simp [hlen])
      (by simp [hne])
      rfl
      (EvE.const _)
  have hd2 : m2 dst = some (SB.take 95 ++ DB.drop 95) := by
    have hd1' : M.write dst 0 (SB.take 81) dst = some (SB.take 81 ++ DB.drop 81) := hd1
    simp only [m2, m1, s0]
    rw [Mem.write_eq (o := 81) (bs := (SB.drop 81).take 14) hd1']
    congr 1
    have htk : (SB.take 81).length = 81 := by simp [List.length_take, hlen]
    have hT : List.take 81 (SB.take 81 ++ DB.drop 81) = SB.take 81 := List.take_left' htk
    have hD : List.drop 81 (SB.take 81 ++ DB.drop 81) = DB.drop 81 := List.drop_left' htk
    have hD95 : List.drop 95 (SB.take 81 ++ DB.drop 81) = DB.drop 95 := by
      rw [show 95 = 81 + 14 from rfl, ← List.drop_drop, hD, List.drop_drop]
    have lenT : ((SB.drop 81).take 14).length = 14 := by
      simp [List.length_take, List.length_drop, hlen]
    rw [hT, show 81 + ((SB.drop 81).take 14).length = 95 from by rw [lenT], hD95, ← List.take_add]
  have hblk2 : (SB.take 95 ++ DB.drop 95).length = 41088 := by
    simp [List.length_append, List.length_take, List.length_drop, hlen, hlen']
  -- side store [96,100)
  let s1 := { s0 with mem := m2 }
  have hfr : s1.mem src = some SB := by
    simp only [s1, m2, m1, s0]
    rw [Mem.write_ne hne.symm, Mem.write_ne hne.symm]
    exact hsrc
  have hside : EvE Gen.prog s1 (.load (.int ⟨32, false⟩) (.field (.var 1) 96))
      (.int ⟨32, false⟩ (decodeLE ((SB.drop 96).take 4))) := by
    refine EvE_of_eval (n := 20) ?_
    have hl1 : s1.locals 1 = some (.ptr src 0) := rfl
    simp [evalExpr, hfr, hl1, hlen, Res.bind_eq, Res.bind_ok, ptrAddN, load, readBytes, Ty.size, IntTy.bytes, IntTy.u32, IntTy.u64, IntTy.u8, IntTy.i32]
  let m3 := m2.write dst 96 (encodeLE 4 (decodeLE ((SB.drop 96).take 4)))
  obtain ⟨blk3, hd3, hd3L⟩ := block_len_after_write (b := dst) (o := 96) (bs := encodeLE 4 (decodeLE ((SB.drop 96).take 4))) hd2 (by
    simp [List.length_append, List.length_take, List.length_drop, hlen, hlen', encodeLE_length])
  have hL3 : blk3.length = 41088 := by rw [hd3L]; exact hblk2
  have e3 : ExS Gen.prog s1 (.store (.int ⟨32, false⟩) (.field (.var 0) 96) (.load (.int ⟨32, false⟩) (.field (.var 1) 96)))
      .normal { s1 with mem := m3 } :=
    store_int_field (s := s1) (o := 0) (b := dst) (i := 96) (t := ⟨32, false⟩) (v := decodeLE ((SB.drop 96).take 4)) (e := .load (.int ⟨32, false⟩) (.field (.var 1) 96)) (blk := SB.take 95 ++ DB.drop 95) (hj := rfl) (hb := hd2)
      (hi := by rw [hblk2]; show 0 + 96 + 4 ≤ 41088; omega)
      (he := hside) (hro := rfl) (hlen := by simp [encodeLE_length])
  -- move_number store [100,104)
  let s2 := { s1 with mem := m3 }
  have hfr2 : s2.mem src = some SB := by
    simp only [s2, s1, m3, m2, m1, s0]
    rw [Mem.write_ne hne.symm, Mem.write_ne hne.symm, Mem.write_ne hne.symm]
    exact hsrc
  have hmn : EvE Gen.prog s2 (.load (.int ⟨32, false⟩) (.field (.var 1) 100))
      (.int ⟨32, false⟩ (decodeLE ((SB.drop 100).take 4))) := by
    refine EvE_of_eval (n := 20) ?_
    have hl1 : s2.locals 1 = some (.ptr src 0) := rfl
    simp [evalExpr, hfr2, hl1, hlen, Res.bind_eq, Res.bind_ok, ptrAddN, load, readBytes, Ty.size, IntTy.bytes, IntTy.u32, IntTy.u64, IntTy.u8, IntTy.i32]
  let m4 := m3.write dst 100 (encodeLE 4 (decodeLE ((SB.drop 100).take 4)))
  obtain ⟨blk4, hd4, hd4L⟩ := block_len_after_write (b := dst) (o := 100) (bs := encodeLE 4 (decodeLE ((SB.drop 100).take 4))) hd3 (by
    rw [hL3, encodeLE_length]; omega)
  have hL4 : blk4.length = 41088 := by rw [hd4L]; exact hL3
  have e4 : ExS Gen.prog s2 (.store (.int ⟨32, false⟩) (.field (.var 0) 100) (.load (.int ⟨32, false⟩) (.field (.var 1) 100)))
      .normal { s2 with mem := m4 } :=
    store_int_field (s := s2) (o := 0) (b := dst) (i := 100) (t := ⟨32, false⟩) (v := decodeLE ((SB.drop 100).take 4)) (e := .load (.int ⟨32, false⟩) (.field (.var 1) 100)) (blk := blk3) (hj := rfl) (hb := hd3)
      (hi := by rw [hL3]; show 0 + 100 + 4 ≤ 41088; omega)
      (he := hmn) (hro := rfl) (hlen := by simp [encodeLE_length])
  -- hash store [104,112)
  let s3 := { s2 with mem := m4 }
  have hfr3 : s3.mem src = some SB := by
    simp only [s3, s2, s1, m4, m3, m2, m1, s0]
    rw [Mem.write_ne hne.symm, Mem.write_ne hne.symm, Mem.write_ne hne.symm, Mem.write_ne hne.symm]
    exact hsrc
  have hhash : EvE Gen.prog s3 (.load (.int ⟨64, false⟩) (.field (.var 1) 104))
      (.int ⟨64, false⟩ (decodeLE ((SB.drop 104).take 8))) := by
    refine EvE_of_eval (n := 20) ?_
    have hl1 : s3.locals 1 = some (.ptr src 0) := rfl
    simp [evalExpr, hfr3, hl1, hlen, Res.bind_eq, Res.bind_ok, ptrAddN, load, readBytes, Ty.size, IntTy.bytes, IntTy.u32, IntTy.u64, IntTy.u8, IntTy.i32]
  let m5 := m4.write dst 104 (encodeLE 8 (decodeLE ((SB.drop 104).take 8)))
  obtain ⟨blk5, hd5, hd5L⟩ := block_len_after_write (b := dst) (o := 104) (bs := encodeLE 8 (decodeLE ((SB.drop 104).take 8))) hd4 (by
    rw [hL4, encodeLE_length]; omega)
  have hL5 : blk5.length = 41088 := by rw [hd5L]; exact hL4
  have e5 : ExS Gen.prog s3 (.store (.int ⟨64, false⟩) (.field (.var 0) 104) (.load (.int ⟨64, false⟩) (.field (.var 1) 104)))
      .normal { s3 with mem := m5 } :=
    store_int_field (s := s3) (o := 0) (b := dst) (i := 104) (t := ⟨64, false⟩) (v := decodeLE ((SB.drop 104).take 8)) (e := .load (.int ⟨64, false⟩) (.field (.var 1) 104)) (blk := blk4) (hj := rfl) (hb := hd4)
      (hi := by rw [hL4]; show 0 + 104 + 8 ≤ 41088; omega)
      (he := hhash) (hro := rfl) (hlen := by simp [encodeLE_length])
  -- king BLACK store [112,113)
  let s4 := { s3 with mem := m5 }
  have hfr4 : s4.mem src = some SB := by
    simp only [s4, s3, s2, s1, m5, m4, m3, m2, m1, s0]
    rw [Mem.write_ne hne.symm, Mem.write_ne hne.symm, Mem.write_ne hne.symm, Mem.write_ne hne.symm, Mem.write_ne hne.symm]
    exact hsrc
  have hk0 : EvE Gen.prog s4 (.load (.int ⟨8, false⟩) (.index (.field (.var 1) 112) (.const (.int ⟨32, true⟩ 0)) 1))
      (.int IntTy.u8 (decodeLE ((SB.drop 112).take 1))) := by
    refine EvE_of_eval (n := 30) ?_
    have hl1 : s4.locals 1 = some (.ptr src 0) := rfl
    have htoInt : (⟨32, true⟩ : IntTy).toInt 0 = 0 := rfl
    simp [evalExpr, hfr4, hl1, hlen, htoInt, Res.bind_eq, Res.bind_ok, ptrAdd, ptrAddN, load, readBytes, Ty.size, IntTy.bytes, IntTy.u8, IntTy.u32, IntTy.u64, IntTy.i32]
  let m6 := m5.write dst 112 (encodeLE 1 (decodeLE ((SB.drop 112).take 1)))
  obtain ⟨blk6, hd6, hd6L⟩ := block_len_after_write (b := dst) (o := 112) (bs := encodeLE 1 (decodeLE ((SB.drop 112).take 1))) hd5 (by
    rw [hL5, encodeLE_length]; omega)
  have hL6 : blk6.length = 41088 := by rw [hd6L]; exact hL5
  have e6 : ExS Gen.prog s4 (.store (.int ⟨8, false⟩) (.index (.field (.var 0) 112) (.const (.int ⟨32, true⟩ 0)) 1)
      (.load (.int ⟨8, false⟩) (.index (.field (.var 1) 112) (.const (.int ⟨32, true⟩ 0)) 1)))
      .normal { s4 with mem := m6 } :=
    have paEv : EvE Gen.prog s4 (.index (.field (.var 0) 112) (.const (.int ⟨32, true⟩ 0)) 1) (.ptr dst 112) := by
      refine EvE_of_eval (n := 30) ?_
      have hl0 : s4.locals 0 = some (.ptr dst 0) := rfl
      have htoInt : (⟨32, true⟩ : IntTy).toInt 0 = 0 := rfl
      have hd5' : s4.mem dst = some blk5 := hd5
      simp [evalExpr, hd5', hL5, hl0, htoInt, Res.bind_eq, Res.bind_ok, ptrAdd, ptrAddN]
    have hm : store s4.mem (Ty.int ⟨8, false⟩) (Val.ptr dst 112)
        (Val.int ⟨8, false⟩ (decodeLE ((SB.drop 112).take 1))) = .ok m6 := by
      show writeBytes s4.mem dst 112 (encodeLE 1 (decodeLE ((SB.drop 112).take 1))) = .ok m6
      exact writeBytes_ok hd5 (by simp [encodeLE_length, IntTy.bytes, hL5])
    ExS.store (pa := .ptr dst 112) paEv hk0 rfl hm
  -- king WHITE store [113,114)
  let s5 := { s4 with mem := m6 }
  have hfr5 : s5.mem src = some SB := by
    simp only [s5, s4, s3, s2, s1, m6, m5, m4, m3, m2, m1, s0]
    rw [Mem.write_ne hne.symm, Mem.write_ne hne.symm, Mem.write_ne hne.symm, Mem.write_ne hne.symm, Mem.write_ne hne.symm, Mem.write_ne hne.symm]
    exact hsrc
  have hk1 : EvE Gen.prog s5 (.load (.int ⟨8, false⟩) (.index (.field (.var 1) 112) (.const (.int ⟨32, true⟩ 1)) 1))
      (.int IntTy.u8 (decodeLE ((SB.drop 113).take 1))) := by
    refine EvE_of_eval (n := 30) ?_
    have hl1 : s5.locals 1 = some (.ptr src 0) := rfl
    have htoInt : (⟨32, true⟩ : IntTy).toInt 1 = 1 := by rfl
    simp [evalExpr, hfr5, hl1, hlen, htoInt, Res.bind_eq, Res.bind_ok, ptrAdd, ptrAddN, load, readBytes, Ty.size, IntTy.bytes, IntTy.u8, IntTy.u32, IntTy.u64, IntTy.i32]
  let m7 := m6.write dst 113 (encodeLE 1 (decodeLE ((SB.drop 113).take 1)))
  obtain ⟨blk7, hd7, hd7L⟩ := block_len_after_write (b := dst) (o := 113) (bs := encodeLE 1 (decodeLE ((SB.drop 113).take 1))) hd6 (by
    rw [hL6, encodeLE_length]; omega)
  have hL7 : blk7.length = 41088 := by rw [hd7L]; exact hL6
  have e7 : ExS Gen.prog s5 (.store (.int ⟨8, false⟩) (.index (.field (.var 0) 112) (.const (.int ⟨32, true⟩ 1)) 1)
      (.load (.int ⟨8, false⟩) (.index (.field (.var 1) 112) (.const (.int ⟨32, true⟩ 1)) 1)))
      .normal { s5 with mem := m7 } :=
    have paEv : EvE Gen.prog s5 (.index (.field (.var 0) 112) (.const (.int ⟨32, true⟩ 1)) 1) (.ptr dst 113) := by
      refine EvE_of_eval (n := 30) ?_
      have hl0 : s5.locals 0 = some (.ptr dst 0) := rfl
      have htoInt : (⟨32, true⟩ : IntTy).toInt 1 = 1 := rfl
      have hd6' : s5.mem dst = some blk6 := hd6
      simp [evalExpr, hd6', hL6, hl0, htoInt, Res.bind_eq, Res.bind_ok, ptrAdd, ptrAddN]
    have hm : store s5.mem (Ty.int ⟨8, false⟩) (Val.ptr dst 113)
        (Val.int ⟨8, false⟩ (decodeLE ((SB.drop 113).take 1))) = .ok m7 := by
      show writeBytes s5.mem dst 113 (encodeLE 1 (decodeLE ((SB.drop 113).take 1))) = .ok m7
      exact writeBytes_ok hd6 (by simp [encodeLE_length, IntTy.bytes, hL6])
    ExS.store (pa := .ptr dst 113) paEv hk1 rfl hm
  -- set 2 := load history_length (u64 at 41080)
  let s7 := { s5 with mem := m7 }
  have hfr6 : s7.mem src = some SB := by
    simp only [s7, s5, s4, s3, s2, s1, m7, m6, m5, m4, m3, m2, m1, s0]
    rw [Mem.write_ne hne.symm, Mem.write_ne hne.symm, Mem.write_ne hne.symm, Mem.write_ne hne.symm,
      Mem.write_ne hne.symm, Mem.write_ne hne.symm, Mem.write_ne hne.symm]
    exact hsrc
  have hhl : EvE Gen.prog s7 (.load (.int ⟨64, false⟩) (.field (.var 1) 41080))
      (.int ⟨64, false⟩ (decodeLE ((SB.drop 41080).take 8))) := by
    refine EvE_of_eval (n := 20) ?_
    have hl1 : s7.locals 1 = some (.ptr src 0) := rfl
    simp [evalExpr, hfr6, hl1, hlen, Res.bind_eq, Res.bind_ok, ptrAddN, load, readBytes, Ty.size, IntTy.bytes, IntTy.u32, IntTy.u64, IntTy.u8, IntTy.i32]
  have e8 : ExS Gen.prog s7 (.set 2 (.load (.int ⟨64, false⟩) (.field (.var 1) 41080)))
      .normal { s7 with locals := s7.locals.upd 2 (.int ⟨64, false⟩ (decodeLE ((SB.drop 41080).take 8))) } := by
    apply ExS.set
    exact hhl
  let s8 := { s7 with locals := s7.locals.upd 2 (.int ⟨64, false⟩ hl) }
  -- clamp history_length to 4096
  have h4096 : EvE Gen.prog s8 (.cast ⟨64, false⟩ (.const (.int ⟨32, true⟩ 4096))) (.int ⟨64, false⟩ 4096) := by
    refine EvE.cast (EvE.const _) ?_
    simp [evalCast, IntTy.wrap, IntTy.toInt, IntTy.modulus]
  have h2 : EvE Gen.prog s8 (.var 2) (.int ⟨64, false⟩ hl) := EvE.var (by rfl)
  have hbin : EvE Gen.prog s8 (.bin .gt (some ⟨64, false⟩) (.var 2) (.cast ⟨64, false⟩ (.const (.int ⟨32, true⟩ 4096))))
      (boolVal (decide (hl > 4096))) :=
    EvE.bin h2 h4096 (by simp [evalBin, isPtr, evalBinInt, binInt, intOf, IntTy.u64, Res.bind, IntTy.modulus])
  have e9 : ExS Gen.prog s8 (.ite (.bin .gt (some ⟨64, false⟩) (.var 2) (.cast ⟨64, false⟩ (.const (.int ⟨32, true⟩ 4096))))
      (.set 2 (.cast ⟨64, false⟩ (.const (.int ⟨32, true⟩ 4096)))) .skip)
      .normal { s8 with locals := s8.locals.upd 2 (.int ⟨64, false⟩ h') } := by
    by_cases h : hl > 4096
    · rw [show h' = 4096 from by rw [show h' = min hl 4096 from rfl]; omega]
      exact ExS.ite (bc := true) hbin (by rw [show decide (hl > 4096) = true from by simp [h]]; rfl)
        (ExS.set (EvE.cast (EvE.const _) (by simp [evalCast, IntTy.wrap, IntTy.toInt, IntTy.modulus])))
    · have heh : h' = hl := by rw [show h' = min hl 4096 from rfl]; exact Nat.min_eq_left (Nat.le_of_not_gt h)
      rw [heh]
      have hloc : s8.locals.upd 2 (.int ⟨64, false⟩ hl) = s8.locals := by
        funext j
        simp [s8, s7, s5, s4, s3, s2, s1, s0, Locals.upd]
        by_cases hj : j = 2 <;> simp [hj]
      rw [hloc]
      exact ExS.ite (bc := false) hbin (by rw [show decide (hl > 4096) = false from by simp [h]]; rfl) ExS.skip
  -- store history_length back to dst at 41080
  let s9 := { s8 with locals := s8.locals.upd 2 (.int ⟨64, false⟩ h') }
  have hhl9 : s9.locals 2 = some (.int ⟨64, false⟩ h') := by
    simp [s9, s8, Locals.upd]
  let m9 := m7.write dst 41080 (encodeLE 8 h')
  obtain ⟨blk9, hd9, hd9L⟩ := block_len_after_write (b := dst) (o := 41080) (bs := encodeLE 8 h') hd7 (by
    rw [hL7, encodeLE_length]; omega)
  have hL9 : blk9.length = 41088 := by rw [hd9L]; exact hL7
  let s9' := { s9 with mem := m9 }
  have e10 : ExS Gen.prog s9 (.store (.int ⟨64, false⟩) (.field (.var 0) 41080) (.var 2))
      .normal { s9' with mem := m9 } :=
    have hd7' : s9.mem dst = some blk7 := by
      simp only [s9, s8, s7, s5, s4, s3, s2, s1, s0, m7, m6, m5, m4, m3, m2, m1]
      exact hd7
    have hj9 : s9.locals 0 = some (.ptr dst 0) := rfl
    store_int_field (s := s9) (j := 0) (o := 0) (b := dst) (i := 41080) (t := ⟨64, false⟩) (v := h') (e := .var 2) (blk := blk7) (hj := hj9) (hb := hd7')
      (hi := by rw [hL7]; show 0 + 41080 + 8 ≤ 41088; omega)
      (he := EvE.var hhl9) (hlen := by simp [encodeLE_length])
      (hro := rfl)
  have hdisj10 : ((SB.drop 120).take (8 * h')).length = 8 * h' := by
    rw [List.length_take, List.length_drop, hlen]; omega
  have hdisj11 : ((SB.drop 32888).take h').length = h' := by
    rw [List.length_take, List.length_drop, hlen]; omega
  have hdisj12 : ((SB.drop 36984).take h').length = h' := by
    rw [List.length_take, List.length_drop, hlen]; omega
  -- memcpy history keys [120, 120 + 8h')
  let s10 := { s9' with mem := m9 }
  have hsrc10 : s10.mem src = some SB := by
    simp only [s10, s9', s9, s8, s7, s5, s4, s3, s2, s1, m9, m7, m6, m5, m4, m3, m2, m1, s0]
    rw [Mem.write_ne hne.symm, Mem.write_ne hne.symm, Mem.write_ne hne.symm, Mem.write_ne hne.symm,
      Mem.write_ne hne.symm, Mem.write_ne hne.symm, Mem.write_ne hne.symm, Mem.write_ne hne.symm]
    exact hsrc
  have h8h' : EvE Gen.prog s10 (.bin .mul (some ⟨64, false⟩) (.var 2) (.const (.int ⟨64, false⟩ 8)))
      (.int ⟨64, false⟩ (8 * h')) :=
    EvE.bin (EvE.var hhl9) (EvE.const _) (by
      simp [evalBin, isPtr, evalBinInt, binInt, intOf, IntTy.u64, Res.bind, IntTy.modulus,
        Nat.mod_eq_of_lt (show h' * 8 < 18446744073709551616 from by omega)]; omega)
  let m10 := m9.write dst 120 ((SB.drop 120).take (8 * h'))
  have e11 : ExS Gen.prog s10 (.memcpy (.field (.var 0) 120) (.field (.var 1) 120) (.bin .mul (some ⟨64, false⟩) (.var 2) (.const (.int ⟨64, false⟩ 8))))
      .normal { s10 with mem := m10 } :=
    memcpy_spec (by rfl) (by rfl) hd9 hsrc10
      (by rw [hL9]; omega)
      (by rw [hlen]; omega)
      (by simp [hne])
      rfl
      h8h'
  -- memcpy mover [32888, 32888 + h')
  let s11 := { s10 with mem := m10 }
  have hsrc11 : s11.mem src = some SB := by
    simp only [s11, s10, s9', s9, s8, s7, s5, s4, s3, s2, s1, m10, m9, m7, m6, m5, m4, m3, m2, m1, s0]
    rw [Mem.write_ne hne.symm, Mem.write_ne hne.symm, Mem.write_ne hne.symm, Mem.write_ne hne.symm,
      Mem.write_ne hne.symm, Mem.write_ne hne.symm, Mem.write_ne hne.symm, Mem.write_ne hne.symm, Mem.write_ne hne.symm]
    exact hsrc
  obtain ⟨blk10, hd10, hd10L⟩ := block_len_after_write (b := dst) (o := 120) (bs := (SB.drop 120).take (8 * h')) hd9 (by
    have hl10 : ((SB.drop 120).take (8 * h')).length = 8 * h' := by
      rw [take_length_of_le (by simp [List.length_drop, hlen]; omega)]
    rw [hL9, hl10]; omega)
  have hL10 : blk10.length = 41088 := by rw [hd10L]; exact hL9
  let m11 := m10.write dst 32888 ((SB.drop 32888).take h')
  have e12 : ExS Gen.prog s11 (.memcpy (.field (.var 0) 32888) (.field (.var 1) 32888) (.bin .mul (some ⟨64, false⟩) (.var 2) (.const (.int ⟨64, false⟩ 1))))
      .normal { s11 with mem := m11 } :=
    memcpy_spec (by rfl) (by rfl) hd10 hsrc11
      (by rw [hL10]; omega)
      (by simp [hlen]; omega)
      (by simp [hne])
      rfl
      (EvE.bin (EvE.var hhl9) (EvE.const _) (by
        simp [evalBin, isPtr, evalBinInt, binInt, intOf, IntTy.u64, Res.bind, IntTy.modulus,
          Nat.mod_eq_of_lt (show h' < 18446744073709551616 from by omega)]))
  -- memcpy check [36984, 36984 + h')
  let s12 := { s11 with mem := m11 }
  have hsrc12 : s12.mem src = some SB := by
    simp only [s12, s11, s10, s9', s9, s8, s7, s5, s4, s3, s2, s1, m11, m10, m9, m7, m6, m5, m4, m3, m2, m1, s0]
    rw [Mem.write_ne hne.symm, Mem.write_ne hne.symm, Mem.write_ne hne.symm, Mem.write_ne hne.symm,
      Mem.write_ne hne.symm, Mem.write_ne hne.symm, Mem.write_ne hne.symm, Mem.write_ne hne.symm,
      Mem.write_ne hne.symm, Mem.write_ne hne.symm]
    exact hsrc
  obtain ⟨blk11, hd11, hd11L⟩ := block_len_after_write (b := dst) (o := 32888) (bs := (SB.drop 32888).take h') hd10 (by
    have hl11 : ((SB.drop 32888).take h').length = h' := by
      rw [take_length_of_le (by simp [List.length_drop, hlen]; omega)]
    rw [hL10, hl11]; omega)
  have hL11 : blk11.length = 41088 := by rw [hd11L]; exact hL10
  let m12 := m11.write dst 36984 ((SB.drop 36984).take h')
  have e13 : ExS Gen.prog s12 (.memcpy (.field (.var 0) 36984) (.field (.var 1) 36984) (.bin .mul (some ⟨64, false⟩) (.var 2) (.const (.int ⟨64, false⟩ 1))))
      .normal { s12 with mem := m12 } :=
    memcpy_spec (by rfl) (by rfl) hd11 hsrc12
      (by rw [hL11]; omega)
      (by simp [hlen]; omega)
      (by simp [hne])
      rfl
      (EvE.bin (EvE.var hhl9) (EvE.const _) (by
        simp [evalBin, isPtr, evalBinInt, binInt, intOf, IntTy.u64, Res.bind, IntTy.modulus,
          Nat.mod_eq_of_lt (show h' < 18446744073709551616 from by omega)]))
  obtain ⟨blk12, hd12, hd12L⟩ := block_len_after_write (b := dst) (o := 36984) (bs := (SB.drop 36984).take h') hd11 (by
    have hl12 : ((SB.drop 36984).take h').length = h' := by
      rw [take_length_of_le (by simp [List.length_drop, hlen]; omega)]
    rw [hL11, hl12]; omega)
  have hL12 : blk12.length = 41088 := by rw [hd12L]; exact hL11
  let s' := { s12 with mem := m12 }
  -- frame: everything except the dst block is unchanged
  have hfin : ∀ x, x ≠ dst → m12 x = M x := by
    intro x hx
    show (m11.write dst 36984 ((SB.drop 36984).take h')) x = M x
    rw [Mem.write_ne hx]
    show (m10.write dst 32888 ((SB.drop 32888).take h')) x = M x
    rw [Mem.write_ne hx]
    show (m9.write dst 120 ((SB.drop 120).take (8 * h'))) x = M x
    rw [Mem.write_ne hx]
    show m9 x = M x
    show (m7.write dst 41080 (encodeLE 8 h')) x = M x
    rw [Mem.write_ne hx]
    show (m6.write dst 113 (encodeLE 1 (decodeLE ((SB.drop 113).take 1)))) x = M x
    rw [Mem.write_ne hx]
    show (m5.write dst 112 (encodeLE 1 (decodeLE ((SB.drop 112).take 1)))) x = M x
    rw [Mem.write_ne hx]
    show (m4.write dst 104 (encodeLE 8 (decodeLE ((SB.drop 104).take 8)))) x = M x
    rw [Mem.write_ne hx]
    show (m3.write dst 100 (encodeLE 4 (decodeLE ((SB.drop 100).take 4)))) x = M x
    rw [Mem.write_ne hx]
    show (m2.write dst 96 (encodeLE 4 (decodeLE ((SB.drop 96).take 4)))) x = M x
    rw [Mem.write_ne hx]
    show (m1.write dst 81 ((SB.drop 81).take 14)) x = M x
    rw [Mem.write_ne hx]
    show (s0.mem.write dst 0 (SB.take 81)) x = M x
    rw [Mem.write_ne hx]
  -- peeling helpers: one for each write, applied outward-to-inward
  have pb36984 : readBytes m12 dst 0 81 = readBytes m11 dst 0 81 :=
    readBytes_write_disjoint hd11 (by
      have hl := take_length_of_le (l := SB.drop 36984) (n := h') (by
        simp [List.length_drop, hlen]; omega)
      rw [hL11, hl]; omega)
      (Or.inl (by omega))
  have pb32888 : readBytes m11 dst 0 81 = readBytes m10 dst 0 81 :=
    readBytes_write_disjoint hd10 (by
      have hl := take_length_of_le (l := SB.drop 32888) (n := h') (by
        simp [List.length_drop, hlen]; omega)
      rw [hL10, hl]; omega)
      (Or.inl (by omega))
  have pb120 : readBytes m10 dst 0 81 = readBytes m9 dst 0 81 :=
    readBytes_write_disjoint hd9 (by
      have hl := take_length_of_le (l := SB.drop 120) (n := 8 * h') (by
        simp [List.length_drop, hlen]; omega)
      rw [hL9, hl]; omega)
      (Or.inl (by omega))
  have pb41080 : readBytes m9 dst 0 81 = readBytes m7 dst 0 81 :=
    readBytes_write_disjoint hd7 (by rw [hL7, encodeLE_length]; omega)
      (Or.inl (by omega))
  have pb113 : readBytes m7 dst 0 81 = readBytes m6 dst 0 81 :=
    readBytes_write_disjoint hd6 (by rw [hL6, encodeLE_length]; omega)
      (Or.inl (by omega))
  have pb112 : readBytes m6 dst 0 81 = readBytes m5 dst 0 81 :=
    readBytes_write_disjoint hd5 (by rw [hL5, encodeLE_length]; omega)
      (Or.inl (by omega))
  have pb104 : readBytes m5 dst 0 81 = readBytes m4 dst 0 81 :=
    readBytes_write_disjoint hd4 (by rw [hL4, encodeLE_length]; omega)
      (Or.inl (by omega))
  have pb100 : readBytes m4 dst 0 81 = readBytes m3 dst 0 81 :=
    readBytes_write_disjoint hd3 (by rw [hL3, encodeLE_length]; omega)
      (Or.inl (by omega))
  have pb96 : readBytes m3 dst 0 81 = readBytes m2 dst 0 81 :=
    readBytes_write_disjoint hd2 (by
      simp [List.length_append, List.length_take, List.length_drop, hlen, hlen', encodeLE_length])
      (Or.inl (by omega))
  have pb81 : readBytes m2 dst 0 81 = readBytes m1 dst 0 81 :=
    readBytes_write_disjoint hd1 (by
      simp [List.length_append, List.length_take, List.length_drop, hlen, hlen', encodeLE_length])
      (Or.inl (by omega))
  have hb81 : readBytes m12 dst 0 81 = .ok (SB.take 81) := by
    rw [pb36984, pb32888, pb120, pb41080, pb113, pb112, pb104, pb100, pb96, pb81]
    have h1 : (SB.take 81).length = 81 := by simp [List.length_take, hlen]
    have hfit : 0 + (SB.take 81).length ≤ DB.length := by rw [h1]; simp [hlen']
    have hfit2 : (0 : Nat) ≤ 0 ∧ 0 + 81 ≤ 0 + (SB.take 81).length := by
      rw [h1]; exact ⟨Nat.zero_le _, by omega⟩
    have hw := readBytes_write_window hd hfit hfit2
    simp only [Nat.sub_self, List.drop_zero, List.take_take, Nat.min_self] at hw
    exact hw
  have pb369845 : readBytes m12 dst 81 14 = readBytes m11 dst 81 14 :=
    readBytes_write_disjoint hd11 (by
      have hl := take_length_of_le (l := SB.drop 36984) (n := h') (by
        simp [List.length_drop, hlen]; omega)
      rw [hL11, hl]; omega)
      (Or.inl (by omega))
  have pb328885 : readBytes m11 dst 81 14 = readBytes m10 dst 81 14 :=
    readBytes_write_disjoint hd10 (by
      have hl := take_length_of_le (l := SB.drop 32888) (n := h') (by
        simp [List.length_drop, hlen]; omega)
      rw [hL10, hl]; omega)
      (Or.inl (by omega))
  have pb1205 : readBytes m10 dst 81 14 = readBytes m9 dst 81 14 :=
    readBytes_write_disjoint hd9 (by
      have hl := take_length_of_le (l := SB.drop 120) (n := 8 * h') (by
        simp [List.length_drop, hlen]; omega)
      rw [hL9, hl]; omega)
      (Or.inl (by omega))
  have pb410805 : readBytes m9 dst 81 14 = readBytes m7 dst 81 14 :=
    readBytes_write_disjoint hd7 (by rw [hL7, encodeLE_length]; omega)
      (Or.inl (by omega))
  have pb113c : readBytes m7 dst 81 14 = readBytes m6 dst 81 14 :=
    readBytes_write_disjoint hd6 (by rw [hL6, encodeLE_length]; omega)
      (Or.inl (by omega))
  have pb112c : readBytes m6 dst 81 14 = readBytes m5 dst 81 14 :=
    readBytes_write_disjoint hd5 (by rw [hL5, encodeLE_length]; omega)
      (Or.inl (by omega))
  have pb104c : readBytes m5 dst 81 14 = readBytes m4 dst 81 14 :=
    readBytes_write_disjoint hd4 (by rw [hL4, encodeLE_length]; omega)
      (Or.inl (by omega))
  have pb100c : readBytes m4 dst 81 14 = readBytes m3 dst 81 14 :=
    readBytes_write_disjoint hd3 (by rw [hL3, encodeLE_length]; omega)
      (Or.inl (by omega))
  have pb96c : readBytes m3 dst 81 14 = readBytes m2 dst 81 14 :=
    readBytes_write_disjoint hd2 (by
      simp [List.length_append, List.length_take, List.length_drop, hlen, hlen', encodeLE_length])
      (Or.inl (by omega))
  -- conclusion: dst [81, 95) = SB[81, 95)
  have hb81_95 : readBytes m12 dst 81 14 = .ok ((SB.drop 81).take 14) := by
    rw [pb369845, pb328885, pb1205, pb410805, pb113c, pb112c, pb104c, pb100c, pb96c]
    have h1 : ((SB.drop 81).take 14).length = 14 := by simp [List.length_take, List.length_drop, hlen]
    have hfit : 81 + ((SB.drop 81).take 14).length ≤ (SB.take 81 ++ DB.drop 81).length := by
      rw [h1]; simp [List.length_append, List.length_take, List.length_drop, hlen, hlen']
    have hfit2 : (81 : Nat) ≤ 81 ∧ 81 + 14 ≤ 81 + ((SB.drop 81).take 14).length := by
      rw [h1]; exact ⟨Nat.le_refl _, by omega⟩
    have hw := readBytes_write_window hd1 hfit hfit2
    simp only [Nat.sub_self, List.drop_zero, List.take_take, Nat.min_self] at hw
    exact hw
  have pb369845a : readBytes m12 dst 96 4 = readBytes m11 dst 96 4 :=
    readBytes_write_disjoint hd11 (by
      have hl := take_length_of_le (l := SB.drop 36984) (n := h') (by
        simp [List.length_drop, hlen]; omega)
      rw [hL11, hl]; omega)
      (Or.inl (by omega))
  have pb328885a : readBytes m11 dst 96 4 = readBytes m10 dst 96 4 :=
    readBytes_write_disjoint hd10 (by
      have hl := take_length_of_le (l := SB.drop 32888) (n := h') (by
        simp [List.length_drop, hlen]; omega)
      rw [hL10, hl]; omega)
      (Or.inl (by omega))
  have pb1205a : readBytes m10 dst 96 4 = readBytes m9 dst 96 4 :=
    readBytes_write_disjoint hd9 (by
      have hl := take_length_of_le (l := SB.drop 120) (n := 8 * h') (by
        simp [List.length_drop, hlen]; omega)
      rw [hL9, hl]; omega)
      (Or.inl (by omega))
  have pb410805a : readBytes m9 dst 96 4 = readBytes m7 dst 96 4 :=
    readBytes_write_disjoint hd7 (by rw [hL7, encodeLE_length]; omega)
      (Or.inl (by omega))
  have pb113ca : readBytes m7 dst 96 4 = readBytes m6 dst 96 4 :=
    readBytes_write_disjoint hd6 (by rw [hL6, encodeLE_length]; omega)
      (Or.inl (by omega))
  have pb112ca : readBytes m6 dst 96 4 = readBytes m5 dst 96 4 :=
    readBytes_write_disjoint hd5 (by rw [hL5, encodeLE_length]; omega)
      (Or.inl (by omega))
  have pb104ca : readBytes m5 dst 96 4 = readBytes m4 dst 96 4 :=
    readBytes_write_disjoint hd4 (by rw [hL4, encodeLE_length]; omega)
      (Or.inl (by omega))
  have pb100ca : readBytes m4 dst 96 4 = readBytes m3 dst 96 4 :=
    readBytes_write_disjoint hd3 (by rw [hL3, encodeLE_length]; omega)
      (Or.inl (by omega))
  have hb96 : readBytes m12 dst 96 4 = .ok ((SB.drop 96).take 4) := by
    rw [pb369845a, pb328885a, pb1205a, pb410805a, pb113ca, pb112ca, pb104ca, pb100ca]
    have h1 : (encodeLE 4 (decodeLE ((SB.drop 96).take 4))).length = 4 := by
      simp [encodeLE_length]
    have hfit : 96 + (encodeLE 4 (decodeLE ((SB.drop 96).take 4))).length ≤ (SB.take 95 ++ DB.drop 95).length := by
      rw [h1]; simp [List.length_append, List.length_take, List.length_drop, hlen, hlen']
    have hfit2 : (96 : Nat) ≤ 96 ∧ 96 + 4 ≤ 96 + (encodeLE 4 (decodeLE ((SB.drop 96).take 4))).length := by
      rw [h1]; exact ⟨Nat.le_refl _, by omega⟩
    have hw := readBytes_write_window hd2 hfit hfit2
    have henc : (encodeLE 4 (decodeLE ((SB.drop 96).take 4))) = ((SB.drop 96).take 4) := by
      have h1l : ((SB.drop 96).take 4).length = 4 := by
        simp [List.length_take, List.length_drop, hlen]
      have hthis := encodeLE_decodeLE ((SB.drop 96).take 4)
      rw [h1l] at hthis
      exact hthis
    simp only [Nat.sub_self, List.drop_zero] at hw
    rw [List.take_encodeLE] at hw
    rw [← henc]
    exact hw

  have pb369845b : readBytes m12 dst 100 4 = readBytes m11 dst 100 4 :=
    readBytes_write_disjoint hd11 (by
      have hl := take_length_of_le (l := SB.drop 36984) (n := h') (by
        simp [List.length_drop, hlen]; omega)
      rw [hL11, hl]; omega)
      (Or.inl (by omega))
  have pb328885b : readBytes m11 dst 100 4 = readBytes m10 dst 100 4 :=
    readBytes_write_disjoint hd10 (by
      have hl := take_length_of_le (l := SB.drop 32888) (n := h') (by
        simp [List.length_drop, hlen]; omega)
      rw [hL10, hl]; omega)
      (Or.inl (by omega))
  have pb1205b : readBytes m10 dst 100 4 = readBytes m9 dst 100 4 :=
    readBytes_write_disjoint hd9 (by
      have hl := take_length_of_le (l := SB.drop 120) (n := 8 * h') (by
        simp [List.length_drop, hlen]; omega)
      rw [hL9, hl]; omega)
      (Or.inl (by omega))
  have pb410805b : readBytes m9 dst 100 4 = readBytes m7 dst 100 4 :=
    readBytes_write_disjoint hd7 (by rw [hL7, encodeLE_length]; omega)
      (Or.inl (by omega))
  have pb113cb : readBytes m7 dst 100 4 = readBytes m6 dst 100 4 :=
    readBytes_write_disjoint hd6 (by rw [hL6, encodeLE_length]; omega)
      (Or.inl (by omega))
  have pb112cb : readBytes m6 dst 100 4 = readBytes m5 dst 100 4 :=
    readBytes_write_disjoint hd5 (by rw [hL5, encodeLE_length]; omega)
      (Or.inl (by omega))
  have pb104cb : readBytes m5 dst 100 4 = readBytes m4 dst 100 4 :=
    readBytes_write_disjoint hd4 (by rw [hL4, encodeLE_length]; omega)
      (Or.inl (by omega))
  have hb100 : readBytes m12 dst 100 4 = .ok ((SB.drop 100).take 4) := by
    rw [pb369845b, pb328885b, pb1205b, pb410805b, pb113cb, pb112cb, pb104cb]
    have h1 : (encodeLE 4 (decodeLE ((SB.drop 100).take 4))).length = 4 := by
      simp [encodeLE_length]
    have hfit : 100 + (encodeLE 4 (decodeLE ((SB.drop 100).take 4))).length ≤ blk3.length := by
      rw [h1, hd3L]; omega
    have hfit2 : (100 : Nat) ≤ 100 ∧ 100 + 4 ≤ 100 + (encodeLE 4 (decodeLE ((SB.drop 100).take 4))).length := by
      rw [h1]; exact ⟨Nat.le_refl _, by omega⟩
    have hw := readBytes_write_window hd3 hfit hfit2
    have henc : (encodeLE 4 (decodeLE ((SB.drop 100).take 4))) = ((SB.drop 100).take 4) := by
      have h1l : ((SB.drop 100).take 4).length = 4 := by
        simp [List.length_take, List.length_drop, hlen]
      have hthis := encodeLE_decodeLE ((SB.drop 100).take 4)
      rw [h1l] at hthis
      exact hthis
    simp only [Nat.sub_self, List.drop_zero] at hw
    rw [List.take_encodeLE] at hw
    rw [← henc]
    exact hw

  have pb369845c : readBytes m12 dst 104 8 = readBytes m11 dst 104 8 :=
    readBytes_write_disjoint hd11 (by
      have hl := take_length_of_le (l := SB.drop 36984) (n := h') (by
        simp [List.length_drop, hlen]; omega)
      rw [hL11, hl]; omega)
      (Or.inl (by omega))
  have pb328885c : readBytes m11 dst 104 8 = readBytes m10 dst 104 8 :=
    readBytes_write_disjoint hd10 (by
      have hl := take_length_of_le (l := SB.drop 32888) (n := h') (by
        simp [List.length_drop, hlen]; omega)
      rw [hL10, hl]; omega)
      (Or.inl (by omega))
  have pb1205c : readBytes m10 dst 104 8 = readBytes m9 dst 104 8 :=
    readBytes_write_disjoint hd9 (by
      have hl := take_length_of_le (l := SB.drop 120) (n := 8 * h') (by
        simp [List.length_drop, hlen]; omega)
      rw [hL9, hl]; omega)
      (Or.inl (by omega))
  have pb410805c : readBytes m9 dst 104 8 = readBytes m7 dst 104 8 :=
    readBytes_write_disjoint hd7 (by rw [hL7, encodeLE_length]; omega)
      (Or.inl (by omega))
  have pb113cc : readBytes m7 dst 104 8 = readBytes m6 dst 104 8 :=
    readBytes_write_disjoint hd6 (by rw [hL6, encodeLE_length]; omega)
      (Or.inl (by omega))
  have pb112cc : readBytes m6 dst 104 8 = readBytes m5 dst 104 8 :=
    readBytes_write_disjoint hd5 (by rw [hL5, encodeLE_length]; omega)
      (Or.inl (by omega))
  have hb104 : readBytes m12 dst 104 8 = .ok ((SB.drop 104).take 8) := by
    rw [pb369845c, pb328885c, pb1205c, pb410805c, pb113cc, pb112cc]
    have h1 : (encodeLE 8 (decodeLE ((SB.drop 104).take 8))).length = 8 := by
      simp [encodeLE_length]
    have hfit : 104 + (encodeLE 8 (decodeLE ((SB.drop 104).take 8))).length ≤ blk4.length := by
      rw [h1, hL4]; omega
    have hfit2 : (104 : Nat) ≤ 104 ∧ 104 + 8 ≤ 104 + (encodeLE 8 (decodeLE ((SB.drop 104).take 8))).length := by
      rw [h1]; exact ⟨Nat.le_refl _, by omega⟩
    have hw := readBytes_write_window hd4 hfit hfit2
    have henc : (encodeLE 8 (decodeLE ((SB.drop 104).take 8))) = ((SB.drop 104).take 8) := by
      have h1l : ((SB.drop 104).take 8).length = 8 := by
        simp [List.length_take, List.length_drop, hlen]
      have hthis := encodeLE_decodeLE ((SB.drop 104).take 8)
      rw [h1l] at hthis
      exact hthis
    simp only [Nat.sub_self, List.drop_zero] at hw
    rw [List.take_encodeLE] at hw
    rw [← henc]
    exact hw

  have pb369845k1 : readBytes m12 dst 112 1 = readBytes m11 dst 112 1 :=
    readBytes_write_disjoint hd11 (by rw [hL11, hdisj12]; omega)
      (Or.inl (by omega))
  have pb328885k1 : readBytes m11 dst 112 1 = readBytes m10 dst 112 1 :=
    readBytes_write_disjoint hd10 (by rw [hL10, hdisj11]; omega)
      (Or.inl (by omega))
  have pb1205k1 : readBytes m10 dst 112 1 = readBytes m9 dst 112 1 :=
    readBytes_write_disjoint hd9 (by rw [hL9, hdisj10]; omega)
      (Or.inl (by omega))
  have pb410805k1 : readBytes m9 dst 112 1 = readBytes m7 dst 112 1 :=
    readBytes_write_disjoint hd7 (by rw [hL7, encodeLE_length]; omega)
      (Or.inl (by omega))
  have pb113k1 : readBytes m7 dst 112 1 = readBytes m6 dst 112 1 :=
    readBytes_write_disjoint hd6 (by rw [hL6, encodeLE_length]; omega)
      (Or.inl (by omega))
  have hb112 : readBytes m12 dst 112 1 = .ok ((SB.drop 112).take 1) := by
    rw [pb369845k1, pb328885k1, pb1205k1, pb410805k1, pb113k1]
    have h1 : (encodeLE 1 (decodeLE ((SB.drop 112).take 1))).length = 1 := by
      simp [encodeLE_length]
    have hfit : 112 + (encodeLE 1 (decodeLE ((SB.drop 112).take 1))).length ≤ blk5.length := by
      rw [h1, hL5]; omega
    have hfit2 : (112 : Nat) ≤ 112 ∧ 112 + 1 ≤ 112 + (encodeLE 1 (decodeLE ((SB.drop 112).take 1))).length := by
      rw [h1]; exact ⟨Nat.le_refl _, by omega⟩
    have hw := readBytes_write_window hd5 hfit hfit2
    have henc : (encodeLE 1 (decodeLE ((SB.drop 112).take 1))) = ((SB.drop 112).take 1) := by
      have h1l : ((SB.drop 112).take 1).length = 1 := by
        simp [List.length_take, List.length_drop, hlen]
      have hthis := encodeLE_decodeLE ((SB.drop 112).take 1)
      rw [h1l] at hthis
      exact hthis
    simp only [Nat.sub_self, List.drop_zero] at hw
    rw [List.take_encodeLE] at hw
    rw [← henc]
    exact hw

  have pb369845k2 : readBytes m12 dst 113 1 = readBytes m11 dst 113 1 :=
    readBytes_write_disjoint hd11 (by rw [hL11, hdisj12]; omega)
      (Or.inl (by omega))
  have pb328885k2 : readBytes m11 dst 113 1 = readBytes m10 dst 113 1 :=
    readBytes_write_disjoint hd10 (by rw [hL10, hdisj11]; omega)
      (Or.inl (by omega))
  have pb1205k2 : readBytes m10 dst 113 1 = readBytes m9 dst 113 1 :=
    readBytes_write_disjoint hd9 (by rw [hL9, hdisj10]; omega)
      (Or.inl (by omega))
  have pb410805k2 : readBytes m9 dst 113 1 = readBytes m7 dst 113 1 :=
    readBytes_write_disjoint hd7 (by rw [hL7, encodeLE_length]; omega)
      (Or.inl (by omega))
  have hb113 : readBytes m12 dst 113 1 = .ok ((SB.drop 113).take 1) := by
    rw [pb369845k2, pb328885k2, pb1205k2, pb410805k2]
    have h1 : (encodeLE 1 (decodeLE ((SB.drop 113).take 1))).length = 1 := by
      simp [encodeLE_length]
    have hfit : 113 + (encodeLE 1 (decodeLE ((SB.drop 113).take 1))).length ≤ blk6.length := by
      rw [h1, hL6]; omega
    have hfit2 : (113 : Nat) ≤ 113 ∧ 113 + 1 ≤ 113 + (encodeLE 1 (decodeLE ((SB.drop 113).take 1))).length := by
      rw [h1]; exact ⟨Nat.le_refl _, by omega⟩
    have hw := readBytes_write_window hd6 hfit hfit2
    have henc : (encodeLE 1 (decodeLE ((SB.drop 113).take 1))) = ((SB.drop 113).take 1) := by
      have h1l : ((SB.drop 113).take 1).length = 1 := by
        simp [List.length_take, List.length_drop, hlen]
      have hthis := encodeLE_decodeLE ((SB.drop 113).take 1)
      rw [h1l] at hthis
      exact hthis
    simp only [Nat.sub_self, List.drop_zero] at hw
    rw [List.take_encodeLE] at hw
    rw [← henc]
    exact hw

  have pb369845120 : readBytes m12 dst 120 (8 * h') = readBytes m11 dst 120 (8 * h') :=
    readBytes_write_disjoint hd11 (by rw [hL11, hdisj12]; omega)
      (Or.inl (by omega))
  have pb328885120 : readBytes m11 dst 120 (8 * h') = readBytes m10 dst 120 (8 * h') :=
    readBytes_write_disjoint hd10 (by rw [hL10, hdisj11]; omega)
      (Or.inl (by omega))
  have hb120 : readBytes m12 dst 120 (8 * h') = .ok ((SB.drop 120).take (8 * h')) := by
    rw [pb369845120, pb328885120]
    have hfit : 120 + ((SB.drop 120).take (8 * h')).length ≤ blk9.length := by
      rw [hdisj10, hL9]; omega
    have hfit2 : (120 : Nat) ≤ 120 ∧ 120 + 8 * h' ≤ 120 + ((SB.drop 120).take (8 * h')).length := by
      rw [hdisj10]; exact ⟨Nat.le_refl _, by omega⟩
    have hw := readBytes_write_window hd9 hfit hfit2
    have htake : List.take (8 * h') ((SB.drop 120).take (8 * h')) = (SB.drop 120).take (8 * h') :=
      List.take_of_length_le (by rw [hdisj10]; exact Nat.le_refl _)
    simp only [Nat.sub_self, List.drop_zero, htake] at hw
    exact hw

  have pb36984532888 : readBytes m12 dst 32888 h' = readBytes m11 dst 32888 h' :=
    readBytes_write_disjoint hd11 (by rw [hL11, hdisj12]; omega)
      (Or.inl (by omega))
  have hb32888 : readBytes m12 dst 32888 h' = .ok ((SB.drop 32888).take h') := by
    rw [pb36984532888]
    have hfit : 32888 + ((SB.drop 32888).take h').length ≤ blk10.length := by
      rw [hdisj11, hL10]; omega
    have hfit2 : (32888 : Nat) ≤ 32888 ∧ 32888 + h' ≤ 32888 + ((SB.drop 32888).take h').length := by
      rw [hdisj11]; exact ⟨Nat.le_refl _, by omega⟩
    have hw := readBytes_write_window hd10 hfit hfit2
    have htake : List.take h' ((SB.drop 32888).take h') = (SB.drop 32888).take h' :=
      List.take_of_length_le (by rw [hdisj11]; exact Nat.le_refl _)
    simp only [Nat.sub_self, List.drop_zero, htake] at hw
    exact hw

  have hb36984 : readBytes m12 dst 36984 h' = .ok ((SB.drop 36984).take h') := by
    have hfit : 36984 + ((SB.drop 36984).take h').length ≤ blk11.length := by
      rw [hdisj12, hL11]; omega
    have hfit2 : (36984 : Nat) ≤ 36984 ∧ 36984 + h' ≤ 36984 + ((SB.drop 36984).take h').length := by
      rw [hdisj12]; exact ⟨Nat.le_refl _, by omega⟩
    have hw := readBytes_write_window hd11 hfit hfit2
    have htake : List.take h' ((SB.drop 36984).take h') = (SB.drop 36984).take h' :=
      List.take_of_length_le (by rw [hdisj12]; exact Nat.le_refl _)
    simp only [Nat.sub_self, List.drop_zero, htake] at hw
    exact hw

  have pb36984541080 : readBytes m12 dst 41080 8 = readBytes m11 dst 41080 8 :=
    readBytes_write_disjoint hd11 (by rw [hL11, hdisj12]; omega)
      (Or.inr (by omega))
  have pb32888541080 : readBytes m11 dst 41080 8 = readBytes m10 dst 41080 8 :=
    readBytes_write_disjoint hd10 (by rw [hL10, hdisj11]; omega)
      (Or.inr (by omega))
  have pb120541080 : readBytes m10 dst 41080 8 = readBytes m9 dst 41080 8 :=
    readBytes_write_disjoint hd9 (by rw [hL9, hdisj10]; omega)
      (Or.inr (by omega))
  have hb41080 : readBytes m12 dst 41080 8 = .ok (encodeLE 8 h') := by
    rw [pb36984541080, pb32888541080, pb120541080]
    have h1 : (encodeLE 8 h').length = 8 := by simp [encodeLE_length]
    have hfit : 41080 + (encodeLE 8 h').length ≤ blk7.length := by
      rw [h1, hL7]; omega
    have hfit2 : (41080 : Nat) ≤ 41080 ∧ 41080 + 8 ≤ 41080 + (encodeLE 8 h').length := by
      rw [h1]; exact ⟨Nat.le_refl _, by omega⟩
    have hw := readBytes_write_window hd7 hfit hfit2
    simp only [Nat.sub_self, List.drop_zero] at hw
    rw [List.take_encodeLE] at hw
    exact hw

  have eChain : ExS Gen.prog s0 Gen.shogi_position_copy_active.body .normal { s12 with mem := m12 } := by
    refine ExS.seq e0 (ExS.seq e1 (ExS.seq e2 (ExS.seq e3 (ExS.seq e4 (ExS.seq e5
      (ExS.seq e6 (ExS.seq e7 (ExS.seq e8 (ExS.seq e9 (ExS.seq e10 (ExS.seq e11 (ExS.seq e12 e13))))))))))))
  refine ⟨s', eChain, hfin, hb81, hb81_95, hb96, hb100, hb104, hb112, hb113, hb120, hb32888, hb36984, hb41080,
    blk12, hd12, hL12⟩




theorem take_drop_of_prefix {α : Type _} {l l' : List α} {len o n : Nat}
    (h : l.take len = l') (hon : o + n ≤ len) :
    (l.drop o).take n = (l'.drop o).take n := by
  rw [List.take_drop, List.take_drop]
  have ht : l.take (o + n) = l'.take (o + n) := by
    calc
      l.take (o + n) = (l.take len).take (o + n) := by
        rw [List.take_take, Nat.min_eq_left hon]
      _ = (l').take (o + n) := by rw [h]
  rw [ht]

/-- The seven field-byte reads of the 114-byte prefix that the internal generator needs. -/
def FieldsOK (p : Position) (m : Mem) (b : Nat) : Prop :=
  readBytes m b 0 81 = .ok ((encode p).take 81) ∧
  readBytes m b 81 14 = .ok (((encode p).drop 81).take 14) ∧
  readBytes m b 96 4 = .ok (((encode p).drop 96).take 4) ∧
  readBytes m b 100 4 = .ok (((encode p).drop 100).take 4) ∧
  readBytes m b 104 8 = .ok (((encode p).drop 104).take 8) ∧
  readBytes m b 112 1 = .ok (((encode p).drop 112).take 1) ∧
  readBytes m b 113 1 = .ok (((encode p).drop 113).take 1)

/-- Field facts for a source block whose prefix is `encode p`. -/
theorem source_fields (p : Position) {SB : Block} (hpref : SB.take (encode p).length = encode p) :
    SB.take 81 = (encode p).take 81 ∧
    (SB.drop 81).take 14 = ((encode p).drop 81).take 14 ∧
    (SB.drop 96).take 4 = ((encode p).drop 96).take 4 ∧
    (SB.drop 100).take 4 = ((encode p).drop 100).take 4 ∧
    (SB.drop 104).take 8 = ((encode p).drop 104).take 8 ∧
    (SB.drop 112).take 1 = ((encode p).drop 112).take 1 ∧
    (SB.drop 113).take 1 = ((encode p).drop 113).take 1 := by
  have hlen : (encode p).length = 114 := encode_length p
  have t81 : SB.take 81 = (encode p).take 81 := by
    calc
      SB.take 81 = (SB.take (encode p).length).take 81 := by
        rw [List.take_take]
        rw [Nat.min_eq_left (by rw [hlen]; decide : 81 ≤ (encode p).length)]
      _ = (encode p).take 81 := by rw [hpref]
  have f (o n : Nat) (hon : o + n ≤ 114) :
      (SB.drop o).take n = ((encode p).drop o).take n := by
    rw [← hpref]
    exact take_drop_of_prefix rfl (by rwa [hlen])
  exact ⟨t81, f 81 14 (by decide), f 96 4 (by decide), f 100 4 (by decide),
    f 104 8 (by decide), f 112 1 (by decide), f 113 1 (by decide)⟩

/-- The internal generator's contract on a full-size copied work block.
    This is the one gap left in the fid 38 bridge: it holds for the 114-byte
    `encode p` block by `generate_legal_refines`, but not yet for a full
    41088-byte block with the same field prefix. -/
def CopyGenSpec (fuel : Nat) (p : Position) (cap : Nat) : Prop :=
  ∀ (M : Mem) (work moves n : Nat) (WB MB : Block),
    M work = some WB → WB.length = 41088 → FieldsOK p M work →
    M moves = some MB → cap * 5 ≤ MB.length →
    TablesIn M → Fresh M n →
    n + 1000000000 < 2 ^ 64 →
    work ≠ 0 → moves ≠ 0 → moves ≠ work →
    (work < 8192 ∨ 8196 < work) → (moves < 8192 ∨ 8196 < moves) →
    ∃ K : List (List UInt8), ∃ cnt s' cb,
      K.Perm ((Position.legalAux (fuel + 1) p).map (moveBytes p)) ∧
      ExS Gen.prog ⟨frameLocals Gen.generate_legal_mut_internal.params
          [.ptr work 0, .ptr moves 0, .int IntTy.u64 cap, .int IntTy.u8 1], M, false⟩
        Gen.generate_legal_mut_internal.body (.ret (some (.int IntTy.u64 cnt))) s' ∧
      Buf s'.mem moves 0 cb 0 cap K

/-- `shogi_generate_legal` (fid 38): guard, allocate the work block, copy the
    position into it, run the internal generator there and return its count.
    The internal call is carried as the explicit hypothesis `CopyGenSpec`;
    discharging it is the remaining full-block generalisation of
    `generate_legal_refines`. -/
theorem shogi_generate_legal_spec (p : Position) (hS : p.Shaped) (hK : KingsUnique p)
    (hw : ∀ i, p.hand p.side i < 256) (fuel : Nat) (cap : Nat)
    (Hcall : CopyGenSpec fuel p cap) (hcap7200 : 7200 ≤ cap) (hcap64 : cap < 2 ^ 64)
    {M : Mem} {pos moves n : Nat} {SB MB : Block}
    (hsrc : M pos = some SB) (hlen : SB.length = 41088)
    (hpref : SB.take (encode p).length = encode p)
    (ht : TablesIn M) (hf : Fresh M n)
    (hmoves : M moves = some MB) (hlenM : cap * 5 ≤ MB.length)
    (hmoves0 : moves ≠ 0) (hpos0 : pos ≠ 0) (hpm : pos ≠ moves)
    (hmbt : moves < 8192 ∨ 8196 < moves)
    (h64 : n + 1000000000 < 2 ^ 64) (h64succ : n + 1 + 1000000000 < 2 ^ 64) :
    ∃ K : List (List UInt8), K.Perm ((Position.legalAux (fuel + 1) p).map (moveBytes p)) ∧
      ∃ cnt s' cb,
        ExS Gen.prog ⟨frameLocals Gen.shogi_generate_legal.params
            [.ptr pos 0, .ptr moves 0, .int IntTy.u64 cap], M, false⟩
          Gen.shogi_generate_legal.body (.ret (some (.int IntTy.u64 cnt))) s' ∧
        Buf s'.mem moves 0 cb 0 cap K := by
  let s0 : State := ⟨frameLocals Gen.shogi_generate_legal.params
    [.ptr pos 0, .ptr moves 0, .int IntTy.u64 cap], M, false⟩
  have hguard : EvE Gen.prog s0 (.lor (.bin .eq none (.var 0) (.const .null))
      (.bin .eq none (.var 1) (.const .null))) (boolVal false) := by
    refine EvE_of_eval (n := 4) ?_
    rfl
  have e0 : ExS Gen.prog s0 (.ite (.lor (.bin .eq none (.var 0) (.const .null))
      (.bin .eq none (.var 1) (.const .null))) (.ret (some (.cast ⟨64, false⟩ (.const (.int ⟨32, true⟩ 0)))))
      .skip) .normal s0 := ExS.ite (bc := false) hguard rfl ExS.skip
  have hn64 : n < 2 ^ 64 := by omega
  have halloc : ExS Gen.prog s0 (.alloc 3 41088) .normal
      { s0 with mem := (s0.mem.upd 0 (encodeLE 8 (n + 1))).upd n (List.replicate 41088 0),
                locals := s0.locals.upd 3 (.ptr n 0) } := by
    exact exec_alloc (Fresh.allocAt hf hn64) 3 41088
  let m1 : Mem := (M.upd 0 (encodeLE 8 (n + 1))).upd n (List.replicate 41088 0)
  let s1 : State := { s0 with mem := m1, locals := s0.locals.upd 3 (.ptr n 0) }
  have halloc' : ExS Gen.prog s0 (.alloc 3 41088) .normal s1 := halloc
  have hn0 : n ≠ 0 := hf.2.1
  have hnpos : n ≠ pos := by
    intro e
    rw [e] at hf
    have : M pos = none := hf.2.2 pos (Nat.le_refl _)
    rw [hsrc] at this
    cases this
  have hsrc1 : m1 pos = some SB := by
    simp only [m1]
    rw [Mem.upd_ne (Ne.symm hnpos), Mem.upd_ne hpos0]
    exact hsrc
  have hd1 : m1 n = some (List.replicate 41088 0) := by simp only [m1]; rw [Mem.upd_eq]
  let hCS := shogi_position_copy_active_spec (M := m1) (src := pos) (dst := n) (SB := SB)
      (DB := List.replicate 41088 0) hsrc1 hlen hd1 (by rw [List.length_replicate]) hnpos hn0
  let sc : State := Classical.choose hCS
  have hsc := Classical.choose_spec hCS
  let ec := hsc.1
  let t1 := hsc.2
  let hfc := t1.1
  let t2 := t1.2
  let hb81 := t2.1
  let t3 := t2.2
  let hb81_95 := t3.1
  let t4 := t3.2
  let hb96 := t4.1
  let t5 := t4.2
  let hb100 := t5.1
  let t6 := t5.2
  let hb104 := t6.1
  let t7 := t6.2
  let hb112 := t7.1
  let t8 := t7.2
  let hb113 := t8.1
  let t9 := t8.2
  let hb120 := t9.1
  let t10 := t9.2
  let hb32888 := t10.1
  let t11 := t10.2
  let hb36984 := t11.1
  let t12 := t11.2
  let hb41080 := t12.1
  let hWBex := t12.2
  let WB : Block := Classical.choose hWBex
  have hWBC : sc.mem n = some WB := (Classical.choose_spec hWBex).1
  have hWBL : WB.length = 41088 := (Classical.choose_spec hWBex).2
  let s2 : State := { s1 with mem := (Classical.choose hCS).mem }
  have hargs1 : EvArgs Gen.prog s1 [(.var 3), (.var 0)] [(.ptr n 0), (.ptr pos 0)] :=
    EvArgs.cons (EvE.var rfl) (EvArgs.cons (EvE.var rfl) EvArgs.nil)
  have hcopy : ExS Gen.prog s1 (.call none 37 [(.var 3), (.var 0)]) .normal s2 := by
    have hf37 : Gen.prog Gen.fid_shogi_position_copy_active = some Gen.shogi_position_copy_active := rfl
    have hlen37 : Gen.shogi_position_copy_active.params.length = 2 := rfl
    exact ExS.call hargs1 hf37 hlen37 (by simpa [s2, s1] using ec) (Or.inl rfl)
  have hprefF := source_fields p hpref
  rcases hprefF with ⟨t81, t81_14, t96, t100, t104, t112, t113⟩
  have hFields : FieldsOK p s2.mem n := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simpa [s2, sc, t81] using hb81
    · simpa [s2, sc, t81_14] using hb81_95
    · simpa [s2, sc, t96] using hb96
    · simpa [s2, sc, t100] using hb100
    · simpa [s2, sc, t104] using hb104
    · simpa [s2, sc, t112] using hb112
    · simpa [s2, sc, t113] using hb113
  have hmoves_lt_n : moves < n := hf.lt (by rw [hmoves]; simp)
  have hmoves_ne_n : moves ≠ n := by omega
  have hmoves2 : s2.mem moves = some MB := by
    have hfm := hfc moves hmoves_ne_n
    rw [hfm]
    change m1 moves = some MB
    dsimp only [m1]
    rw [Mem.upd_ne hmoves_ne_n, Mem.upd_ne hmoves0]
    exact hmoves
  have ht1 : TablesIn m1 := by
    have ht0 : TablesIn (M.upd 0 (encodeLE 8 (n + 1))) := ht.upd0 _
    exact ht0.upd (List.replicate 41088 0) (by
      rw [Mem.upd_ne hn0]
      exact hf.2.2 n (Nat.le_refl _))
  have hn_not_table : n ≠ 8192 ∧ n ≠ 8193 ∧ n ≠ 8194 ∧ n ≠ 8195 ∧ n ≠ 8196 := by
    have hfresh := fresh_not_table hf ht (Nat.le_refl n)
    omega
  have ht2 : TablesIn s2.mem := by
    exact ⟨by rw [hfc 8192 (by omega : 8192 ≠ n)]; exact ht1.g1,
      by rw [hfc 8193 (by omega : 8193 ≠ n)]; exact ht1.g2,
      by rw [hfc 8194 (by omega : 8194 ≠ n)]; exact ht1.g3,
      by rw [hfc 8195 (by omega : 8195 ≠ n)]; exact ht1.g4,
      by rw [hfc 8196 (by omega : 8196 ≠ n)]; exact ht1.g5⟩
  have hf2 : Fresh s2.mem (n + 1) := by
    refine ⟨?_, ?_, ?_⟩
    · rw [hfc 0 (Ne.symm hn0)]
      change m1 0 = some (encodeLE 8 (n + 1))
      dsimp only [m1]
      rw [Mem.upd_ne (Ne.symm hn0), Mem.upd_eq]
    · omega
    · intro x hx
      rw [hfc x (by omega : x ≠ n)]
      dsimp only [m1]
      rw [Mem.upd_ne (by omega : x ≠ n), Mem.upd_ne (by omega : x ≠ 0)]
      exact hf.2.2 x (by omega)
  obtain ⟨K, cnt, s3, cb, hperm, ecall, hbuf⟩ :=
    Hcall s2.mem n moves (n + 1) WB MB hWBC hWBL hFields hmoves2 hlenM ht2 hf2
      h64succ hn0 hmoves0 hmoves_ne_n
      (fresh_not_table hf ht (Nat.le_refl n)) hmbt
  have hencarg : EvE Gen.prog s2 (.cast ⟨8, false⟩ (.bin .ne (some ⟨32, true⟩)
      (.const (.int ⟨32, true⟩ 1)) (.const (.int ⟨32, true⟩ 0)))) (.int IntTy.u8 1) := by
    refine EvE_of_eval (n := 4) ?_
    rfl
  have hargs2 : EvArgs Gen.prog s2
      [(.var 3), (.var 1), (.var 2),
       (.cast ⟨8, false⟩ (.bin .ne (some ⟨32, true⟩) (.const (.int ⟨32, true⟩ 1))
         (.const (.int ⟨32, true⟩ 0))))]
      [(.ptr n 0), (.ptr moves 0), (.int IntTy.u64 cap), (.int IntTy.u8 1)] :=
    EvArgs.cons (EvE.var rfl)
      (EvArgs.cons (EvE.var rfl)
        (EvArgs.cons (EvE.var rfl)
          (EvArgs.cons hencarg EvArgs.nil)))
  have hf35 : Gen.prog Gen.fid_generate_legal_mut_internal = some Gen.generate_legal_mut_internal := rfl
  have hlen35 : Gen.generate_legal_mut_internal.params.length = 4 := rfl
  let s4 : State := { s2 with mem := s3.mem, locals := s2.locals.upd 4 (.int IntTy.u64 cnt) }
  have hcall : ExS Gen.prog s2
      (.call (some 4) 35 [(.var 3), (.var 1), (.var 2),
        (.cast ⟨8, false⟩ (.bin .ne (some ⟨32, true⟩) (.const (.int ⟨32, true⟩ 1))
          (.const (.int ⟨32, true⟩ 0))))]) .normal s4 := by
    exact ExS.call_dst hargs2 hf35 hlen35 (by simpa [s4] using ecall)
  have hret : ExS Gen.prog s4 (.ret (some (.var 4)))
      (.ret (some (.int IntTy.u64 cnt))) s4 := ExS.ret (EvE.var rfl)
  refine ⟨K, hperm, cnt, s4, cb, ?_, hbuf⟩
  exact ExS.seq e0 (ExS.seq halloc'
    (ExS.seq hcopy (ExS.seq hcall hret)))


end Shogi.C.Proofs
