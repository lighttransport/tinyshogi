/-
  R3: the public pseudo-move generators `shogi_generate_pseudo` (fid 29) and
  `shogi_generate_pseudo_for_color` (fid 30). Each allocates an 8-byte count,
  initialises it to 0, calls the internal generator (fid 28 / fid 27), and
  returns the count written. The refinement reuses `generate_pseudo_wrap`.
-/
import Shogi.C.Proofs.GenPseudo

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

namespace Shogi.C.Proofs
variable {posBlock : Nat}
open MiniC Shogi Shogi.C

/-- Initialise an 8-byte count block at `n` in local `loc`. Mirrors
    `legal_count_init` but with a caller-chosen local id. -/
theorem count_init {s : State} {loc n mb mo cap : Nat} {blk : Block} (hf : Fresh s.mem n)
    (h64 : n + 4000000200 < 2 ^ 64) (hro : s.ro = false)
    (hmb : s.mem mb = some blk) (hlen : mo + 5 * cap ≤ blk.length)
    (hmb0 : mb ≠ 0) (hcap : cap < 2 ^ 64) :
    ∃ s', ExS Gen.prog s (.seq (.alloc loc 8)
        (.store (.int ⟨64, false⟩) (.var loc) (.cast ⟨64, false⟩ (.const (.int ⟨32, true⟩ 0))))) .normal s' ∧
      Buf s'.mem mb mo n 0 cap [] ∧ Fresh s'.mem (n + 1) ∧ s'.locals loc = some (.ptr n 0) ∧
      (∀ x, x ≠ loc → s'.locals x = s.locals x) ∧ s'.ro = s.ro ∧
      (∀ b, b ≠ 0 → b ≠ n → s'.mem b = s.mem b) := by
  have e1 := exec_alloc (hf.allocAt (by omega)) loc 8
  have hf1 := hf.after_alloc (List.replicate 8 0)
  generalize hM : (s.mem.upd 0 (encodeLE 8 (n + 1))).upd n (List.replicate 8 0) = M at e1 hf1
  have g1 : M n = some (List.replicate 8 0) := by rw [← hM]; exact Mem.upd_eq
  have gb : ∀ b, b ≠ 0 → b ≠ n → M b = s.mem b := fun b a c => by rw [← hM, Mem.upd_ne c, Mem.upd_ne a]
  have hmbn : mb ≠ n := fun e => by have := hf.2.2 n (Nat.le_refl _); rw [← e, hmb] at this; simp at this
  let L1 := s.locals.upd loc (.ptr n 0)
  have es : ExS Gen.prog ⟨L1, M, s.ro⟩ (.store (.int ⟨64, false⟩) (.var loc)
      (.cast ⟨64, false⟩ (.const (.int ⟨32, true⟩ 0)))) .normal ⟨L1, M.write n 0 (encodeLE 8 0), s.ro⟩ := by
    refine ExS.store (pa := .ptr n 0) (v := .int ⟨64, false⟩ 0) (EvE.var (by simp [L1, Locals.upd]))
      (EvE_of_eval (n := 2) ?_) hro ?_
    · simp [evalExpr, evalCast, IntTy.wrap, IntTy.toInt, IntTy.modulus]
    · simp only [store, Ty.size, IntTy.bytes]
      exact writeBytes_ok g1 (by simp [encodeLE_length])
  refine ⟨_, ExS.seq e1 es, ?_, ?_, by simp [L1, Locals.upd], fun x a => by simp [L1, Locals.upd, a], rfl,
    fun b a c => ?_⟩
  · refine ⟨⟨encodeLE 8 0, ?_, by simp [encodeLE_length], by simp [List.take_of_length_le, encodeLE_length]⟩,
      ⟨blk, ?_, hlen, by simp⟩, by simp, hmbn, hmb0, hf.2.1, hcap⟩
    · show (M.write n 0 _) n = _
      rw [Mem.write_eq g1]; simp [encodeLE_length]
    · show (M.write n 0 _) mb = _
      rw [Mem.write_ne hmbn, gb mb hmb0 hmbn]; exact hmb
  · refine ⟨?_, by omega, fun x hx => ?_⟩
    · show (M.write n 0 _) 0 = _
      rw [Mem.write_ne hf.2.1.symm]; exact hf1.1
    · show (M.write n 0 _) x = _
      rw [Mem.write_ne (by omega)]; exact hf1.2.2 x hx
  · show (M.write n 0 (encodeLE 8 0)) b = s.mem b
    rw [Mem.write_ne c]
    exact gb b a c

/-- `shogi_generate_pseudo` (fid 29) writes a permutation of the side-to-move's
    pseudo moves and returns its count (capped at `cap`). -/
theorem shogi_generate_pseudo_spec {p : Position} {m : Mem} {mb mo cap n : Nat} {blk : Block}
    (hm : m posBlock = some (encode p)) (hmb : m mb = some blk)
    (hlen : mo + 5 * cap ≤ blk.length) (hf : Fresh m n)
    (h64 : n + 4000000200 < 2 ^ 64) (hcap : cap < 2 ^ 64)
    (hmb0 : mb ≠ 0) (hpm : posBlock ≠ mb) :
    ∃ s' cnt, ExS Gen.prog ⟨frameLocals Gen.shogi_generate_pseudo.params
        [posPtr' posBlock, .ptr mb mo, .int IntTy.u64 cap], m, false⟩
      Gen.shogi_generate_pseudo.body (.ret (some (.int IntTy.u64 cnt))) s' ∧
      cnt = min (pseudoC p p.side).length cap ∧
      Buf s'.mem mb mo n 0 cap (pseudoC p p.side) := by
  let s0 : State := ⟨frameLocals Gen.shogi_generate_pseudo.params
    [posPtr' posBlock, .ptr mb mo, .int IntTy.u64 cap], m, false⟩
  -- guard: pointers are non-null
  have hguard : EvE Gen.prog s0 (.lor (.bin .eq none (.var 0) (.const .null))
      (.bin .eq none (.var 1) (.const .null))) (boolVal false) := by
    refine EvE_of_eval (n := 4) ?_
    rfl
  have e0 : ExS Gen.prog s0
      (.ite (.lor (.bin .eq none (.var 0) (.const .null)) (.bin .eq none (.var 1) (.const .null)))
        (.ret (some (.cast ⟨64, false⟩ (.const (.int ⟨32, true⟩ 0))))) .skip) .normal s0 :=
    ExS.ite (bc := false) hguard rfl ExS.skip
  -- alloc + init count in local 3
  obtain ⟨s1, ea, hbuf0, hf1, hl3, hlother, hro1, hf1mem⟩ :=
    count_init (s := s0) (loc := 3) (n := n) (mb := mb) (mo := mo) (cap := cap) (blk := blk)
      hf (by omega) rfl hmb hlen hmb0 hcap
  have hpn : posBlock ≠ n := by
    intro h
    have hnempty' : m posBlock = none := by rw [h]; exact hf.2.2 n (Nat.le_refl n)
    rw [hnempty'] at hm
    cases hm
  have hpos0 : posBlock ≠ 0 := posBlock_ne_zero hf.1 hm
  have hs1mempos : s1.mem posBlock = some (encode p) := by
    rw [hf1mem posBlock hpos0 hpn]
    exact hm
  -- call fid 28
  obtain ⟨sg, n', eg, hbG, hfG, hnG, hfrG⟩ := generate_pseudo_wrap (p := p) (m := s1.mem)
    (mb := mb) (mo := mo) (cb := n) (co := 0) (cap := cap) (n := n + 1)
    hbuf0 hf1 (by omega) hs1mempos hpm (by omega)
  have hs1ro : s1.ro = false := by rw [hro1]
  have eg' : ExS Gen.prog ⟨frameLocals Gen.generate_pseudo.params
      [posPtr' posBlock, .ptr mb mo, .ptr n 0, .int IntTy.u64 cap], s1.mem, s1.ro⟩
      Gen.generate_pseudo.body Outcome.normal sg := by
    simpa [hs1ro] using eg
  have hl0 : s1.locals 0 = some (posPtr' posBlock) := by rw [hlother 0 (by omega)]; rfl
  have hl1 : s1.locals 1 = some (.ptr mb mo) := by rw [hlother 1 (by omega)]; rfl
  have hl2 : s1.locals 2 = some (.int IntTy.u64 cap) := by rw [hlother 2 (by omega)]; rfl
  have ecall : ExS Gen.prog s1
      (.call none 28 [(.var 0), (.var 1), (.var 3), (.var 2)]) .normal
      { s1 with mem := sg.mem } := by
    refine ExS.call (vs := [posPtr' posBlock, .ptr mb mo, .ptr n 0, .int IntTy.u64 cap])
      (EvArgs.cons (EvE.var hl0)
        (EvArgs.cons (EvE.var hl1)
          (EvArgs.cons (EvE.var hl3)
            (EvArgs.cons (EvE.var hl2) EvArgs.nil)))) rfl rfl eg' (Or.inl rfl)
  -- read back the count
  have hcntblk : ∃ cb, sg.mem n = some cb ∧ cb.take 8 = encodeLE 8 (min (pseudoC p p.side).length cap) := by
    obtain ⟨cb, hcb, hcbl, hcbv⟩ := hbG.cnt
    exact ⟨cb, hcb, by simpa using hcbv⟩
  obtain ⟨cb, hcb, hcbv⟩ := hcntblk
  have hread : load sg.mem (Ty.int ⟨64, false⟩) (.ptr n 0) =
      .ok (.int IntTy.u64 (min (pseudoC p p.side).length cap)) := by
    have hlen8 : 8 ≤ cb.length := by
      have := congrArg List.length hcbv
      simp [encodeLE_length] at this
      omega
    simp only [load, readBytes, hcb, Ty.size, IntTy.bytes]
    simp [hlen8, hcbv, decode_encode8, IntTy.u64, show min (pseudoC p p.side).length cap < 2 ^ 64 by omega]
  have eret : ExS Gen.prog { s1 with mem := sg.mem }
      (.ret (some (.load (.int ⟨64, false⟩) (.var 3))))
      (.ret (some (.int IntTy.u64 (min (pseudoC p p.side).length cap))))
      { s1 with mem := sg.mem } := by
    refine ExS.ret (EvE_of_eval (n := 4) ?_)
    simp [evalExpr, hl3, hread]
  refine ⟨{ s1 with mem := sg.mem }, min (pseudoC p p.side).length cap, ?_, rfl, hbG⟩
  exact ExS.seq e0 (ExS.seq ea (ExS.seq ecall eret))

/-- `shogi_generate_pseudo_for_color` (fid 30) writes a permutation of the
    given colour's pseudo moves and returns its count. -/
theorem shogi_generate_pseudo_for_color_spec {p : Position} {c : Color}
    {m : Mem} {mb mo cap n : Nat} {blk : Block}
    (hm : m posBlock = some (encode p)) (hmb : m mb = some blk)
    (hlen : mo + 5 * cap ≤ blk.length) (hf : Fresh m n)
    (h64 : n + 4000000200 < 2 ^ 64) (hcap : cap < 2 ^ 64)
    (hmb0 : mb ≠ 0) (hpm : posBlock ≠ mb) :
    ∃ s' cnt, ExS Gen.prog ⟨frameLocals Gen.shogi_generate_pseudo_for_color.params
        [posPtr' posBlock, u32 c.idx, .ptr mb mo, .int IntTy.u64 cap], m, false⟩
      Gen.shogi_generate_pseudo_for_color.body (.ret (some (.int IntTy.u64 cnt))) s' ∧
      cnt = min (pseudoC p c).length cap ∧
      Buf s'.mem mb mo n 0 cap (pseudoC p c) := by
  let s0 : State := ⟨frameLocals Gen.shogi_generate_pseudo_for_color.params
    [posPtr' posBlock, u32 c.idx, .ptr mb mo, .int IntTy.u64 cap], m, false⟩
  have hguard : EvE Gen.prog s0
      (.lor (.lor (.bin .eq none (.var 0) (.const .null))
        (.bin .eq none (.var 2) (.const .null)))
        (.land (.bin .ne (some ⟨32, false⟩) (.cast ⟨32, false⟩ (.var 1))
          (.cast ⟨32, false⟩ (.const (.int ⟨32, true⟩ 0))))
          (.bin .ne (some ⟨32, false⟩) (.cast ⟨32, false⟩ (.var 1))
            (.cast ⟨32, false⟩ (.const (.int ⟨32, true⟩ 1)))))) (boolVal false) := by
    refine EvE_of_eval (n := 8) ?_
    cases c <;> rfl
  have e0 : ExS Gen.prog s0
      (.ite (.lor (.lor (.bin .eq none (.var 0) (.const .null))
        (.bin .eq none (.var 2) (.const .null)))
        (.land (.bin .ne (some ⟨32, false⟩) (.cast ⟨32, false⟩ (.var 1))
          (.cast ⟨32, false⟩ (.const (.int ⟨32, true⟩ 0))))
          (.bin .ne (some ⟨32, false⟩) (.cast ⟨32, false⟩ (.var 1))
            (.cast ⟨32, false⟩ (.const (.int ⟨32, true⟩ 1))))))
        (.ret (some (.cast ⟨64, false⟩ (.const (.int ⟨32, true⟩ 0))))) .skip) .normal s0 :=
    ExS.ite (bc := false) hguard rfl ExS.skip
  obtain ⟨s1, ea, hbuf0, hf1, hl4, hlother, hro1, hf1mem⟩ :=
    count_init (s := s0) (loc := 4) (n := n) (mb := mb) (mo := mo) (cap := cap) (blk := blk)
      hf (by omega) rfl hmb hlen hmb0 hcap
  have hpn : posBlock ≠ n := by
    intro h
    have hnempty' : m posBlock = none := by rw [h]; exact hf.2.2 n (Nat.le_refl n)
    rw [hnempty'] at hm
    cases hm
  have hpos0 : posBlock ≠ 0 := posBlock_ne_zero hf.1 hm
  have hs1mempos : s1.mem posBlock = some (encode p) := by
    rw [hf1mem posBlock hpos0 hpn]
    exact hm
  obtain ⟨sg, n', eg, hbG, hfG, hnG, hfrG⟩ := generate_pseudo_spec (p := p) (c := c)
    (m := s1.mem) (mb := mb) (mo := mo) (cb := n) (co := 0) (cap := cap) (n := n + 1)
    hbuf0 hf1 (by omega) hs1mempos hpm (by omega)
  have hs1ro : s1.ro = false := by rw [hro1]
  have eg' : ExS Gen.prog ⟨frameLocals Gen.generate_pseudo_for_color.params
      [posPtr' posBlock, u32 c.idx, .ptr mb mo, .ptr n 0, .int IntTy.u64 cap], s1.mem, s1.ro⟩
      Gen.generate_pseudo_for_color.body Outcome.normal sg := by
    simpa [hs1ro] using eg
  have hl0 : s1.locals 0 = some (posPtr' posBlock) := by rw [hlother 0 (by omega)]; rfl
  have hl1 : s1.locals 1 = some (u32 c.idx) := by rw [hlother 1 (by omega)]; rfl
  have hl2 : s1.locals 2 = some (.ptr mb mo) := by rw [hlother 2 (by omega)]; rfl
  have hl3 : s1.locals 3 = some (.int IntTy.u64 cap) := by rw [hlother 3 (by omega)]; rfl
  have ecall : ExS Gen.prog s1
      (.call none 27 [(.var 0), (.var 1), (.var 2), (.var 4), (.var 3)]) .normal
      { s1 with mem := sg.mem } := by
    refine ExS.call (vs := [posPtr' posBlock, u32 c.idx, .ptr mb mo, .ptr n 0, .int IntTy.u64 cap])
      (EvArgs.cons (EvE.var hl0) (EvArgs.cons (EvE.var hl1)
        (EvArgs.cons (EvE.var hl2) (EvArgs.cons (EvE.var hl4)
          (EvArgs.cons (EvE.var hl3) EvArgs.nil))))) rfl rfl eg' (Or.inl rfl)
  have hcntblk : ∃ cb, sg.mem n = some cb ∧ cb.take 8 = encodeLE 8 (min (pseudoC p c).length cap) := by
    obtain ⟨cb, hcb, hcbl, hcbv⟩ := hbG.cnt
    exact ⟨cb, hcb, by simpa using hcbv⟩
  obtain ⟨cb, hcb, hcbv⟩ := hcntblk
  have hread : load sg.mem (Ty.int ⟨64, false⟩) (.ptr n 0) =
      .ok (.int IntTy.u64 (min (pseudoC p c).length cap)) := by
    have hlen8 : 8 ≤ cb.length := by
      have := congrArg List.length hcbv
      simp [encodeLE_length] at this
      omega
    simp only [load, readBytes, hcb, Ty.size, IntTy.bytes]
    simp [hlen8, hcbv, decode_encode8, IntTy.u64, show min (pseudoC p c).length cap < 2 ^ 64 by omega]
  have eret : ExS Gen.prog { s1 with mem := sg.mem }
      (.ret (some (.load (.int ⟨64, false⟩) (.var 4))))
      (.ret (some (.int IntTy.u64 (min (pseudoC p c).length cap))))
      { s1 with mem := sg.mem } := by
    refine ExS.ret (EvE_of_eval (n := 4) ?_)
    simp [evalExpr, hl4, hread]
  refine ⟨{ s1 with mem := sg.mem }, min (pseudoC p c).length cap, ?_, rfl, hbG⟩
  exact ExS.seq e0 (ExS.seq ea (ExS.seq ecall eret))

end Shogi.C.Proofs
