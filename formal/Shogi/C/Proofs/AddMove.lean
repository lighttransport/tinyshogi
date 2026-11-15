/-
  T7 generators, layer 0: `add_move` appends one 5-byte `ShogiMove` to a
  bounded buffer. The abstraction `Buf` describes the buffer by the list of
  moves *offered* so far: the count is `min L.length cap` and the first
  `count` slots hold `L.take cap` (C silently drops moves once the buffer is
  full; the spec of every caller is stated through this truncation).
-/
import Shogi.C.Proofs.InCheck

namespace Shogi.C.Proofs
open MiniC Shogi Shogi.C

theorem wr_window {α} (blk bs : List α) (o j : Nat) (h : o + j + bs.length ≤ blk.length) :
    ((blk.take (o + j) ++ bs ++ blk.drop (o + j + bs.length)).drop o).take (j + bs.length)
      = (blk.drop o).take j ++ bs := by
  apply List.ext_getElem
  · simp; omega
  · intro i h1 h2
    have e1 : min (o + j) blk.length = o + j := by omega
    have e2 : min j (blk.length - o) = j := by omega
    simp only [List.getElem_take, List.getElem_drop, List.getElem_append, List.length_append,
      List.length_take, List.length_drop, e1, e2]
    by_cases hi : i < j
    · simp [hi, show o + i < o + j by omega]; intro; omega
    · simp [hi, show ¬ o + i < o + j by omega, show o + i < o + j + bs.length by
        simp at h1; omega, show o + i - (o + j) = i - j by omega]

theorem wr_at {α} (blk bs : List α) (o : Nat) (h : o + bs.length ≤ blk.length) :
    ((blk.take o ++ bs ++ blk.drop (o + bs.length)).drop o).take bs.length = bs := by
  have := wr_window blk bs o 0 (by simpa using h)
  simpa using this

theorem wr_length {α} (blk bs : List α) (o : Nat) (h : o + bs.length ≤ blk.length) :
    (blk.take o ++ bs ++ blk.drop (o + bs.length)).length = blk.length := by
  simp; omega

/-- The allocator hands out `n` and every block from `n` on is unused. -/
def Fresh (m : Mem) (n : Nat) : Prop :=
  m 0 = some (encodeLE 8 n) ∧ n ≠ 0 ∧ ∀ x, n ≤ x → m x = none

theorem Fresh.allocAt {m : Mem} {n : Nat} (h : Fresh m n) (h64 : n < 2 ^ 64) : AllocAt m n :=
  ⟨h.1, h.2.1, h64, h.2.2 n (Nat.le_refl _)⟩

theorem Fresh.lt {m : Mem} {n x : Nat} (h : Fresh m n) (hx : m x ≠ none) : x < n :=
  Nat.lt_of_not_le fun hle => hx (h.2.2 x hle)

/-- After `alloc` of block `n`. -/
theorem Fresh.after_alloc {m : Mem} {n : Nat} (h : Fresh m n) (blk : Block) :
    Fresh ((m.upd 0 (encodeLE 8 (n + 1))).upd n blk) (n + 1) := by
  refine ⟨?_, by omega, fun x hx => ?_⟩
  · rw [Mem.upd_ne h.2.1.symm, Mem.upd_eq]
  · rw [Mem.upd_ne (by omega), Mem.upd_ne (by omega)]; exact h.2.2 x (by omega)

/-- Overwrite bytes `[o, o + bs.length)` of block `b` (no-op on a missing block). -/
def _root_.MiniC.Mem.write (m : Mem) (b o : Nat) (bs : List UInt8) : Mem :=
  match m b with
  | some blk => m.upd b (blk.take o ++ bs ++ blk.drop (o + bs.length))
  | none => m

theorem writeBytes_ok {m : Mem} {b o : Nat} {bs : List UInt8} {blk : Block} (hb : m b = some blk)
    (hl : o + bs.length ≤ blk.length) : writeBytes m b o bs = .ok (m.write b o bs) := by
  simp [writeBytes, Mem.write, hb, hl]

theorem _root_.MiniC.Mem.write_ne {m : Mem} {b o x : Nat} {bs : List UInt8} (h : x ≠ b) :
    (m.write b o bs) x = m x := by
  cases hb : m b <;> simp [Mem.write, hb, Mem.upd_ne h]

theorem _root_.MiniC.Mem.write_eq {m : Mem} {b o : Nat} {bs : List UInt8} {blk : Block} (hb : m b = some blk) :
    (m.write b o bs) b = some (blk.take o ++ bs ++ blk.drop (o + bs.length)) := by
  simp [Mem.write, hb, Mem.upd_eq]

theorem Fresh.write {m : Mem} {n b o : Nat} {bs : List UInt8} (h : Fresh m n) (hb : b ≠ 0) :
    Fresh (m.write b o bs) n := by
  refine ⟨by rw [Mem.write_ne hb.symm]; exact h.1, h.2.1, fun x hx => ?_⟩
  cases hblk : m b with
  | some blk =>
    have : b < n := h.lt (by rw [hblk]; simp)
    simp only [Mem.write, hblk]; rw [Mem.upd_ne (by omega)]; exact h.2.2 x hx
  | none => simp only [Mem.write, hblk]; exact h.2.2 x hx

/-- A `ShogiMove` buffer at `(mb, mo)` with capacity `cap` and its count at
    `(cb, co)`, after the moves `L` were offered. -/
structure Buf (m : Mem) (mb mo cb co cap : Nat) (L : List (List UInt8)) : Prop where
  cnt : ∃ cblk, m cb = some cblk ∧ co + 8 ≤ cblk.length ∧
    (cblk.drop co).take 8 = encodeLE 8 (min L.length cap)
  buf : ∃ blk, m mb = some blk ∧ mo + 5 * cap ≤ blk.length ∧
    (blk.drop mo).take (5 * min L.length cap) = (L.take cap).flatten
  len : ∀ x ∈ L, x.length = 5
  ne : mb ≠ cb
  mb0 : mb ≠ 0
  cb0 : cb ≠ 0
  cap64 : cap < 2 ^ 64

theorem flatten_length5 (L : List (List UInt8)) (h : ∀ x ∈ L, x.length = 5) :
    L.flatten.length = 5 * L.length := by
  induction L with
  | nil => rfl
  | cons a t ih =>
    simp only [List.flatten_cons, List.length_append, List.length_cons,
      h a (List.mem_cons_self ..), ih (fun x hx => h x (List.mem_cons_of_mem _ hx))]
    omega

/-- Blocks other than these four are untouched. -/
def Frame (m m' : Mem) (mb cb : Nat) : Prop :=
  ∀ x, x ≠ 0 → x ≠ mb → x ≠ cb → m x ≠ none → m' x = m x

theorem Frame.refl (m : Mem) (mb cb : Nat) : Frame m m mb cb := fun _ _ _ _ _ => rfl

theorem Frame.trans {m1 m2 m3 : Mem} {mb cb : Nat} (h1 : Frame m1 m2 mb cb) (h2 : Frame m2 m3 mb cb) :
    Frame m1 m3 mb cb := fun x a b c d => by rw [h2 x a b c (by rw [h1 x a b c d]; exact d), h1 x a b c d]

theorem Buf.frame {m m' : Mem} {mb mo cb co cap L} (h : Buf m mb mo cb co cap L)
    (hm : m' mb = m mb) (hc : m' cb = m cb) : Buf m' mb mo cb co cap L :=
  ⟨by rw [hc]; exact h.cnt, by rw [hm]; exact h.buf, h.len, h.ne, h.mb0, h.cb0, h.cap64⟩

theorem decode_take8 {cblk : List UInt8} {co k : Nat} (h : (cblk.drop co).take 8 = encodeLE 8 k)
    (hk : k < 2 ^ 64) : decodeLE ((cblk.drop co).take 8) = k := by
  rw [h]; exact decode_encode8 k hk

section add_move
variable {m : Mem} {mb mo cb co cap vb vo n : Nat} {L : List (List UInt8)} {mv : List UInt8}

/-- **`add_move`**: appends `mv` (the 5 bytes at `(vb, vo)`) to the buffer. -/
theorem add_move_spec (hbuf : Buf m mb mo cb co cap L) (hv : readBytes m vb vo 5 = .ok mv)
    (hf : Fresh m n) (h64 : n + 1 < 2 ^ 64) (hvb : vb ≠ 0) :
    ∃ s', ExS Gen.prog ⟨frameLocals Gen.add_move.params
        [.ptr mb mo, .ptr cb co, .int IntTy.u64 cap, .ptr vb vo], m, false⟩
      Gen.add_move.body .normal s' ∧
      Buf s'.mem mb mo cb co cap (L ++ [mv]) ∧ Fresh s'.mem (n + 1) ∧ Frame m s'.mem mb cb := by
  obtain ⟨cblk, hcb, hcl, hcv⟩ := hbuf.cnt
  obtain ⟨blk, hmb, hml, hmv⟩ := hbuf.buf
  have hmvl : mv.length = 5 := by
    unfold readBytes at hv; split at hv
    · cases hv
    · split at hv
      · simp only [Res.ok.injEq] at hv; subst hv; simp; omega
      · cases hv
  have hvbs : m vb ≠ none := by intro e; simp [readBytes, e] at hv
  have hvn : vb ≠ n := fun e => by subst e; exact hvbs (hf.2.2 _ (Nat.le_refl _))
  have hmbn : mb ≠ n := fun e => by rw [e, hf.2.2 n (Nat.le_refl _)] at hmb; cases hmb
  have hcbn : cb ≠ n := fun e => by rw [e, hf.2.2 n (Nat.le_refl _)] at hcb; cases hcb
  obtain ⟨k, hkd⟩ : ∃ k, k = min L.length cap := ⟨_, rfl⟩
  rw [← hkd] at hcv hmv
  have hk64 : k < 2 ^ 64 := by have := hbuf.cap64; omega
  let L0 := frameLocals Gen.add_move.params [.ptr mb mo, .ptr cb co, .int IntTy.u64 cap, .ptr vb vo]
  let s0 : State := ⟨L0, m, false⟩
  let s1 : State := { s0 with locals := s0.locals.upd 4 (.ptr vb vo) }
  have h1 : ExS Gen.prog s0 (.set 4 (.var 3)) .normal s1 := ExS.set (EvE.var rfl)
  let m1 := (m.upd 0 (encodeLE 8 (n + 1))).upd n (List.replicate 5 0)
  let s2 : State := { s1 with mem := m1, locals := s1.locals.upd 3 (.ptr n 0) }
  have h2 : ExS Gen.prog s1 (.alloc 3 5) .normal s2 := exec_alloc (hf.allocAt (by omega)) 3 5
  have hm1n : m1 n = some (List.replicate 5 0) := Mem.upd_eq
  have hm1o : ∀ x, x ≠ 0 → x ≠ n → m1 x = m x := fun x a b => by
    simp only [m1]; rw [Mem.upd_ne b, Mem.upd_ne a]
  let m2 := m1.write n 0 mv
  have hrv1 : readBytes m1 vb vo 5 = .ok mv := by
    simp only [readBytes, hm1o vb hvb hvn]; exact hv
  have h3 : ExS Gen.prog s2 (.memcpy (.var 3) (.var 4) (.const (.int ⟨64, false⟩ 5))) .normal
      { s2 with mem := m2 } :=
    ExS.memcpy (EvE.var rfl) (EvE.var rfl) (EvE.const _) rfl (by simp [Ne.symm hvn]) hrv1
      (writeBytes_ok hm1n (by simp [hmvl]))
  have hm2o : ∀ x, x ≠ 0 → x ≠ n → m2 x = m x := fun x a b => by
    simp only [m2]; rw [Mem.write_ne b]; exact hm1o x a b
  have hm2n : m2 n = some mv := by
    simp only [m2]; rw [Mem.write_eq hm1n]; simp [hmvl]
  have hf2 : Fresh m2 (n + 1) := (hf.after_alloc _).write hf.2.1
  let s3 : State := { s2 with mem := m2 }
  have hrc : readBytes m2 cb co 8 = .ok (encodeLE 8 k) := by
    simp only [readBytes, hm2o cb hbuf.cb0 hcbn, hcb, hcl, ite_true, hcv]
  have hcap := hbuf.cap64
  have hcond : EvE Gen.prog s3 (.bin .lt (some ⟨64, false⟩) (.load (.int ⟨64, false⟩) (.var 1)) (.var 2))
      (boolVal (decide (k < cap))) := by
    refine EvE.bin (va := .int IntTy.u64 k) (EvE.load (EvE.var (v := .ptr cb co) rfl) ?_) (EvE.var (v := .int IntTy.u64 cap) rfl) ?_
    · show (readBytes m2 cb co 8).bind _ = _
      simp [hrc, Res.bind, decode_encode8 k hk64]; rfl
    · simp [evalBin, isPtr, evalBinInt, binInt, intOf, IntTy.u64, Res.bind]
  have hhead : ∀ {r s'}, ExS Gen.prog s3 (.ite (.bin .lt (some ⟨64, false⟩) (.load (.int ⟨64, false⟩)
      (.var 1)) (.var 2)) (.seq (.set 5 (.load (.int ⟨64, false⟩) (.var 1))) (.seq (.store
      (.int ⟨64, false⟩) (.var 1) (.cast ⟨64, false⟩ (.bin .add (some ⟨64, false⟩) (.cast ⟨64, false⟩
      (.var 5)) (.const (.int ⟨64, false⟩ 1))))) (.memcpy (.index (.var 0) (.var 5) 5) (.var 3)
      (.const (.int ⟨64, false⟩ 5))))) .skip) r s' →
      ExS Gen.prog s0 Gen.add_move.body r s' := fun h => ExS.seq h1 (ExS.seq h2 (ExS.seq h3 h))
  have hframe2 : Frame m m2 mb cb := fun x a _ _ d => hm2o x a (fun e => by
    subst e; exact d (hf.2.2 _ (Nat.le_refl _)))
  by_cases hlt : k < cap
  · have hkL : k = L.length := by omega
    have hk1 : k + 1 < 2 ^ 64 := by omega
    let s4 : State := { s3 with locals := s3.locals.upd 5 (.int IntTy.u64 k) }
    have hld : EvE Gen.prog s3 (.load (.int ⟨64, false⟩) (.var 1)) (.int IntTy.u64 k) := by
      refine EvE.load (EvE.var (v := .ptr cb co) rfl) ?_
      show (readBytes m2 cb co 8).bind _ = _
      simp [hrc, Res.bind, decode_encode8 k hk64]; rfl
    have h4 : ExS Gen.prog s3 (.set 5 (.load (.int ⟨64, false⟩) (.var 1))) .normal s4 := ExS.set hld
    let m3 := m2.write cb co (encodeLE 8 (k + 1))
    have hm2c : m2 cb = some cblk := by rw [hm2o cb hbuf.cb0 hcbn]; exact hcb
    have h5 : ExS Gen.prog s4 (.store (.int ⟨64, false⟩) (.var 1) (.cast ⟨64, false⟩ (.bin .add
        (some ⟨64, false⟩) (.cast ⟨64, false⟩ (.var 5)) (.const (.int ⟨64, false⟩ 1))))) .normal
        { s4 with mem := m3 } := by
      refine ExS.store (pa := .ptr cb co) (v := .int IntTy.u64 (k + 1)) (EvE.var rfl) ?_ rfl ?_
      · apply EvE_of_eval (n := 4)
        simp [evalExpr, s4, Locals.upd, evalCast, evalBin, isPtr, evalBinInt, binInt, intOf, IntTy.u64,
          IntTy.wrap, IntTy.modulus, Res.bind, Nat.mod_eq_of_lt hk64, Nat.mod_eq_of_lt hk1]
      · simp only [store, IntTy.u64, IntTy.bytes, ite_true]
        exact writeBytes_ok hm2c (by simp [encodeLE]; omega)
    have hm3b : m3 mb = some blk := by
      simp only [m3]; rw [Mem.write_ne hbuf.ne, hm2o mb hbuf.mb0 hmbn]; exact hmb
    have hm3n : m3 n = some mv := by simp only [m3]; rw [Mem.write_ne (Ne.symm hcbn)]; exact hm2n
    let m4 := m3.write mb (mo + k * 5) mv
    have h6 : ExS Gen.prog { s4 with mem := m3 } (.memcpy (.index (.var 0) (.var 5) 5) (.var 3)
        (.const (.int ⟨64, false⟩ 5))) .normal { s4 with mem := m4 } := by
      refine ExS.memcpy (bd := mb) (od := mo + k * 5) (bs := n) (os := 0) (bytes := mv)
        (EvE.index (EvE.var (v := .ptr mb mo) rfl) (EvE.var (v := .int IntTy.u64 k) rfl) ?_)
        (EvE.var rfl) (EvE.const _) rfl (by simp [hmbn]) ?_ ?_
      · simp [IntTy.u64, ptrAddN, hm3b]; omega
      · simp [readBytes, hm3n, hmvl, List.take_of_length_le (show mv.length ≤ 5 by omega)]
      · exact writeBytes_ok hm3b (by rw [hmvl]; omega)
    refine ⟨{ s4 with mem := m4 }, hhead (ExS.ite (bc := true) hcond (by simp [boolVal, hlt]; rfl)
      (ExS.seq h4 (ExS.seq h5 h6))), ?_, ?_, ?_⟩
    · refine ⟨⟨cblk.take co ++ encodeLE 8 (k + 1) ++ cblk.drop (co + (encodeLE 8 (k + 1)).length), ?_, ?_, ?_⟩, ⟨blk.take (mo + k * 5) ++ mv ++ blk.drop (mo + k * 5 + mv.length), ?_, ?_, ?_⟩,
        ?_, hbuf.ne, hbuf.mb0, hbuf.cb0, hbuf.cap64⟩
      · show m4 cb = _
        simp only [m4]; rw [Mem.write_ne (Ne.symm hbuf.ne)]; simp only [m3]; exact Mem.write_eq hm2c
      · simp [encodeLE]; omega
      · have hmin : min (L ++ [mv]).length cap = k + 1 := by simp; omega
        rw [hmin]
        have := wr_at cblk (encodeLE 8 (k + 1)) co (by simp [encodeLE]; omega)
        simpa [encodeLE] using this
      · exact Mem.write_eq hm3b
      · simp; omega
      · have hmin : min (L ++ [mv]).length cap = k + 1 := by simp; omega
        rw [hmin]
        have hw := wr_window blk mv mo (k * 5) (by rw [hmvl]; omega)
        rw [hmvl] at hw
        rw [show mo + k * 5 + mv.length = mo + k * 5 + 5 by rw [hmvl],
          show 5 * (k + 1) = k * 5 + 5 by omega, hw, show k * 5 = 5 * k by omega, hmv,
          List.take_of_length_le (show L.length ≤ cap by omega),
          List.take_of_length_le (show (L ++ [mv]).length ≤ cap by simp; omega)]
        simp
      · intro x hx
        rcases List.mem_append.1 hx with h | h
        · exact hbuf.len x h
        · simp at h; subst h; exact hmvl
    · exact (hf2.write hbuf.cb0).write hbuf.mb0
    · intro x a b c d
      have hxn : x ≠ n := fun e => by subst e; exact d (hf.2.2 _ (Nat.le_refl _))
      show m4 x = m x
      simp only [m4, m3]; rw [Mem.write_ne b, Mem.write_ne c]; exact hm2o x a hxn
  · have hkc : k = cap := by omega
    refine ⟨s3, hhead (ExS.ite (bc := false) hcond (by simp [boolVal, hlt]; rfl) ExS.skip), ?_, hf2, hframe2⟩
    have hmin : min (L ++ [mv]).length cap = cap := by simp; omega
    have htk : (L ++ [mv]).take cap = L.take cap := List.take_append_of_le_length (by omega)
    refine ⟨⟨cblk, by show m2 cb = _; rw [hm2o cb hbuf.cb0 hcbn]; exact hcb, hcl,
        by rw [hmin, ← hkc]; exact hcv⟩,
      ⟨blk, by show m2 mb = _; rw [hm2o mb hbuf.mb0 hmbn]; exact hmb, hml,
        by rw [hmin, htk]; have := hmv; rw [hkc] at this; exact this⟩,
      ?_, hbuf.ne, hbuf.mb0, hbuf.cb0, hbuf.cap64⟩
    intro x hx
    rcases List.mem_append.1 hx with h | h
    · exact hbuf.len x h
    · simp at h; subst h; exact hmvl
end add_move

end Shogi.C.Proofs
