/-
  T7 generators, layer 2: `add_pseudo_drops` (hand mask, pawn-file mask, and
  per empty square the drops its restrictions allow, lowest hand index first).
  The bit manipulation is mirrored by `allowedC`/`dropBits`; their meaning is
  a kernel-checked finite fact (`allowed_bits`).
-/
import Shogi.C.Proofs.AddSlide

namespace Shogi.C.Proofs
open MiniC Shogi Shogi.C

def dropBits : Nat → Nat → List Nat
  | 0, _ => []
  | k + 1, a => if a = 0 then [] else ctzNat 32 a :: dropBits k (a &&& (a - 1))

def allowedC (act : Nat) (pf : Bool) (c : Color) (r : Nat) : Nat :=
  let a1 := if pf then act &&& (2 ^ 32 - 1 - 1) else act
  if (c == .black && r == 0) || (c == .white && r == 8) then a1 &&& (2 ^ 32 - 1 - 7)
  else if (c == .black && r == 1) || (c == .white && r == 7) then a1 &&& (2 ^ 32 - 1 - 4)
  else a1

def allowedS (act : Nat) (pf : Bool) (c : Color) (r : Nat) : List Nat :=
  ((List.finRange 7).filter (fun i => act.testBit i.val && !(i.val == 0 && pf) &&
    !deadRow c (PieceType.ofHandIndex i) r)).map (·.val)

set_option maxRecDepth 100000 in
/-- The C bit manipulation selects exactly the allowed hand indices, in order. -/
theorem allowed_bits : ∀ c : Color, ∀ act : Fin 128, ∀ pf : Bool, ∀ r : Fin 9,
    dropBits 8 (allowedC act.val pf c r.val) = allowedS act.val pf c r.val := by
  intro c; cases c <;> decide +kernel

/-- The hand byte `hand[c][i]`. -/
def hb (p : Position) (c : Color) (i : Nat) : Nat := ((encode p).getD (81 + 7 * c.idx + i) 0).toNat

def actUpTo (p : Position) (c : Color) : Nat → Nat
  | 0 => 0
  | i + 1 => if hb p c i ≠ 0 then actUpTo p c i ||| 2 ^ i else actUpTo p c i

theorem actUpTo_lt (p : Position) (c : Color) : ∀ i, actUpTo p c i < 2 ^ i := by
  intro i; induction i with
  | zero => simp [actUpTo]
  | succ i ih =>
    simp only [actUpTo]; split
    · exact Nat.or_lt_two_pow (Nat.lt_of_lt_of_le ih (Nat.pow_le_pow_right (by decide) (by omega)))
        (Nat.pow_lt_pow_right (by decide) (by omega))
    · exact Nat.lt_of_lt_of_le ih (Nat.pow_le_pow_right (by decide) (by omega))

theorem ev_ne0e {s : State} {e : Expr} {b : Nat} (hb : b < 256) (h : EvE Gen.prog s e (.int IntTy.u8 b)) :
    EvE Gen.prog s (.bin .ne (some ⟨32, true⟩) (.cast ⟨32, true⟩ e) (.const (.int ⟨32, true⟩ 0)))
      (boolVal (decide (b ≠ 0))) := by
  refine EvE.bin (EvE.cast h rfl) (EvE.const _) ?_
  simp [evalBin, isPtr, evalBinInt, binInt, intOf, IntTy.u8, evalCast, IntTy.modulus, IntTy.toInt, Res.bind,
    Nat.mod_eq_of_lt (show b < 4294967296 by omega), show ¬ (2147483648 ≤ b) by omega]

theorem ev_bor_shl {s : State} {j k a i : Nat} {ti : IntTy} (ha : a < 2 ^ 32) (hi : i < 32)
    (hj : s.locals j = some (.int IntTy.u32 a)) (hk : s.locals k = some (.int ti i))
    (hti : ti.toInt i = i) :
    EvE Gen.prog s (.cast ⟨32, false⟩ (.bin .bor (some ⟨32, false⟩) (.cast ⟨32, false⟩ (.var j))
      (.cast ⟨32, false⟩ (.bin .shl (some ⟨32, false⟩) (.const (.int ⟨32, false⟩ 1)) (.var k)))))
      (.int IntTy.u32 (a ||| 2 ^ i)) := by
  have h2 : 2 ^ i < 2 ^ 32 := Nat.pow_lt_pow_right (by decide) hi
  have hor : a ||| 2 ^ i < 2 ^ 32 := Nat.or_lt_two_pow ha h2
  apply EvE_of_eval (n := 6)
  simp [evalExpr, hj, hk, evalCast, evalBin, isPtr, evalBinInt, binInt, intOf, IntTy.u32, IntTy.modulus,
    Res.bind, hti, MiniC.guard, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt h2, Nat.mod_eq_of_lt hor,
    show (i : Int) < 32 by omega]

theorem ev_hand {s : State} {p : Position} {c : Color} {i : Nat} (hi : i < 7)
    (h0 : s.locals 0 = some posPtr) (h1 : s.locals 1 = some (.int IntTy.u32 c.idx))
    (h9 : s.locals 9 = some (.int IntTy.u32 i)) (hm : s.mem posBlock = some (encode p)) :
    EvE Gen.prog s (.load (.int ⟨8, false⟩) (.index (.index (.field (.var 0) 81) (.var 1) 7) (.var 9) 1))
      (.int IntTy.u8 (hb p c i)) := by
  have hc : c.idx < 2 := by cases c <;> decide
  have hlen := encode_length p
  refine EvE.load (pa := .ptr posBlock (0 + 81 + c.idx * 7 + i * 1))
    (EvE.index (pb := .ptr posBlock (0 + 81 + c.idx * 7))
      (EvE.index (pb := .ptr posBlock (0 + 81)) (EvE.field (EvE.var h0) (by simp [ptrAddN, posPtr, hm, hlen]))
        (EvE.var h1) (by simp [IntTy.u32, ptrAddN, hm, hlen]; omega))
      (EvE.var h9) (by simp [IntTy.u32, ptrAddN, hm, hlen]; omega)) ?_
  simp only [load, Ty.size, IntTy.bytes, show (8 : Nat) / 8 = 1 by rfl]
  rw [readByte hm _ (by rw [hlen]; omega)]
  simp [Res.bind, decodeLE, hb, IntTy.u8, Nat.mul_comm]

def handBody : Stmt := (.ite (.bin .lt (some ⟨32, false⟩) (.var 9) (.const (.int ⟨32, false⟩ 7))) (.ite (.bin .ne (some ⟨32, true⟩) (.cast ⟨32, true⟩ (.load (.int ⟨8, false⟩) (.index (.index (.field (.var 0) 81) (.var 1) 7) (.var 9) 1))) (.const (.int ⟨32, true⟩ 0))) (.set 6 (.cast ⟨32, false⟩ (.bin .bor (some ⟨32, false⟩) (.cast ⟨32, false⟩ (.var 6)) (.cast ⟨32, false⟩ (.bin .shl (some ⟨32, false⟩) (.const (.int ⟨32, false⟩ 1)) (.var 9)))))) .skip) .brk)
def handStep : Stmt := (.set 9 (.cast ⟨32, false⟩ (.bin .add (some ⟨32, false⟩) (.cast ⟨32, false⟩ (.var 9)) (.const (.int ⟨32, false⟩ 1)))))

theorem add_pseudo_drops_loop0_eq : Gen.add_pseudo_drops_loop0 = .loop handBody handStep := rfl

theorem hand_loop (p : Position) (c : Color) :
    ∀ d i (s : State), i + d = 7 → s.locals 0 = some posPtr → s.locals 1 = some (.int IntTy.u32 c.idx) →
      s.locals 9 = some (.int IntTy.u32 i) → s.locals 6 = some (.int IntTy.u32 (actUpTo p c i)) →
      s.mem posBlock = some (encode p) →
      ∃ s', ExS Gen.prog s (.loop handBody handStep) .normal s' ∧ s'.mem = s.mem ∧ s'.ro = s.ro ∧
        s'.locals 6 = some (.int IntTy.u32 (actUpTo p c 7)) ∧ ∀ x, x ≠ 6 → x ≠ 9 → s'.locals x = s.locals x := by
  intro d
  induction d with
  | zero =>
    intro i s hi h0 h1 h9 h6 hm
    have : i = 7 := by omega
    subst this
    refine ⟨s, ExS.loop_brk (ExS.ite (bc := false) (vc := boolVal false) (EvE_of_eval (n := 4) ?_) rfl ExS.brk), rfl, rfl, h6,
      fun _ _ _ => rfl⟩
    simp [evalExpr, h9, evalBin, isPtr, evalBinInt, binInt, intOf, IntTy.u32, Res.bind]
  | succ d ih =>
    intro i s hi h0 h1 h9 h6 hm
    have hi7 : i < 7 := by omega
    have hcond : EvE Gen.prog s (.bin .lt (some ⟨32, false⟩) (.var 9) (.const (.int ⟨32, false⟩ 7)))
        (boolVal true) := by
      apply EvE_of_eval (n := 4)
      simp [evalExpr, h9, evalBin, isPtr, evalBinInt, binInt, intOf, IntTy.u32, Res.bind, hi7]
    have hbl : hb p c i < 256 := UInt8.toNat_lt _
    have hne := ev_ne0e hbl (ev_hand hi7 h0 h1 h9 hm)
    have hlt := actUpTo_lt p c i
    have h128 : actUpTo p c i < 2 ^ 32 := Nat.lt_of_lt_of_le hlt (Nat.pow_le_pow_right (by decide) (by omega))
    -- the body sets local 6 to the next accumulator
    obtain ⟨s1, eb, hs1m, hs1ro, hs1l6, hs1o⟩ : ∃ s1, ExS Gen.prog s handBody .normal s1 ∧ s1.mem = s.mem ∧
        s1.ro = s.ro ∧ s1.locals 6 = some (.int IntTy.u32 (actUpTo p c (i + 1))) ∧
        ∀ x, x ≠ 6 → s1.locals x = s.locals x := by
      by_cases hz : hb p c i ≠ 0
      · refine ⟨_, ExS.ite (bc := true) hcond rfl (ExS.ite (bc := true) hne (by simp [truthy_boolVal, hz])
          (ExS.set (ev_bor_shl h128 (by omega) h6 h9 (by simp [IntTy.toInt, IntTy.u32])))), rfl, rfl, ?_, ?_⟩
        · simp [Locals.upd, actUpTo, hz]
        · intro x hx; simp [Locals.upd, hx]
      · refine ⟨_, ExS.ite (bc := true) hcond rfl (ExS.ite (bc := false) hne (by simp [truthy_boolVal, hz])
          ExS.skip), rfl, rfl, ?_, fun _ _ => rfl⟩
        simp [actUpTo, hz] at h6 ⊢; exact h6
    let s2 : State := { s1 with locals := s1.locals.upd 9 (.int IntTy.u32 (i + 1)) }
    have es : ExS Gen.prog s1 handStep .normal s2 := by
      apply ExS.set; apply EvE_of_eval (n := 4)
      simp [evalExpr, hs1o 9 (by decide), h9, evalCast, evalBin, isPtr, evalBinInt, binInt, intOf, IntTy.u32,
        IntTy.modulus, Res.bind, IntTy.toInt, Nat.mod_eq_of_lt (show i < 4294967296 by omega),
        Nat.mod_eq_of_lt (show i + 1 < 4294967296 by omega)]
    obtain ⟨s', e', hm', hro', h6', ho'⟩ := ih (i + 1) s2 (by omega)
      (by simp [s2, Locals.upd]; rw [hs1o 0 (by decide)]; exact h0)
      (by simp [s2, Locals.upd]; rw [hs1o 1 (by decide)]; exact h1)
      (by simp [s2, Locals.upd]) (by simp [s2, Locals.upd]; exact hs1l6)
      (by simp [s2]; rw [hs1m]; exact hm)
    refine ⟨s', ExS.loop_next eb (Or.inl rfl) es e', by rw [hm']; simp [s2]; exact hs1m,
      by rw [hro']; simp [s2]; exact hs1ro, h6', fun x a b => ?_⟩
    rw [ho' x a b]; simp [s2, Locals.upd, b]; exact hs1o x a

theorem ev_board_i32 {s : State} {p : Position} {j k : Nat} (hk : k < 81)
    (h0 : s.locals 0 = some posPtr) (hj : s.locals j = some (.int IntTy.i32 k))
    (hm : s.mem posBlock = some (encode p)) :
    EvE Gen.prog s (.load (.int ⟨8, false⟩) (.index (.field (.var 0) 0) (.var j) 1)) (.int IntTy.u8 (bb p k)) := by
  have hlen := encode_length p
  refine EvE.load (pa := .ptr posBlock k) (EvE.index (pb := .ptr posBlock (0 + 0))
    (EvE.field (EvE.var h0) (by simp [ptrAddN, posPtr, hm, hlen])) (EvE.var hj) ?_) ?_
  · simp [IntTy.i32, ptrAdd, hm, hlen, IntTy.toInt, show ¬ (2147483648 ≤ k) by omega]; omega
  · simp only [load, Ty.size, IntTy.bytes, show (8 : Nat) / 8 = 1 by rfl, readBoard hm k hk]
    simp [Res.bind, decodeLE, bb, hk]; rfl

theorem ev_eq_u8 {s : State} {e1 e2 : Expr} {a b : Nat} (ha : a < 256) (hb : b < 256)
    (h1 : EvE Gen.prog s e1 (.int IntTy.u8 a)) (h2 : EvE Gen.prog s e2 (.int IntTy.u8 b)) :
    EvE Gen.prog s (.bin .eq (some ⟨32, true⟩) (.cast ⟨32, true⟩ e1) (.cast ⟨32, true⟩ e2))
      (boolVal (decide (a = b))) := by
  refine EvE.bin (EvE.cast h1 rfl) (EvE.cast h2 rfl) ?_
  simp [evalBin, isPtr, evalBinInt, binInt, intOf, IntTy.u8, evalCast, IntTy.modulus, IntTy.toInt, Res.bind,
    Nat.mod_eq_of_lt (show a < 4294967296 by omega), Nat.mod_eq_of_lt (show b < 4294967296 by omega),
    show ¬ (2147483648 ≤ a) by omega, show ¬ (2147483648 ≤ b) by omega, Int.ofNat_inj]

/-- `pawn_files` after the first `k` squares. -/
def pawnUpTo (p : Position) (K : Nat) : Nat → Nat
  | 0 => 0
  | k + 1 => if bb p k = K then pawnUpTo p K k ||| 2 ^ (k % 9) else pawnUpTo p K k

theorem pawnUpTo_lt (p : Position) (K : Nat) : ∀ k, pawnUpTo p K k < 2 ^ 9 := by
  intro k; induction k with
  | zero => simp [pawnUpTo]
  | succ k ih =>
    simp only [pawnUpTo]; split
    · exact Nat.or_lt_two_pow ih (Nat.pow_lt_pow_right (by decide) (by omega))
    · exact ih

def pawnBody : Stmt := (.ite (.bin .lt (some ⟨32, true⟩) (.var 10) (.const (.int ⟨32, true⟩ 81))) (.ite (.bin .eq (some ⟨32, true⟩) (.cast ⟨32, true⟩ (.load (.int ⟨8, false⟩) (.index (.field (.var 0) 0) (.var 10) 1))) (.cast ⟨32, true⟩ (.var 7))) (.seq (.call (some 11) 8 [(.cast ⟨8, false⟩ (.var 10))]) (.set 5 (.cast ⟨32, false⟩ (.bin .bor (some ⟨32, false⟩) (.cast ⟨32, false⟩ (.var 5)) (.cast ⟨32, false⟩ (.bin .shl (some ⟨32, false⟩) (.const (.int ⟨32, false⟩ 1)) (.var 11))))))) .skip) .brk)
def pawnStep : Stmt := (.set 10 (.cast ⟨32, true⟩ (.bin .add (some ⟨32, true⟩) (.cast ⟨32, true⟩ (.var 10)) (.const (.int ⟨32, true⟩ 1)))))

theorem add_pseudo_drops_loop1_eq : Gen.add_pseudo_drops_loop1 = .loop pawnBody pawnStep := rfl

theorem pawn_loop (p : Position) (K : Nat) (hK : K < 256) :
    ∀ d k (s : State), k + d = 81 → s.locals 0 = some posPtr → s.locals 7 = some (.int IntTy.u8 K) →
      s.locals 10 = some (.int IntTy.i32 k) → s.locals 5 = some (.int IntTy.u32 (pawnUpTo p K k)) →
      s.mem posBlock = some (encode p) →
      ∃ s', ExS Gen.prog s (.loop pawnBody pawnStep) .normal s' ∧ s'.mem = s.mem ∧ s'.ro = s.ro ∧
        s'.locals 5 = some (.int IntTy.u32 (pawnUpTo p K 81)) ∧
        ∀ x, x ≠ 5 → x ≠ 10 → x ≠ 11 → s'.locals x = s.locals x := by
  intro d
  induction d with
  | zero =>
    intro k s hk h0 h7 h10 h5 hm
    have : k = 81 := by omega
    subst this
    refine ⟨s, ExS.loop_brk (ExS.ite (bc := false) (vc := boolVal false) (EvE_of_eval (n := 4) ?_) rfl ExS.brk),
      rfl, rfl, h5, fun _ _ _ _ => rfl⟩
    simp [evalExpr, h10, evalBin, isPtr, evalBinInt, binInt, intOf, IntTy.i32, Res.bind, IntTy.toInt]
  | succ d ih =>
    intro k s hk h0 h7 h10 h5 hm
    have hk81 : k < 81 := by omega
    have hcond : EvE Gen.prog s (.bin .lt (some ⟨32, true⟩) (.var 10) (.const (.int ⟨32, true⟩ 81)))
        (boolVal true) := by
      apply EvE_of_eval (n := 4)
      simp [evalExpr, h10, evalBin, isPtr, evalBinInt, binInt, intOf, IntTy.i32, Res.bind, IntTy.toInt,
        show ¬ (2147483648 ≤ k) by omega, show (k : Int) < 81 by omega]
    have hbl : bb p k < 256 := bb_lt p k
    have heq := ev_eq_u8 hbl hK (ev_board_i32 hk81 h0 h10 hm) (EvE.var h7)
    have hlt := pawnUpTo_lt p K k
    have h32 : pawnUpTo p K k < 2 ^ 32 := Nat.lt_of_lt_of_le hlt (Nat.pow_le_pow_right (by decide) (by omega))
    obtain ⟨s1, eb, hs1m, hs1ro, hs1l5, hs1o⟩ : ∃ s1, ExS Gen.prog s pawnBody .normal s1 ∧ s1.mem = s.mem ∧
        s1.ro = s.ro ∧ s1.locals 5 = some (.int IntTy.u32 (pawnUpTo p K (k + 1))) ∧
        ∀ x, x ≠ 5 → x ≠ 11 → s1.locals x = s.locals x := by
      by_cases hz : bb p k = K
      · have hcol : run Gen.fid_col_of [u8 k] = some (some (i32 ((k % 9 : Nat) : Int))) :=
          col_of_refines ⟨k, hk81⟩
        have hcast : EvE Gen.prog s (.cast ⟨8, false⟩ (.var 10)) (u8 k) :=
          EvE.cast (EvE.var h10) (by simp [evalCast, IntTy.i32, IntTy.toInt, IntTy.wrap, IntTy.modulus, u8,
            IntTy.u8, show ¬ (2147483648 ≤ k) by omega]; omega)
        let sA : State := { s with locals := s.locals.upd 11 (i32 ((k % 9 : Nat) : Int)) }
        have ec := call_pure (s := s) (d := 11) rfl rfl rfl rfl hcol (EvArgs.cons hcast EvArgs.nil)
        refine ⟨_, ExS.ite (bc := true) hcond rfl (ExS.ite (bc := true) heq (by simp [truthy_boolVal, hz])
          (ExS.seq ec (ExS.set (ev_bor_shl (s := sA) h32 (show k % 9 < 32 by omega)
            (by simp [sA, Locals.upd]; exact h5)
            (ti := IntTy.i32) (by simp only [sA, Locals.upd, if_true]; rw [i32_nat (k % 9) (by omega)])
            (by simp [IntTy.toInt, IntTy.i32]; omega))))),
          rfl, rfl, ?_, ?_⟩
        · simp [Locals.upd, pawnUpTo, hz]
        · intro x a b; simp [Locals.upd, a, b, sA]
      · refine ⟨_, ExS.ite (bc := true) hcond rfl (ExS.ite (bc := false) heq (by simp [truthy_boolVal, hz])
          ExS.skip), rfl, rfl, ?_, fun _ _ _ => rfl⟩
        simp [pawnUpTo, hz]; exact h5
    let s2 : State := { s1 with locals := s1.locals.upd 10 (.int IntTy.i32 (k + 1)) }
    have hv : s1.locals 10 = some (i32 (k : Int)) := by
      rw [hs1o 10 (by decide) (by decide), h10, i32_nat k (by omega)]
    have es : ExS Gen.prog s1 pawnStep .normal s2 := by
      have := ExS.set (p := Gen.prog) (i := 10) (s := s1) (EvE.cast (EvE.bin (EvE.cast (EvE.var hv) (cast_i32 k (by omega) (by omega)))
        (EvE.const (.int ⟨32, true⟩ 1)) (add_i32 (k : Int) 1 (by omega) (by omega) (by omega) (by omega) (by omega)
          (by omega))) (cast_i32 _ (by omega) (by omega)))
      rw [show ((k : Int) + 1) = ((k + 1 : Nat) : Int) by omega, i32_nat (k + 1) (by omega)] at this
      exact this
    obtain ⟨s', e', hm', hro', h5', ho'⟩ := ih (k + 1) s2 (by omega)
      (by simp [s2, Locals.upd]; rw [hs1o 0 (by decide) (by decide)]; exact h0)
      (by simp [s2, Locals.upd]; rw [hs1o 7 (by decide) (by decide)]; exact h7)
      (by simp [s2, Locals.upd]) (by simp [s2, Locals.upd]; exact hs1l5)
      (by simp [s2]; rw [hs1m]; exact hm)
    refine ⟨s', ExS.loop_next eb (Or.inl rfl) es e', by rw [hm']; simp [s2]; exact hs1m,
      by rw [hro']; simp [s2]; exact hs1ro, h5', fun x a b c => ?_⟩
    rw [ho' x a b c]; simp [s2, Locals.upd, b]; exact hs1o x a c

/-- The 5 bytes of a drop `{SHOGI_SQ_NONE, to, 0, 0, hand + 1}`. -/
def dmBytes (to h : Nat) : List UInt8 := [255, to.toUInt8, 0, 0, (h + 1).toUInt8]

def demitStmt : Stmt :=
  .seq (.alloc 18 5) (.seq (.store (.int ⟨8, false⟩) (.field (.var 18) 0) (.cast ⟨8, false⟩ (.const (.int ⟨32, true⟩ 255))))
    (.seq (.store (.int ⟨8, false⟩) (.field (.var 18) 1) (.var 14))
    (.seq (.store (.int ⟨8, false⟩) (.field (.var 18) 2) (.cast ⟨8, false⟩ (.const (.int ⟨32, true⟩ 0))))
    (.seq (.store (.int ⟨8, false⟩) (.field (.var 18) 3) (.cast ⟨8, false⟩ (.const (.int ⟨32, true⟩ 0))))
    (.seq (.store (.int ⟨8, false⟩) (.field (.var 18) 4) (.cast ⟨8, false⟩ (.bin .add (some ⟨32, false⟩) (.var 17)
      (.const (.int ⟨32, false⟩ 1)))))
      (.call none 22 [(.var 2), (.var 3), (.var 4), (.var 18)]))))))

theorem demit_spec {s : State} {to h mb mo cb co cap n : Nat} {L : List (List UInt8)}
    (h14 : s.locals 14 = some (.int IntTy.u8 to)) (h17 : s.locals 17 = some (.int IntTy.u32 h))
    (h2 : s.locals 2 = some (.ptr mb mo)) (h3 : s.locals 3 = some (.ptr cb co))
    (h4 : s.locals 4 = some (.int IntTy.u64 cap)) (hro : s.ro = false)
    (hto : to < 256) (hh : h < 32) (hbuf : Buf s.mem mb mo cb co cap L) (hf : Fresh s.mem n)
    (h64 : n + 2 < 2 ^ 64) :
    ∃ s', ExS Gen.prog s demitStmt .normal s' ∧ s'.locals = s.locals.upd 18 (.ptr n 0) ∧ s'.ro = s.ro ∧
      Buf s'.mem mb mo cb co cap (L ++ [dmBytes to h]) ∧ Fresh s'.mem (n + 1 + 1) ∧
      Frame s.mem s'.mem mb cb := by
  have hmbn : mb ≠ n := fun e => by
    obtain ⟨blk, hb, _⟩ := hbuf.buf; rw [e, hf.2.2 n (Nat.le_refl _)] at hb; cases hb
  have hcbn : cb ≠ n := fun e => by
    obtain ⟨blk, hb, _⟩ := hbuf.cnt; rw [e, hf.2.2 n (Nat.le_refl _)] at hb; cases hb
  let m1 := (s.mem.upd 0 (encodeLE 8 (n + 1))).upd n (List.replicate 5 0)
  let s1 : State := { s with mem := m1, locals := s.locals.upd 18 (.ptr n 0) }
  have ha : ExS Gen.prog s (.alloc 18 5) .normal s1 := exec_alloc (hf.allocAt (by omega)) 18 5
  have hj' : ∀ x, x ≠ 18 → s1.locals x = s.locals x := fun x hx => by simp [s1, Locals.upd, hx]
  have hjj : s1.locals 18 = some (.ptr n 0) := by simp [s1, Locals.upd]
  have hm1n : m1 n = some (List.replicate 5 0) := Mem.upd_eq
  have hm1o : ∀ x, x ≠ 0 → x ≠ n → m1 x = s.mem x := fun x a b => by
    simp only [m1]; rw [Mem.upd_ne b, Mem.upd_ne a]
  let m2 := m1.write n (0 + 0) (encodeLE 1 255)
  let m3 := m2.write n (0 + 1) (encodeLE 1 to)
  let m4 := m3.write n (0 + 2) (encodeLE 1 0)
  let m5 := m4.write n (0 + 3) (encodeLE 1 0)
  let m6 := m5.write n (0 + 4) (encodeLE 1 (h + 1))
  have hm2n : m2 n = some [255, 0, 0, 0, 0] := by simp only [m2]; rw [Mem.write_eq hm1n]; simp [encodeLE]
  have hm3n : m3 n = some [255, to.toUInt8, 0, 0, 0] := by
    simp only [m3]; rw [Mem.write_eq hm2n]; simp [encodeLE, Nat.mod_eq_of_lt hto]
  have hm4n : m4 n = some [255, to.toUInt8, 0, 0, 0] := by
    simp only [m4]; rw [Mem.write_eq hm3n]; simp [encodeLE]
  have hm5n : m5 n = some [255, to.toUInt8, 0, 0, 0] := by
    simp only [m5]; rw [Mem.write_eq hm4n]; simp [encodeLE]
  have hm6n : m6 n = some (dmBytes to h) := by
    simp only [m6]; rw [Mem.write_eq hm5n]; simp [encodeLE, dmBytes, Nat.mod_eq_of_lt (show h + 1 < 256 by omega)]
  have hmo : ∀ x, x ≠ n → m6 x = m1 x := fun x hx => by
    simp only [m6, m5, m4, m3, m2]; rw [Mem.write_ne hx, Mem.write_ne hx, Mem.write_ne hx,
      Mem.write_ne hx, Mem.write_ne hx]
  let s2 : State := { s1 with mem := m2 }
  let s3 : State := { s1 with mem := m3 }
  let s4 : State := { s1 with mem := m4 }
  let s5 : State := { s1 with mem := m5 }
  let s6 : State := { s1 with mem := m6 }
  have st0 : ExS Gen.prog s1 (.store (.int ⟨8, false⟩) (.field (.var 18) 0) (.cast ⟨8, false⟩
      (.const (.int ⟨32, true⟩ 255)))) .normal s2 :=
    store_u8_field hjj hm1n (by simp) (EvE_of_eval (n := 2) rfl) hro
  have st1 : ExS Gen.prog s2 (.store (.int ⟨8, false⟩) (.field (.var 18) 1) (.var 14)) .normal s3 :=
    store_u8_field (s := s2) hjj hm2n (by simp) (EvE.var (by rw [hj' 14 (by decide)]; exact h14)) hro
  have st2 : ExS Gen.prog s3 (.store (.int ⟨8, false⟩) (.field (.var 18) 2) (.cast ⟨8, false⟩
      (.const (.int ⟨32, true⟩ 0)))) .normal s4 :=
    store_u8_field (s := s3) hjj hm3n (by simp) (EvE_of_eval (n := 2) rfl) hro
  have st3 : ExS Gen.prog s4 (.store (.int ⟨8, false⟩) (.field (.var 18) 3) (.cast ⟨8, false⟩
      (.const (.int ⟨32, true⟩ 0)))) .normal s5 :=
    store_u8_field (s := s4) hjj hm4n (by simp) (EvE_of_eval (n := 2) rfl) hro
  have st4 : ExS Gen.prog s5 (.store (.int ⟨8, false⟩) (.field (.var 18) 4) (.cast ⟨8, false⟩
      (.bin .add (some ⟨32, false⟩) (.var 17) (.const (.int ⟨32, false⟩ 1))))) .normal s6 := by
    refine store_u8_field (s := s5) hjj hm5n (by simp) ?_ hro
    have h17' : s5.locals 17 = some (.int IntTy.u32 h) := by rw [hj' 17 (by decide)]; exact h17
    apply EvE_of_eval (n := 4)
    simp [evalExpr, h17', evalCast, evalBin, isPtr, evalBinInt, binInt, intOf, IntTy.u32, IntTy.modulus,
      Res.bind, IntTy.u8, Nat.mod_eq_of_lt (show h + 1 < 4294967296 by omega),
      Nat.mod_eq_of_lt (show h + 1 < 256 by omega)]
  have hbuf6 : Buf m6 mb mo cb co cap L := hbuf.frame
    (by rw [hmo mb hmbn, hm1o mb hbuf.mb0 hmbn]) (by rw [hmo cb hcbn, hm1o cb hbuf.cb0 hcbn])
  have hf6 : Fresh m6 (n + 1) := by
    have := hf.after_alloc (List.replicate 5 0)
    exact ((((this.write hf.2.1).write hf.2.1).write hf.2.1).write hf.2.1).write hf.2.1
  have hrd : readBytes m6 n 0 5 = .ok (dmBytes to h) := by simp [readBytes, hm6n, dmBytes]
  obtain ⟨sA, hA, hbA, hfA, hfrA⟩ := add_move_spec hbuf6 hrd hf6 (by omega) hf.2.1
  have hcall : ExS Gen.prog s6 (.call none 22 [(.var 2), (.var 3), (.var 4), (.var 18)]) .normal
      { s6 with mem := sA.mem } := by
    refine ExS.call (vs := [.ptr mb mo, .ptr cb co, .int IntTy.u64 cap, .ptr n 0]) ?_ rfl rfl ?_ (Or.inl rfl)
    · refine EvArgs.cons (EvE.var ?_) (EvArgs.cons (EvE.var ?_) (EvArgs.cons (EvE.var ?_)
        (EvArgs.cons (EvE.var hjj) EvArgs.nil)))
      · show s1.locals 2 = _; rw [hj' 2 (by decide)]; exact h2
      · show s1.locals 3 = _; rw [hj' 3 (by decide)]; exact h3
      · show s1.locals 4 = _; rw [hj' 4 (by decide)]; exact h4
    · rw [hro]; exact hA
  refine ⟨{ s6 with mem := sA.mem }, ExS.seq ha (ExS.seq st0 (ExS.seq st1 (ExS.seq st2 (ExS.seq st3
    (ExS.seq st4 hcall))))), rfl, rfl, hbA, hfA, ?_⟩
  intro x a b c d
  have hxn : x ≠ n := fun e => by subst e; exact d (hf.2.2 _ (Nat.le_refl _))
  show sA.mem x = s.mem x
  rw [hfrA x a b c (by rw [hmo x hxn, hm1o x a hxn]; exact d), hmo x hxn, hm1o x a hxn]

def bitsDone : Nat → Nat → Bool
  | 0, a => a == 0
  | k + 1, a => a == 0 || bitsDone k (a &&& (a - 1))

set_option maxRecDepth 100000 in
theorem bits_done : ∀ a : Fin 128, bitsDone 8 a.val = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem ctz_small : ∀ a : Fin 128, a.val ≠ 0 → ctzNat 32 a.val < 7 := by decide +kernel

def bitBody : Stmt := .ite (.bin .ne (some ⟨32, false⟩) (.var 16) (.const (.int ⟨32, false⟩ 0)))
  (.seq (.set 17 (.cast ⟨32, false⟩ (.un .ctz ⟨32, false⟩ (.var 16))))
    (.seq (.set 16 (.cast ⟨32, false⟩ (.bin .band (some ⟨32, false⟩) (.cast ⟨32, false⟩ (.var 16))
      (.cast ⟨32, false⟩ (.bin .sub (some ⟨32, false⟩) (.var 16) (.const (.int ⟨32, false⟩ 1)))))))
      demitStmt)) .brk

theorem add_pseudo_drops_loop2_eq : Gen.add_pseudo_drops_loop2 = .loop bitBody .skip := rfl

theorem bit_loop {to mb mo cb co cap : Nat} (hto : to < 256) :
    ∀ k a (s : State) (L : List (List UInt8)) n, a < 128 → bitsDone k a = true →
      s.locals 14 = some (.int IntTy.u8 to) → s.locals 16 = some (.int IntTy.u32 a) →
      s.locals 2 = some (.ptr mb mo) → s.locals 3 = some (.ptr cb co) →
      s.locals 4 = some (.int IntTy.u64 cap) → s.ro = false →
      Buf s.mem mb mo cb co cap L → Fresh s.mem n → n + 2 * k < 2 ^ 64 →
      ∃ s', ExS Gen.prog s (.loop bitBody .skip) .normal s' ∧
        Buf s'.mem mb mo cb co cap (L ++ (dropBits k a).map (dmBytes to)) ∧
        Fresh s'.mem (n + 2 * (dropBits k a).length) ∧ Frame s.mem s'.mem mb cb ∧ s'.ro = false ∧
        ∀ x, x ≠ 16 → x ≠ 17 → x ≠ 18 → s'.locals x = s.locals x := by
  intro k
  induction k with
  | zero =>
    intro a s L n ha hd h14 h16 h2 h3 h4 hro hb hf _
    have : a = 0 := by simpa [bitsDone] using hd
    subst this
    refine ⟨s, ExS.loop_brk (ExS.ite (bc := false) (vc := boolVal false) (EvE_of_eval (n := 4) ?_) rfl ExS.brk),
      by simpa [dropBits] using hb, by simpa [dropBits] using hf, Frame.refl _ _ _, hro, fun _ _ _ _ => rfl⟩
    simp [evalExpr, h16, evalBin, isPtr, evalBinInt, binInt, intOf, IntTy.u32, Res.bind]
  | succ k ih =>
    intro a s L n ha hd h14 h16 h2 h3 h4 hro hb hf h64
    by_cases ha0 : a = 0
    · subst ha0
      refine ⟨s, ExS.loop_brk (ExS.ite (bc := false) (vc := boolVal false) (EvE_of_eval (n := 4) ?_) rfl ExS.brk),
        by simpa [dropBits] using hb, by simpa [dropBits] using hf, Frame.refl _ _ _, hro, fun _ _ _ _ => rfl⟩
      simp [evalExpr, h16, evalBin, isPtr, evalBinInt, binInt, intOf, IntTy.u32, Res.bind]
    have hct := ctz_small ⟨a, ha⟩ ha0
    simp only at hct
    have hd' : bitsDone k (a &&& (a - 1)) = true := by simpa [bitsDone, ha0] using hd
    have ha' : a &&& (a - 1) < 128 := Nat.lt_of_le_of_lt Nat.and_le_left ha
    let s1 : State := { s with locals := s.locals.upd 17 (.int IntTy.u32 (ctzNat 32 a)) }
    let s2 : State := { s1 with locals := s1.locals.upd 16 (.int IntTy.u32 (a &&& (a - 1))) }
    have e1 : ExS Gen.prog s (.set 17 (.cast ⟨32, false⟩ (.un .ctz ⟨32, false⟩ (.var 16)))) .normal s1 := by
      apply ExS.set; apply EvE_of_eval (n := 4)
      simp [evalExpr, h16, evalUn, evalCast, intOf, IntTy.u32, Res.bind, ha0, IntTy.i32, IntTy.toInt,
        IntTy.wrap, IntTy.modulus, show ¬ (2147483648 ≤ ctzNat 32 a) by omega]
      omega
    have e2 : ExS Gen.prog s1 (.set 16 (.cast ⟨32, false⟩ (.bin .band (some ⟨32, false⟩) (.cast ⟨32, false⟩ (.var 16))
        (.cast ⟨32, false⟩ (.bin .sub (some ⟨32, false⟩) (.var 16) (.const (.int ⟨32, false⟩ 1))))))) .normal s2 := by
      apply ExS.set; apply EvE_of_eval (n := 5)
      have h16' : s1.locals 16 = some (.int IntTy.u32 a) := by simp [s1, Locals.upd]; exact h16
      have m1 : a % 4294967296 = a := Nat.mod_eq_of_lt (by omega)
      have m2 : (a - 1) % 4294967296 = a - 1 := Nat.mod_eq_of_lt (by omega)
      have m3 : (a &&& (a - 1)) % 4294967296 = a &&& (a - 1) :=
        Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt Nat.and_le_left (by omega))
      have h1a : 1 ≤ a := by omega
      simp only [evalExpr, h16', evalCast, evalBin, isPtr, evalBinInt, binInt, intOf, IntTy.u32, IntTy.modulus,
        Res.bind, h1a, if_true, Bool.false_and, Bool.false_eq_true, ite_false, show 2 ^ 32 = 4294967296 from rfl,
        m1, m2, m3, Res.bind_eq, Res.bind_ok, pure, ite_true, Bool.and_self]
    obtain ⟨s3, e3, hl3, hro3, hb3, hf3, hfr3⟩ := demit_spec (s := s2) (h := ctzNat 32 a)
      (by simp [s2, s1, Locals.upd]; exact h14) (by simp [s2, s1, Locals.upd])
      (by simp [s2, s1, Locals.upd]; exact h2) (by simp [s2, s1, Locals.upd]; exact h3)
      (by simp [s2, s1, Locals.upd]; exact h4) hro hto (by omega) hb hf (by omega)
    have hcond : EvE Gen.prog s (.bin .ne (some ⟨32, false⟩) (.var 16) (.const (.int ⟨32, false⟩ 0)))
        (boolVal true) := by
      apply EvE_of_eval (n := 4)
      simp [evalExpr, h16, evalBin, isPtr, evalBinInt, binInt, intOf, IntTy.u32, Res.bind, ha0]
    obtain ⟨s', e', hb', hf', hfr', hro', hl'⟩ := ih (a &&& (a - 1)) s3 _ _ ha' hd'
      (by rw [hl3]; simp [s2, s1, Locals.upd]; exact h14) (by rw [hl3]; simp [s2, s1, Locals.upd])
      (by rw [hl3]; simp [s2, s1, Locals.upd]; exact h2) (by rw [hl3]; simp [s2, s1, Locals.upd]; exact h3)
      (by rw [hl3]; simp [s2, s1, Locals.upd]; exact h4) (by rw [hro3]; exact hro) hb3 hf3 (by omega)
    have hout : dropBits (k + 1) a = ctzNat 32 a :: dropBits k (a &&& (a - 1)) := by simp [dropBits, ha0]
    refine ⟨s', ExS.loop_next (ExS.ite (bc := true) hcond rfl (ExS.seq e1 (ExS.seq e2 e3))) (Or.inl rfl)
      ExS.skip e', ?_, ?_, Frame.trans hfr3 hfr', hro', ?_⟩
    · rw [hout]; simpa using hb'
    · rw [hout]; simp only [List.length_cons]
      rw [show n + 2 * ((dropBits k (a &&& (a - 1))).length + 1) = n + 1 + 1 + 2 * (dropBits k (a &&& (a - 1))).length
        by omega]; exact hf'
    · intro x a1 a2 a3; rw [hl' x a1 a2 a3, hl3]; simp [s2, s1, Locals.upd, a1, a2, a3]

end Shogi.C.Proofs
