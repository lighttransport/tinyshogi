/-
  R3: `same_move` (fid 32) refines byte comparison of the four rule-relevant
  fields of two `ShogiMove` structs. The C copies both structs into fresh
  blocks (so argument aliasing is irrelevant) and compares fields 0 (from),
  1 (to), 3 (promote), 4 (drop).
-/
import Shogi.C.Proofs.InCheck
import Shogi.C.Proofs.EntryPoints

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

namespace Shogi.C.Proofs
variable {posBlock : Nat}
open MiniC Shogi Shogi.C

/-- Comparison of the four fields of two 5-byte move blobs. -/
def moveFieldsEq (A B : List UInt8) : Bool :=
  A.getD 0 0 == B.getD 0 0 && A.getD 1 0 == B.getD 1 0 &&
  A.getD 3 0 == B.getD 3 0 && A.getD 4 0 == B.getD 4 0

/-- The u8 value the C returns for a boolean. -/
def u8bool (b : Bool) : Val := .int IntTy.u8 (if b then 1 else 0)

/-- A list of length at least 5 decomposes into its first five elements. -/
theorem list5 (l : List UInt8) (hl : 5 ≤ l.length) :
    ∃ (a0 a1 a2 a3 a4 : UInt8) (r : List UInt8), l = a0 :: a1 :: a2 :: a3 :: a4 :: r := by
  cases l with
  | nil => simp at hl
  | cons a0 l1 =>
    cases l1 with
    | nil => simp at hl
    | cons a1 l2 =>
      cases l2 with
      | nil => simp at hl
      | cons a2 l3 =>
        cases l3 with
        | nil => simp at hl
        | cons a3 l4 =>
          cases l4 with
          | nil => simp at hl
          | cons a4 l5 =>
            exact ⟨a0, a1, a2, a3, a4, l5, rfl⟩

theorem same_move_spec {m : Mem} {pa pb n : Nat} {A B : Block}
    (hpa : m pa = some A) (hpb : m pb = some B)
    (hlA : 5 ≤ A.length) (hlB : 5 ≤ B.length)
    (hf : Fresh m n) (hn64 : n + 2 < 2 ^ 64)
    (hpa0 : pa ≠ 0) (hpb0 : pb ≠ 0) :
    ∃ s', ExS Gen.prog ⟨frameLocals Gen.same_move.params
        [.ptr pa 0, .ptr pb 0], m, false⟩ Gen.same_move.body
      (.ret (some (u8bool (moveFieldsEq A B)))) s' ∧
      (∀ x, x ≠ 0 → x ≠ n → x ≠ n + 1 → m x ≠ none → s'.mem x = m x) := by
  have hnempty : m n = none := hf.2.2 n (Nat.le_refl n)
  have hpan : pa ≠ n := by intro h; subst h; rw [hnempty] at hpa; cases hpa
  have hpbn : pb ≠ n := by intro h; subst h; rw [hnempty] at hpb; cases hpb
  let L0 := frameLocals Gen.same_move.params [.ptr pa 0, .ptr pb 0]
  let s0 : State := ⟨L0, m, false⟩
  -- set 2 = var 0
  let s1 : State := { s0 with locals := s0.locals.upd 2 (.ptr pa 0) }
  have e1 : ExS Gen.prog s0 (.set 2 (.var 0)) .normal s1 := ExS.set (EvE.var rfl)
  -- alloc 0 5
  let m1 : Mem := (m.upd 0 (encodeLE 8 (n + 1))).upd n (List.replicate 5 0)
  let s2 : State := { s1 with mem := m1, locals := s1.locals.upd 0 (.ptr n 0) }
  have e2 : ExS Gen.prog s1 (.alloc 0 5) .normal s2 := by
    simpa [s2, m1] using exec_alloc (s := s1) (hf.allocAt (by omega)) 0 5
  have hm1n : m1 n = some (List.replicate 5 0) := Mem.upd_eq
  have hm1o : ∀ x, x ≠ 0 → x ≠ n → m1 x = m x := by
    intro x hx0 hxn
    simp only [m1]
    rw [Mem.upd_ne hxn, Mem.upd_ne hx0]
  -- memcpy fresh(n) <- pa
  have hsrcA : readBytes m1 pa 0 5 = .ok (A.take 5) := by
    simp only [readBytes, hm1o pa hpa0 hpan, hpa]
    simp [hlA]
  let m2 : Mem := m1.write n 0 (A.take 5)
  have e3 : ExS Gen.prog s2 (.memcpy (.var 0) (.var 2) (.const (.int ⟨64, false⟩ 5))) .normal
      { s2 with mem := m2 } := by
    refine ExS.memcpy (s := s2) (EvE.var rfl) (EvE.var rfl) (EvE.const _) rfl
      (by simp [Ne.symm hpan]) hsrcA (writeBytes_ok hm1n (by simp [hlA]))
  have hm2o : ∀ x, x ≠ 0 → x ≠ n → m2 x = m x := by
    intro x hx0 hxn
    simp only [m2]
    rw [Mem.write_ne hxn]
    exact hm1o x hx0 hxn
  have hm2n : m2 n = some (A.take 5) := by
    simp only [m2]
    rw [Mem.write_eq hm1n]
    simp [hlA]
  have hf2 : Fresh m2 (n + 1) := by
    simpa [m2, m1] using (hf.after_alloc (List.replicate 5 0)).write (b := n) (o := 0) (bs := A.take 5) hf.2.1
  -- set 3 = var 1
  let s3 : State := { s2 with mem := m2, locals := s2.locals.upd 3 (.ptr pb 0) }
  have e4 : ExS Gen.prog { s2 with mem := m2 } (.set 3 (.var 1)) .normal s3 := by
    simpa [s3] using ExS.set (s := { s2 with mem := m2 }) (EvE.var rfl)
  -- alloc 1 5
  let m3 : Mem := (m2.upd 0 (encodeLE 8 (n + 2))).upd (n + 1) (List.replicate 5 0)
  let s4 : State := { s3 with mem := m3, locals := s3.locals.upd 1 (.ptr (n + 1) 0) }
  have e5 : ExS Gen.prog s3 (.alloc 1 5) .normal s4 := by
    simpa [s4, m3] using exec_alloc (s := s3) (hf2.allocAt (by omega)) 1 5
  have hm3nn : m3 (n + 1) = some (List.replicate 5 0) := Mem.upd_eq
  have hm3o : ∀ x, x ≠ 0 → x ≠ n + 1 → m3 x = m2 x := by
    intro x hx0 hxnn
    simp only [m3]
    rw [Mem.upd_ne hxnn, Mem.upd_ne hx0]
  have hpbn1 : pb ≠ n + 1 := by
    intro h; subst h
    have hmn1 : m (n + 1) = none := by
      rw [← hm2o (n + 1) (by omega) (by omega)]
      exact hf2.2.2 (n + 1) (Nat.le_refl _)
    rw [hmn1] at hpb; cases hpb
  have hsrcB : readBytes m3 pb 0 5 = .ok (B.take 5) := by
    simp only [readBytes, hm3o pb hpb0 hpbn1, hm2o pb hpb0 hpbn, hpb]
    simp [hlB]
  let m4 : Mem := m3.write (n + 1) 0 (B.take 5)
  have e6 : ExS Gen.prog s4 (.memcpy (.var 1) (.var 3) (.const (.int ⟨64, false⟩ 5))) .normal
      { s4 with mem := m4 } := by
    refine ExS.memcpy (s := s4) (EvE.var rfl) (EvE.var rfl) (EvE.const _) rfl
      (by
        have hnpb : n + 1 ≠ pb := fun h => hpbn1 h.symm
        simp [hnpb]) hsrcB (writeBytes_ok hm3nn (by simp [hlB]))
  have hm4nn : m4 (n + 1) = some (B.take 5) := by
    simp only [m4]
    rw [Mem.write_eq hm3nn]
    simp [hlB]
  have hm4n : m4 n = some (A.take 5) := by
    simp only [m4]
    rw [Mem.write_ne (by omega)]
    rw [hm3o n hf.2.1 (by omega : n ≠ n + 1)]
    exact hm2n
  have hm4o : ∀ x, x ≠ 0 → x ≠ n → x ≠ n + 1 → m4 x = m x := by
    intro x hx0 hxn hxnn
    simp only [m4]
    rw [Mem.write_ne hxnn]
    rw [hm3o x hx0 hxnn]
    exact hm2o x hx0 hxn
  -- the final comparison expression
  let s6 : State := { s4 with mem := m4 }
  let expr : Expr := (.cast ⟨8, false⟩ (.bin .ne (some ⟨32, true⟩)
    (.land (.land (.land
      (.bin .eq (some ⟨32, true⟩) (.cast ⟨32, true⟩ (.load (.int ⟨8, false⟩) (.field (.var 0) 0)))
        (.cast ⟨32, true⟩ (.load (.int ⟨8, false⟩) (.field (.var 1) 0))))
      (.bin .eq (some ⟨32, true⟩) (.cast ⟨32, true⟩ (.load (.int ⟨8, false⟩) (.field (.var 0) 1)))
        (.cast ⟨32, true⟩ (.load (.int ⟨8, false⟩) (.field (.var 1) 1)))))
      (.bin .eq (some ⟨32, true⟩) (.cast ⟨32, true⟩ (.load (.int ⟨8, false⟩) (.field (.var 0) 3)))
        (.cast ⟨32, true⟩ (.load (.int ⟨8, false⟩) (.field (.var 1) 3)))))
      (.bin .eq (some ⟨32, true⟩) (.cast ⟨32, true⟩ (.load (.int ⟨8, false⟩) (.field (.var 0) 4)))
        (.cast ⟨32, true⟩ (.load (.int ⟨8, false⟩) (.field (.var 1) 4)))))
    (.const (.int ⟨32, true⟩ 0))))
  -- Decompose A and B so the byte reads reduce concretely.
  obtain ⟨a0, a1, a2, a3, a4, rA, rfl⟩ := list5 A hlA
  obtain ⟨b0, b1, b2, b3, b4, rB, rfl⟩ := list5 B hlB
  have hexpr : evalExpr Gen.prog 60 s6 expr = .ok (u8bool (moveFieldsEq
      (a0 :: a1 :: a2 :: a3 :: a4 :: rA) (b0 :: b1 :: b2 :: b3 :: b4 :: rB))) := by
    simp only [expr, u8bool, moveFieldsEq]
    dsimp [s6, s4, s3, s2, s1, s0, L0]
    have ha0 : (¬ (2147483648 : Nat) ≤ a0.toNat) := by
      have hlt := UInt8.toNat_lt a0
      omega
    have ha1 : (¬ (2147483648 : Nat) ≤ a1.toNat) := by
      have hlt := UInt8.toNat_lt a1
      omega
    have ha3 : (¬ (2147483648 : Nat) ≤ a3.toNat) := by
      have hlt := UInt8.toNat_lt a3
      omega
    have ha4 : (¬ (2147483648 : Nat) ≤ a4.toNat) := by
      have hlt := UInt8.toNat_lt a4
      omega
    have hb0 : (¬ (2147483648 : Nat) ≤ b0.toNat) := by
      have hlt := UInt8.toNat_lt b0
      omega
    have hb1 : (¬ (2147483648 : Nat) ≤ b1.toNat) := by
      have hlt := UInt8.toNat_lt b1
      omega
    have hb3 : (¬ (2147483648 : Nat) ≤ b3.toNat) := by
      have hlt := UInt8.toNat_lt b3
      omega
    have hb4 : (¬ (2147483648 : Nat) ≤ b4.toNat) := by
      have hlt := UInt8.toNat_lt b4
      omega
    have h0to : ((↑a0.toNat : Int) = ↑b0.toNat ↔ a0 = b0) := by
      constructor
      · intro h
        have hn : a0.toNat = b0.toNat := by omega
        rw [← UInt8.ofNat_toNat (x := a0), ← UInt8.ofNat_toNat (x := b0), hn]
      · intro h; subst h; rfl
    have h1to : ((↑a1.toNat : Int) = ↑b1.toNat ↔ a1 = b1) := by
      constructor
      · intro h
        have hn : a1.toNat = b1.toNat := by omega
        rw [← UInt8.ofNat_toNat (x := a1), ← UInt8.ofNat_toNat (x := b1), hn]
      · intro h; subst h; rfl
    have h3to : ((↑a3.toNat : Int) = ↑b3.toNat ↔ a3 = b3) := by
      constructor
      · intro h
        have hn : a3.toNat = b3.toNat := by omega
        rw [← UInt8.ofNat_toNat (x := a3), ← UInt8.ofNat_toNat (x := b3), hn]
      · intro h; subst h; rfl
    have h4to : ((↑a4.toNat : Int) = ↑b4.toNat ↔ a4 = b4) := by
      constructor
      · intro h
        have hn : a4.toNat = b4.toNat := by omega
        rw [← UInt8.ofNat_toNat (x := a4), ← UInt8.ofNat_toNat (x := b4), hn]
      · intro h; subst h; rfl
    by_cases h0 : a0 = b0 <;> by_cases h1 : a1 = b1 <;>
      by_cases h3 : a3 = b3 <;> by_cases h4 : a4 = b4 <;>
      simp [evalExpr, evalBin, evalBinInt, evalCast, evalUn, isPtr, intOf, IntTy.toInt, IntTy.wrap,
        IntTy.modulus, boolVal, IntTy.u8, IntTy.i32, Res.bind, truthy, ptrAddN, load, Ty.size,
        IntTy.bytes, readBytes, hm4n, hm4nn, hlA, hlB, binInt, decodeLE, ha0, ha1, ha3, ha4,
        hb0, hb1, hb3, hb4, h0to, h1to, h3to, h4to, h0, h1, h3, h4, Locals.upd, frameLocals]
  have eret : ExS Gen.prog s6 (.ret (some expr)) (.ret (some (u8bool (moveFieldsEq
      (a0 :: a1 :: a2 :: a3 :: a4 :: rA) (b0 :: b1 :: b2 :: b3 :: b4 :: rB))))) s6 :=
    ExS.ret (EvE_of_eval hexpr)
  refine ⟨s6, ?_, ?_⟩
  · exact ExS.seq e1 (ExS.seq e2 (ExS.seq e3 (ExS.seq e4 (ExS.seq e5 (ExS.seq e6 eret)))))
  · intro x hx0 hxn hxnn hmx
    exact hm4o x hx0 hxn hxnn

end Shogi.C.Proofs
