import Shogi.C.Proofs.ValidateMaterial
set_option maxHeartbeats 8000000
set_option linter.unusedSimpArgs false
set_option maxRecDepth 100000
namespace Shogi.C.Proofs
open MiniC Shogi Shogi.C

def s15s (code : Nat) (dr dc fwd : Int) : State :=
  ⟨(fun i => match i with | 0 => some (i8 code) | 1 => some (i32 dr) | 2 => some (i32 dc) | 3 => some (i32 fwd) | _ => none), (fun _ => none), false⟩

def u8bool (b : Bool) : Val := .int ⟨8, false⟩ (if b then 1 else 0)

theorem i8_toInt_wrap (n : Nat) (h : n < 128) :
    IntTy.toInt IntTy.i8 (((n : Int) % 256).toNat) = (n : Int) := by
  have hw : ((n : Int) % 256).toNat = n := by rw [Int.emod_eq_of_lt (by omega) (by omega)]; simp
  rw [hw]; simp [IntTy.toInt, IntTy.i8, IntTy.modulus]; omega

theorem fid15_i8_int (n : Nat) (h : n < 128) : IntTy.toInt IntTy.i8 n = (n : Int) := by
  simp [IntTy.toInt, IntTy.i8, IntTy.modulus]; omega

theorem i32_toInt_small : ∀ n : Nat, n < 128 → IntTy.toInt (⟨32, true⟩ : IntTy) n = (n : Int) := by
  intro n h; simp [IntTy.toInt, IntTy.modulus]; omega

theorem fid15_neg1 : IntTy.toInt (⟨32, true⟩ : IntTy) 4294967295 = -1 := by
  simp [IntTy.toInt, IntTy.modulus]

theorem fid15_toInt_mod (z : Int) (h1 : -2147483648 ≤ z) (h2 : z < 2147483648) :
    IntTy.toInt (⟨32, true⟩ : IntTy) ((z % 4294967296).toNat) = z := by
  simpa [IntTy.wrap, IntTy.modulus] using toInt_wrap32 z h1 h2

def c1 : Expr := (.land (.land (.bin .eq (some ⟨32, false⟩) (.cast ⟨32, false⟩ (.var 0)) (.cast ⟨32, false⟩ (.const (.int ⟨32, true⟩ 1)))) (.bin .eq (some ⟨32, true⟩) (.var 1) (.var 3))) (.bin .eq (some ⟨32, true⟩) (.var 2) (.const (.int ⟨32, true⟩ 0))))
def c2 : Expr := (.land (.land (.bin .eq (some ⟨32, false⟩) (.cast ⟨32, false⟩ (.var 0)) (.cast ⟨32, false⟩ (.const (.int ⟨32, true⟩ 3)))) (.bin .eq (some ⟨32, true⟩) (.var 1) (.bin .mul (some ⟨32, true⟩) (.const (.int ⟨32, true⟩ 2)) (.var 3)))) (.lor (.bin .eq (some ⟨32, true⟩) (.var 2) (.un .neg ⟨32, true⟩ (.const (.int ⟨32, true⟩ 1)))) (.bin .eq (some ⟨32, true⟩) (.var 2) (.const (.int ⟨32, true⟩ 1)))))
def c3 : Expr := (.land (.bin .eq (some ⟨32, false⟩) (.cast ⟨32, false⟩ (.var 0)) (.cast ⟨32, false⟩ (.const (.int ⟨32, true⟩ 4)))) (.lor (.land (.land (.bin .eq (some ⟨32, true⟩) (.var 1) (.var 3)) (.bin .ge (some ⟨32, true⟩) (.var 2) (.un .neg ⟨32, true⟩ (.const (.int ⟨32, true⟩ 1))))) (.bin .le (some ⟨32, true⟩) (.var 2) (.const (.int ⟨32, true⟩ 1)))) (.land (.bin .eq (some ⟨32, true⟩) (.var 1) (.un .neg ⟨32, true⟩ (.var 3))) (.lor (.bin .eq (some ⟨32, true⟩) (.var 2) (.un .neg ⟨32, true⟩ (.const (.int ⟨32, true⟩ 1)))) (.bin .eq (some ⟨32, true⟩) (.var 2) (.const (.int ⟨32, true⟩ 1)))))))
def c4 : Expr := (.land (.lor (.lor (.lor (.lor (.bin .eq (some ⟨32, false⟩) (.cast ⟨32, false⟩ (.var 0)) (.cast ⟨32, false⟩ (.const (.int ⟨32, true⟩ 5)))) (.bin .eq (some ⟨32, false⟩) (.cast ⟨32, false⟩ (.var 0)) (.cast ⟨32, false⟩ (.const (.int ⟨32, true⟩ 9))))) (.bin .eq (some ⟨32, false⟩) (.cast ⟨32, false⟩ (.var 0)) (.cast ⟨32, false⟩ (.const (.int ⟨32, true⟩ 10))))) (.bin .eq (some ⟨32, false⟩) (.cast ⟨32, false⟩ (.var 0)) (.cast ⟨32, false⟩ (.const (.int ⟨32, true⟩ 11))))) (.bin .eq (some ⟨32, false⟩) (.cast ⟨32, false⟩ (.var 0)) (.cast ⟨32, false⟩ (.const (.int ⟨32, true⟩ 12))))) (.lor (.lor (.land (.land (.bin .eq (some ⟨32, true⟩) (.var 1) (.var 3)) (.bin .ge (some ⟨32, true⟩) (.var 2) (.un .neg ⟨32, true⟩ (.const (.int ⟨32, true⟩ 1))))) (.bin .le (some ⟨32, true⟩) (.var 2) (.const (.int ⟨32, true⟩ 1)))) (.land (.bin .eq (some ⟨32, true⟩) (.var 1) (.const (.int ⟨32, true⟩ 0))) (.lor (.bin .eq (some ⟨32, true⟩) (.var 2) (.un .neg ⟨32, true⟩ (.const (.int ⟨32, true⟩ 1)))) (.bin .eq (some ⟨32, true⟩) (.var 2) (.const (.int ⟨32, true⟩ 1)))))) (.land (.bin .eq (some ⟨32, true⟩) (.var 1) (.un .neg ⟨32, true⟩ (.var 3))) (.bin .eq (some ⟨32, true⟩) (.var 2) (.const (.int ⟨32, true⟩ 0))))))
def c5 : Expr := (.land (.land (.land (.land (.land (.bin .eq (some ⟨32, false⟩) (.cast ⟨32, false⟩ (.var 0)) (.cast ⟨32, false⟩ (.const (.int ⟨32, true⟩ 8)))) (.bin .ge (some ⟨32, true⟩) (.var 1) (.un .neg ⟨32, true⟩ (.const (.int ⟨32, true⟩ 1))))) (.bin .le (some ⟨32, true⟩) (.var 1) (.const (.int ⟨32, true⟩ 1)))) (.bin .ge (some ⟨32, true⟩) (.var 2) (.un .neg ⟨32, true⟩ (.const (.int ⟨32, true⟩ 1))))) (.bin .le (some ⟨32, true⟩) (.var 2) (.const (.int ⟨32, true⟩ 1)))) (.lor (.bin .ne (some ⟨32, true⟩) (.var 1) (.const (.int ⟨32, true⟩ 0))) (.bin .ne (some ⟨32, true⟩) (.var 2) (.const (.int ⟨32, true⟩ 0)))))
def c6 : Expr := (.land (.bin .eq (some ⟨32, false⟩) (.cast ⟨32, false⟩ (.var 0)) (.cast ⟨32, false⟩ (.const (.int ⟨32, true⟩ 13)))) (.bin .eq (some ⟨32, true⟩) (.bin .add (some ⟨32, true⟩) (.cond (.bin .lt (some ⟨32, true⟩) (.var 1) (.const (.int ⟨32, true⟩ 0))) (.un .neg ⟨32, true⟩ (.var 1)) (.var 1)) (.cond (.bin .lt (some ⟨32, true⟩) (.var 2) (.const (.int ⟨32, true⟩ 0))) (.un .neg ⟨32, true⟩ (.var 2)) (.var 2))) (.const (.int ⟨32, true⟩ 1))))
def c7 : Expr := (.land (.land (.bin .eq (some ⟨32, false⟩) (.cast ⟨32, false⟩ (.var 0)) (.cast ⟨32, false⟩ (.const (.int ⟨32, true⟩ 14)))) (.bin .eq (some ⟨32, true⟩) (.cond (.bin .lt (some ⟨32, true⟩) (.var 1) (.const (.int ⟨32, true⟩ 0))) (.un .neg ⟨32, true⟩ (.var 1)) (.var 1)) (.const (.int ⟨32, true⟩ 1)))) (.bin .eq (some ⟨32, true⟩) (.cond (.bin .lt (some ⟨32, true⟩) (.var 2) (.const (.int ⟨32, true⟩ 0))) (.un .neg ⟨32, true⟩ (.var 2)) (.var 2)) (.const (.int ⟨32, true⟩ 1))))
-- spec predicates (Bool)
def sp1 (code : Nat) (dr dc fwd : Int) : Bool := (code == 1) && (dr == fwd) && (dc == 0)
def sp2 (code : Nat) (dr dc fwd : Int) : Bool := (code == 3) && (dr == 2*fwd) && (dc == -1 || dc == 1)
def sp3 (code : Nat) (dr dc fwd : Int) : Bool := (code == 4) &&
  ((dr == fwd && dc >= -1 && dc <= 1) || (dr == -fwd && (dc == -1 || dc == 1)))
def sp4 (code : Nat) (dr dc fwd : Int) : Bool :=
  (code == 5 || code == 9 || code == 10 || code == 11 || code == 12) &&
  ((dr == fwd && dc >= -1 && dc <= 1) || (dr == 0 && (dc == -1 || dc == 1)) || (dr == -fwd && dc == 0))
def sp5 (code : Nat) (dr dc fwd : Int) : Bool :=
  (code == 8) && (dr >= -1) && (dr <= 1) && (dc >= -1) && (dc <= 1) && (dr != 0 || dc != 0)
def sp6 (code : Nat) (dr dc fwd : Int) : Bool :=
  (code == 13) && ((if dr < 0 then -dr else dr) + (if dc < 0 then -dc else dc) == 1)
def sp7 (code : Nat) (dr dc fwd : Int) : Bool :=
  (code == 14) && ((if dr < 0 then -dr else dr) == 1) && ((if dc < 0 then -dc else dc) == 1)

def cformula (code : Nat) (dr dc fwd : Int) : Bool :=
  sp1 code dr dc fwd || sp2 code dr dc fwd || sp3 code dr dc fwd || sp4 code dr dc fwd ||
  sp5 code dr dc fwd || sp6 code dr dc fwd || sp7 code dr dc fwd

theorem fid15_ev_c1 (code : Nat) (hcode : code < 128) (dr dc fwd : Int)
    (hdr : -2147483648 ≤ dr ∧ dr < 2147483648) (hdc : -2147483648 ≤ dc ∧ dc < 2147483648)
    (hfwd : fwd = 1 ∨ fwd = -1) :
    EvE Gen.prog (s15s code dr dc fwd) c1 (boolVal (sp1 code dr dc fwd)) := by
  classical
  by_cases ha0 : code = 1 <;> by_cases ha1 : dr = fwd <;> by_cases ha2 : dc = 0
  all_goals
    refine EvE_of_eval (n := 20) ?_
    simp [sp1, sp2, sp3, sp4, sp5, sp6, sp7, c1, s15s, evalExpr, evalBin, evalBinInt, binInt, intOf, isPtr, evalUn,
      evalCast, IntTy.wrap, IntTy.modulus, i8, i32, IntTy.i32, IntTy.u32, ha0, ha1, ha2,
      boolVal, truthy, Res.bind_eq, i8_toInt_wrap code hcode,
      show (2 : Nat) ^ IntTy.i8.width = 256 by rfl, show IntTy.i8.signed = true by rfl,
      show (code : Int) % 4294967296 = code by rw [Int.emod_eq_of_lt (by omega) (by omega)],
      fid15_toInt_mod dr hdr.1 hdr.2, fid15_toInt_mod dc hdc.1 hdc.2,
      fid15_toInt_mod fwd (by rcases hfwd with rfl | rfl <;> omega) (by rcases hfwd with rfl | rfl <;> omega),
      fid15_neg1,
      show (IntTy.i8.toInt 1 % 4294967296).toNat = 1 by simp [IntTy.toInt, IntTy.i8, IntTy.modulus],
      show (IntTy.i8.toInt 0 % 4294967296).toNat = 0 by simp [IntTy.toInt, IntTy.i8, IntTy.modulus],
      i32_toInt_small 1 (by omega), i32_toInt_small 0 (by omega)]

theorem fid15_ev_c2 (code : Nat) (hcode : code < 128) (dr dc fwd : Int)
    (hdr : -2147483648 ≤ dr ∧ dr < 2147483648) (hdc : -2147483648 ≤ dc ∧ dc < 2147483648)
    (hfwd : fwd = 1 ∨ fwd = -1) :
    EvE Gen.prog (s15s code dr dc fwd) c2 (boolVal (sp2 code dr dc fwd)) := by
  classical
  by_cases ha0 : code = 3 <;> by_cases ha1 : dr = 2*fwd <;> by_cases ha2 : dc = -1 <;> by_cases ha3 : dc = 1
  all_goals
    refine EvE_of_eval (n := 20) ?_
    simp [sp1, sp2, sp3, sp4, sp5, sp6, sp7, c2, s15s, evalExpr, evalBin, evalBinInt, binInt, intOf, isPtr, evalUn,
      evalCast, IntTy.wrap, IntTy.modulus, i8, i32, IntTy.i32, IntTy.u32, ha0, ha1, ha2, ha3,
      boolVal, truthy, Res.bind_eq, i8_toInt_wrap code hcode,
      show (2 : Nat) ^ IntTy.i8.width = 256 by rfl, show IntTy.i8.signed = true by rfl,
      show (code : Int) % 4294967296 = code by rw [Int.emod_eq_of_lt (by omega) (by omega)],
      show (IntTy.i8.toInt 0 % 4294967296).toNat = 0 by simp [IntTy.toInt, IntTy.i8, IntTy.modulus], beq_iff_eq,
      show (IntTy.i8.toInt 1 % 4294967296).toNat = 1 by simp [IntTy.toInt, IntTy.i8, IntTy.modulus], show (IntTy.i8.toInt 2 % 4294967296).toNat = 2 by simp [IntTy.toInt, IntTy.i8, IntTy.modulus], show (IntTy.i8.toInt 3 % 4294967296).toNat = 3 by simp [IntTy.toInt, IntTy.i8, IntTy.modulus], show (IntTy.i8.toInt 4 % 4294967296).toNat = 4 by simp [IntTy.toInt, IntTy.i8, IntTy.modulus], show (IntTy.i8.toInt 5 % 4294967296).toNat = 5 by simp [IntTy.toInt, IntTy.i8, IntTy.modulus], show (IntTy.i8.toInt 6 % 4294967296).toNat = 6 by simp [IntTy.toInt, IntTy.i8, IntTy.modulus], show (IntTy.i8.toInt 7 % 4294967296).toNat = 7 by simp [IntTy.toInt, IntTy.i8, IntTy.modulus], show (IntTy.i8.toInt 8 % 4294967296).toNat = 8 by simp [IntTy.toInt, IntTy.i8, IntTy.modulus], show (IntTy.i8.toInt 9 % 4294967296).toNat = 9 by simp [IntTy.toInt, IntTy.i8, IntTy.modulus], show (IntTy.i8.toInt 10 % 4294967296).toNat = 10 by simp [IntTy.toInt, IntTy.i8, IntTy.modulus], show (IntTy.i8.toInt 11 % 4294967296).toNat = 11 by simp [IntTy.toInt, IntTy.i8, IntTy.modulus], show (IntTy.i8.toInt 12 % 4294967296).toNat = 12 by simp [IntTy.toInt, IntTy.i8, IntTy.modulus], show (IntTy.i8.toInt 13 % 4294967296).toNat = 13 by simp [IntTy.toInt, IntTy.i8, IntTy.modulus], show (IntTy.i8.toInt 14 % 4294967296).toNat = 14 by simp [IntTy.toInt, IntTy.i8, IntTy.modulus],
      beq_iff_eq,
      show (IntTy.i8.toInt 1 % 4294967296).toNat = 1 by simp [IntTy.toInt, IntTy.i8, IntTy.modulus],
      show (IntTy.i8.toInt 0 % 4294967296).toNat = 0 by simp [IntTy.toInt, IntTy.i8, IntTy.modulus],
      fid15_toInt_mod dr hdr.1 hdr.2, fid15_toInt_mod dc hdc.1 hdc.2,
      fid15_toInt_mod fwd (by rcases hfwd with rfl | rfl <;> omega) (by rcases hfwd with rfl | rfl <;> omega),
      i32_toInt_small 1 (by omega), i32_toInt_small 0 (by omega), i32_toInt_small 2 (by omega),
      i32_toInt_small 3 (by omega), i32_toInt_small 4 (by omega), i32_toInt_small 5 (by omega),
      i32_toInt_small 6 (by omega), i32_toInt_small 7 (by omega), i32_toInt_small 8 (by omega),
      i32_toInt_small 9 (by omega), i32_toInt_small 10 (by omega), i32_toInt_small 11 (by omega),
      i32_toInt_small 12 (by omega), i32_toInt_small 13 (by omega), i32_toInt_small 14 (by omega),
      fid15_neg1, arith, IntTy.inRange, IntTy.minVal, IntTy.maxVal,
      show -2147483648 ≤ 2*fwd ∧ 2*fwd ≤ 2147483647 by rcases hfwd with rfl | rfl <;> omega,
      show IntTy.toInt (⟨32, true⟩ : IntTy) ((2*fwd % 4294967296).toNat) = 2*fwd by
        apply fid15_toInt_mod <;> rcases hfwd with rfl | rfl <;> omega]

theorem fid15_ev_c3 (code : Nat) (hcode : code < 128) (dr dc fwd : Int)
    (hdr : -2147483648 ≤ dr ∧ dr < 2147483648) (hdc : -2147483648 ≤ dc ∧ dc < 2147483648)
    (hfwd : fwd = 1 ∨ fwd = -1) :
    EvE Gen.prog (s15s code dr dc fwd) c3 (boolVal (sp3 code dr dc fwd)) := by
  classical
  by_cases ha0 : code = 4 <;> by_cases ha1 : dr = fwd <;> by_cases ha2 : dc >= -1 <;> by_cases ha3 : dc <= 1 <;> by_cases ha4 : dr = -fwd <;> by_cases ha5 : dc = -1 <;> by_cases ha6 : dc = 1
  all_goals
    refine EvE_of_eval (n := 20) ?_
    simp [sp1, sp2, sp3, sp4, sp5, sp6, sp7, beq_iff_eq, c3, s15s, evalExpr, evalBin, evalBinInt, binInt, intOf, isPtr, evalUn,
      evalCast, IntTy.wrap, IntTy.modulus, i8, i32, IntTy.i32, IntTy.u32, ha0, ha1, ha2, ha3, ha4, ha5, ha6,
      boolVal, truthy, Res.bind_eq, i8_toInt_wrap code hcode,
      show (2 : Nat) ^ IntTy.i8.width = 256 by rfl, show IntTy.i8.signed = true by rfl,
      show (code : Int) % 4294967296 = code by rw [Int.emod_eq_of_lt (by omega) (by omega)],
      show (IntTy.i8.toInt 0 % 4294967296).toNat = 0 by simp [IntTy.toInt, IntTy.i8, IntTy.modulus], show (IntTy.i8.toInt 1 % 4294967296).toNat = 1 by simp [IntTy.toInt, IntTy.i8, IntTy.modulus], show (IntTy.i8.toInt 2 % 4294967296).toNat = 2 by simp [IntTy.toInt, IntTy.i8, IntTy.modulus], show (IntTy.i8.toInt 3 % 4294967296).toNat = 3 by simp [IntTy.toInt, IntTy.i8, IntTy.modulus], show (IntTy.i8.toInt 4 % 4294967296).toNat = 4 by simp [IntTy.toInt, IntTy.i8, IntTy.modulus], show (IntTy.i8.toInt 5 % 4294967296).toNat = 5 by simp [IntTy.toInt, IntTy.i8, IntTy.modulus], show (IntTy.i8.toInt 6 % 4294967296).toNat = 6 by simp [IntTy.toInt, IntTy.i8, IntTy.modulus], show (IntTy.i8.toInt 7 % 4294967296).toNat = 7 by simp [IntTy.toInt, IntTy.i8, IntTy.modulus], show (IntTy.i8.toInt 8 % 4294967296).toNat = 8 by simp [IntTy.toInt, IntTy.i8, IntTy.modulus], show (IntTy.i8.toInt 9 % 4294967296).toNat = 9 by simp [IntTy.toInt, IntTy.i8, IntTy.modulus], show (IntTy.i8.toInt 10 % 4294967296).toNat = 10 by simp [IntTy.toInt, IntTy.i8, IntTy.modulus], show (IntTy.i8.toInt 11 % 4294967296).toNat = 11 by simp [IntTy.toInt, IntTy.i8, IntTy.modulus], show (IntTy.i8.toInt 12 % 4294967296).toNat = 12 by simp [IntTy.toInt, IntTy.i8, IntTy.modulus], show (IntTy.i8.toInt 13 % 4294967296).toNat = 13 by simp [IntTy.toInt, IntTy.i8, IntTy.modulus], show (IntTy.i8.toInt 14 % 4294967296).toNat = 14 by simp [IntTy.toInt, IntTy.i8, IntTy.modulus],
      show (IntTy.i8.toInt 1 % 4294967296).toNat = 1 by simp [IntTy.toInt, IntTy.i8, IntTy.modulus],
      show (IntTy.i8.toInt 0 % 4294967296).toNat = 0 by simp [IntTy.toInt, IntTy.i8, IntTy.modulus],
      fid15_toInt_mod dr hdr.1 hdr.2, fid15_toInt_mod dc hdc.1 hdc.2,
      fid15_toInt_mod fwd (by rcases hfwd with rfl | rfl <;> omega) (by rcases hfwd with rfl | rfl <;> omega),
      i32_toInt_small 1 (by omega), i32_toInt_small 0 (by omega), i32_toInt_small 2 (by omega),
      i32_toInt_small 3 (by omega), i32_toInt_small 4 (by omega), i32_toInt_small 5 (by omega),
      i32_toInt_small 6 (by omega), i32_toInt_small 7 (by omega), i32_toInt_small 8 (by omega),
      i32_toInt_small 9 (by omega), i32_toInt_small 10 (by omega), i32_toInt_small 11 (by omega),
      i32_toInt_small 12 (by omega), i32_toInt_small 13 (by omega), i32_toInt_small 14 (by omega),
      fid15_neg1, arith, IntTy.inRange, IntTy.minVal, IntTy.maxVal,
      show -2147483648 ≤ -1 ∧ -1 ≤ 2147483647 by omega,
      show -fwd ≠ fwd by rcases hfwd with rfl | rfl <;> omega,
      show fwd ≤ 2147483648 by rcases hfwd with rfl | rfl <;> omega,
      show -2147483648 ≤ -fwd ∧ -fwd ≤ 2147483647 by rcases hfwd with rfl | rfl <;> omega,
      show IntTy.toInt (⟨32, true⟩ : IntTy) (((-1 : Int) % 4294967296).toNat) = -1 by
        simpa [IntTy.wrap, IntTy.modulus] using fid15_toInt_mod (-1) (by omega) (by omega),
      show IntTy.toInt (⟨32, true⟩ : IntTy) (((-fwd : Int) % 4294967296).toNat) = -fwd by
        apply fid15_toInt_mod <;> rcases hfwd with rfl | rfl <;> omega]

theorem fid15_ev_c4 (code : Nat) (hcode : code < 128) (dr dc fwd : Int)
    (hdr : -2147483648 ≤ dr ∧ dr < 2147483648) (hdc : -2147483648 ≤ dc ∧ dc < 2147483648)
    (hfwd : fwd = 1 ∨ fwd = -1) :
    EvE Gen.prog (s15s code dr dc fwd) c4 (boolVal (sp4 code dr dc fwd)) := by
  classical
  by_cases ha0 : code = 5 <;> by_cases ha1 : code = 9 <;> by_cases ha2 : code = 10 <;> by_cases ha3 : code = 11 <;> by_cases ha4 : code = 12 <;> by_cases ha5 : dr = fwd <;> by_cases ha6 : dc >= -1 <;> by_cases ha7 : dc <= 1 <;> by_cases ha8 : dr = 0 <;> by_cases ha9 : dc = -1 <;> by_cases ha10 : dc = 1 <;> by_cases ha11 : dr = -fwd <;> by_cases ha12 : dc = 0
  all_goals
    refine EvE_of_eval (n := 20) ?_
    simp [c4, s15s, evalExpr, evalBin, evalBinInt, binInt, intOf, isPtr, evalUn,
      evalCast, IntTy.wrap, IntTy.modulus, i8, i32, IntTy.i32, IntTy.u32, ha0, ha1, ha2, ha3, ha4, ha5, ha6, ha7, ha8, ha9, ha10, ha11, ha12,
      boolVal, truthy, Res.bind_eq, i8_toInt_wrap code hcode,
      show (2 : Nat) ^ IntTy.i8.width = 256 by rfl, show IntTy.i8.signed = true by rfl,
      show (code : Int) % 4294967296 = code by rw [Int.emod_eq_of_lt (by omega) (by omega)],
      fid15_toInt_mod dr hdr.1 hdr.2, fid15_toInt_mod dc hdc.1 hdc.2,
      fid15_toInt_mod fwd (by rcases hfwd with rfl | rfl <;> omega) (by rcases hfwd with rfl | rfl <;> omega),
      fid15_neg1,]

theorem fid15_ev_c5 (code : Nat) (hcode : code < 128) (dr dc fwd : Int)
    (hdr : -2147483648 ≤ dr ∧ dr < 2147483648) (hdc : -2147483648 ≤ dc ∧ dc < 2147483648)
    (hfwd : fwd = 1 ∨ fwd = -1) :
    EvE Gen.prog (s15s code dr dc fwd) c5 (boolVal (sp5 code dr dc fwd)) := by
  classical
  by_cases ha0 : code = 8 <;> by_cases ha1 : dr >= -1 <;> by_cases ha2 : dr <= 1 <;> by_cases ha3 : dc >= -1 <;> by_cases ha4 : dc <= 1 <;> by_cases ha5 : dr ≠ 0 <;> by_cases ha6 : dc ≠ 0
  all_goals
    refine EvE_of_eval (n := 20) ?_
    simp [c5, s15s, evalExpr, evalBin, evalBinInt, binInt, intOf, isPtr, evalUn,
      evalCast, IntTy.wrap, IntTy.modulus, i8, i32, IntTy.i32, IntTy.u32, ha0, ha1, ha2, ha3, ha4, ha5, ha6,
      boolVal, truthy, Res.bind_eq, i8_toInt_wrap code hcode,
      show (2 : Nat) ^ IntTy.i8.width = 256 by rfl, show IntTy.i8.signed = true by rfl,
      show (code : Int) % 4294967296 = code by rw [Int.emod_eq_of_lt (by omega) (by omega)],
      fid15_toInt_mod dr hdr.1 hdr.2, fid15_toInt_mod dc hdc.1 hdc.2,
      fid15_toInt_mod fwd (by rcases hfwd with rfl | rfl <;> omega) (by rcases hfwd with rfl | rfl <;> omega),
      fid15_neg1,]

theorem fid15_ev_c6 (code : Nat) (hcode : code < 128) (dr dc fwd : Int)
    (hdr : -2147483648 ≤ dr ∧ dr < 2147483648) (hdc : -2147483648 ≤ dc ∧ dc < 2147483648)
    (hfwd : fwd = 1 ∨ fwd = -1) :
    EvE Gen.prog (s15s code dr dc fwd) c6 (boolVal (sp6 code dr dc fwd)) := by
  classical
  by_cases ha0 : code = 13 <;> by_cases ha1 : dr < 0 <;> by_cases ha2 : dc < 0
  all_goals
    refine EvE_of_eval (n := 20) ?_
    simp [c6, s15s, evalExpr, evalBin, evalBinInt, binInt, intOf, isPtr, evalUn,
      evalCast, IntTy.wrap, IntTy.modulus, i8, i32, IntTy.i32, IntTy.u32, ha0, ha1, ha2,
      boolVal, truthy, Res.bind_eq, i8_toInt_wrap code hcode,
      show (2 : Nat) ^ IntTy.i8.width = 256 by rfl, show IntTy.i8.signed = true by rfl,
      show (code : Int) % 4294967296 = code by rw [Int.emod_eq_of_lt (by omega) (by omega)],
      fid15_toInt_mod dr hdr.1 hdr.2, fid15_toInt_mod dc hdc.1 hdc.2,
      fid15_toInt_mod fwd (by rcases hfwd with rfl | rfl <;> omega) (by rcases hfwd with rfl | rfl <;> omega),
      fid15_neg1,]

theorem fid15_ev_c7 (code : Nat) (hcode : code < 128) (dr dc fwd : Int)
    (hdr : -2147483648 ≤ dr ∧ dr < 2147483648) (hdc : -2147483648 ≤ dc ∧ dc < 2147483648)
    (hfwd : fwd = 1 ∨ fwd = -1) :
    EvE Gen.prog (s15s code dr dc fwd) c7 (boolVal (sp7 code dr dc fwd)) := by
  classical
  by_cases ha0 : code = 14 <;> by_cases ha1 : dr < 0 <;> by_cases ha2 : dc < 0
  all_goals
    refine EvE_of_eval (n := 20) ?_
    simp [c7, s15s, evalExpr, evalBin, evalBinInt, binInt, intOf, isPtr, evalUn,
      evalCast, IntTy.wrap, IntTy.modulus, i8, i32, IntTy.i32, IntTy.u32, ha0, ha1, ha2,
      boolVal, truthy, Res.bind_eq, i8_toInt_wrap code hcode,
      show (2 : Nat) ^ IntTy.i8.width = 256 by rfl, show IntTy.i8.signed = true by rfl,
      show (code : Int) % 4294967296 = code by rw [Int.emod_eq_of_lt (by omega) (by omega)],
      fid15_toInt_mod dr hdr.1 hdr.2, fid15_toInt_mod dc hdc.1 hdc.2,
      fid15_toInt_mod fwd (by rcases hfwd with rfl | rfl <;> omega) (by rcases hfwd with rfl | rfl <;> omega),
      fid15_neg1,]

def rTrue : Stmt := .ret (some (.cast ⟨8, false⟩ (.bin .ne (some ⟨32, true⟩) (.const (.int ⟨32, true⟩ 1)) (.const (.int ⟨32, true⟩ 0)))))
def rFinal : Stmt := .ret (some (.cast ⟨8, false⟩ (.bin .ne (some ⟨32, true⟩) (.const (.int ⟨32, true⟩ 0)) (.const (.int ⟨32, true⟩ 0)))))

end Shogi.C.Proofs
