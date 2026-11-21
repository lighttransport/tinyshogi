import Shogi.C.Proofs.ValidateMaterial
set_option maxHeartbeats 8000000
set_option linter.unusedSimpArgs false
set_option maxRecDepth 100000
namespace Shogi.C.Proofs
open MiniC Shogi Shogi.C

def s15s (code : Nat) (dr dc fwd : Int) : State :=
  ⟨(fun i => match i with | 0 => some (i8 code) | 1 => some (i32 dr) | 2 => some (i32 dc) | 3 => some (i32 fwd) | _ => none), (fun _ => none), false⟩

def fid15_u8bool (b : Bool) : Val := .int ⟨8, false⟩ (if b then 1 else 0)

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

end Shogi.C.Proofs
