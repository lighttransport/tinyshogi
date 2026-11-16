/-
  T8: `king_safety_prepare`, part 1 — evaluating the ray-table accesses, with
  the king square read back from the `KingSafety` record.
-/
import Shogi.C.Proofs.Unmake

namespace Shogi.C.Proofs
open MiniC Shogi Shogi.C

section ksexprs
variable {s : State} {Sb : Nat} {S : List UInt8} {t : Square} {r : Nat}
  (hS3 : s.locals 3 = some (.ptr Sb 0)) (hSm : s.mem Sb = some S) (hSl : S.length = 84)
  (hS0 : S.getD 0 0 = t.val.toUInt8)
include hS3 hSm hSl hS0

theorem evKing : EvE Gen.prog s (.load (.int ⟨8, false⟩) (.field (.var 3) 0)) (.int IntTy.u8 t.val) := by
  have := ev_blk_u8 hS3 hSm (k := 0) (by omega)
  rw [hS0, toNat_toUInt8_lt _ (by have := t.isLt; omega)] at this; exact this

theorem evRayLen (hr : r < 8) (h7 : s.locals 7 = some (.int IntTy.u32 r))
    (hG : s.mem 8195 = some Gen.global_attack_ray_length) :
    EvE Gen.prog s (.load (.int ⟨8, false⟩) (.index (.index (.const (.ptr 8195 0))
      (.load (.int ⟨8, false⟩) (.field (.var 3) 0)) 8) (.var 7) 1))
      (.int IntTy.u8 (ray t (rdir r)).length) := by
  have ht := t.isLt
  have := load_u8_at (o := 0 + t.val * 8 + r * 1)
    (EvE.index (pb := .ptr 8195 (0 + t.val * 8)) (elem := 1)
      (EvE.index (elem := 8) (EvE.const (.ptr 8195 0)) (evKing hS3 hSm hSl hS0) (by simp [ptrAddN, hG, G4_len, IntTy.u8]; omega))
      (EvE.var h7) (by simp [ptrAddN, hG, G4_len, IntTy.u32]; omega)) hG (by rw [G4_len]; omega)
  rw [show 0 + t.val * 8 + r * 1 = t.val * 8 + r by omega,
    rayLen_G t r _ attack_ray_length_refine hr] at this
  exact this

theorem evRaySq (hr : r < 8) {k : Nat} (hk : k < (ray t (rdir r)).length) (h7 : s.locals 7 = some (.int IntTy.u32 r))
    (h9 : s.locals 9 = some (.int IntTy.u8 k)) (hG : s.mem 8194 = some Gen.global_attack_rays) :
    EvE Gen.prog s (.load (.int ⟨8, false⟩) (.index (.index (.index (.const (.ptr 8194 0))
      (.load (.int ⟨8, false⟩) (.field (.var 3) 0)) 64) (.var 7) 8) (.var 9) 1))
      (.int IntTy.u8 ((ray t (rdir r))[k]).val) := by
  have ht := t.isLt
  have hl8 := ray_length_le t (rdir r)
  have := load_u8_at (o := 0 + t.val * 64 + r * 8 + k * 1)
    (EvE.index (pb := .ptr 8194 (0 + t.val * 64 + r * 8)) (elem := 1)
      (EvE.index (pb := .ptr 8194 (0 + t.val * 64)) (elem := 8)
        (EvE.index (elem := 64) (EvE.const (.ptr 8194 0)) (evKing hS3 hSm hSl hS0) (by simp [ptrAddN, hG, G3_len, IntTy.u8]; omega))
        (EvE.var h7) (by simp [ptrAddN, hG, G3_len, IntTy.u32]; omega))
      (EvE.var h9) (by simp [ptrAddN, hG, G3_len, IntTy.u8]; omega)) hG (by rw [G3_len]; omega)
  rw [show 0 + t.val * 64 + r * 8 + k * 1 = t.val * 64 + (r * 8 + k) by omega,
    raySq_G t r k _ attack_rays_refine hr hk] at this
  exact this

theorem evMaskAddrK (hr : r < 8) {a : Color} (h5 : s.locals 5 = some (.int IntTy.u32 a.idx))
    (h7 : s.locals 7 = some (.int IntTy.u32 r)) (hG : s.mem 8196 = some Gen.global_attack_ray_masks) :
    EvE Gen.prog s (.index (.index (.index (.const (.ptr 8196 0)) (.var 5) 1296)
      (.load (.int ⟨8, false⟩) (.field (.var 3) 0)) 16) (.var 7) 2)
      (.ptr 8196 (a.idx * 1296 + t.val * 16 + r * 2)) := by
  have ht := t.isLt
  have hai : a.idx < 2 := by cases a <;> decide
  have := EvE.index (pb := .ptr 8196 (0 + a.idx * 1296 + t.val * 16)) (elem := 2)
    (EvE.index (pb := .ptr 8196 (0 + a.idx * 1296)) (elem := 16)
      (EvE.index (elem := 1296) (EvE.const (.ptr 8196 0)) (EvE.var h5) (by simp [ptrAddN, hG, G5_len, IntTy.u32]; omega))
      (evKing hS3 hSm hSl hS0) (by simp [ptrAddN, hG, G5_len, IntTy.u8]; omega))
    (EvE.var h7) (r := .ptr 8196 (0 + a.idx * 1296 + t.val * 16 + r * 2))
    (by simp [ptrAddN, hG, G5_len, IntTy.u32]; omega)
  simpa using this

end ksexprs

theorem shl_eq (k : Nat) : 1 <<< k = 2 ^ k := by rw [Nat.shiftLeft_eq, Nat.one_mul]

theorem evAttacks {s : State} {mk code : Nat} {addr : Expr} {blk o : Nat} (hmk : mk < 65536) (hc : code ≤ 14)
    (ha : EvE Gen.prog s addr (.ptr blk o)) (hr : readBytes s.mem blk o 2 = .ok (encodeLE 2 mk))
    (h14 : s.locals 14 = some (.int IntTy.u32 code)) :
    EvE Gen.prog s (.cast ⟨8, false⟩ (.bin .ne (some ⟨32, true⟩) (.bin .ne (some ⟨32, true⟩)
      (.bin .band (some ⟨32, true⟩) (.cast ⟨32, true⟩ (.load (.int ⟨16, false⟩) addr))
        (.bin .shl (some ⟨32, true⟩) (.cast ⟨32, true⟩ (.cast ⟨16, false⟩ (.const (.int ⟨32, false⟩ 1))))
          (.cast ⟨32, false⟩ (.var 14)))) (.const (.int ⟨32, true⟩ 0))) (.const (.int ⟨32, true⟩ 0))))
      (.int IntTy.u8 (if mk &&& 2 ^ code ≠ 0 then 1 else 0)) := by
  have hdec : decodeLE (encodeLE 2 mk) = mk := by simp [encodeLE, decodeLE]; omega
  have hpow : 2 ^ code ≤ 16384 := by
    have : 2 ^ code ≤ 2 ^ 14 := Nat.pow_le_pow_right (by decide) hc
    simpa using this
  have hand : mk &&& 2 ^ code ≤ mk := Nat.and_le_left
  have hload : EvE Gen.prog s (.load (.int ⟨16, false⟩) addr) (.int ⟨16, false⟩ mk) :=
    EvE.load ha (by simp [load, Ty.size, IntTy.bytes, hr, hdec])
  have hcst : EvE Gen.prog s (.cast ⟨32, true⟩ (.load (.int ⟨16, false⟩) addr)) (.int IntTy.i32 mk) :=
    EvE.cast hload (by simp [evalCast, IntTy.modulus, IntTy.i32]; omega)
  have hshl : EvE Gen.prog s (.bin .shl (some ⟨32, true⟩) (.cast ⟨32, true⟩ (.cast ⟨16, false⟩
      (.const (.int ⟨32, false⟩ 1)))) (.cast ⟨32, false⟩ (.var 14))) (.int IntTy.i32 (2 ^ code)) := by
    apply EvE_of_eval (n := 5)
    have hcast : ((2 : Int) ^ code) = ((2 ^ code : Nat) : Int) := (Int.natCast_pow 2 code).symm
    have hp0 : (0 : Int) ≤ 2 ^ code := by rw [hcast]; exact Int.natCast_nonneg _
    have hp1 : (2 : Int) ^ code ≤ 16384 := by rw [hcast]; have := hpow; omega
    simp [evalExpr, h14, evalCast, evalBin, isPtr, evalBinInt, binInt, intOf, IntTy.toInt, IntTy.wrap,
      IntTy.modulus, IntTy.u32, IntTy.i32, Res.bind, MiniC.guard, arith, IntTy.inRange, IntTy.minVal,
      IntTy.maxVal, Nat.mod_eq_of_lt (show code < 4294967296 by omega)]
    rw [if_pos (by omega)]
    simp only
    rw [if_pos ⟨by omega, by omega⟩]
    simp only [Res.ok.injEq, Val.int.injEq, true_and]
    rw [Int.emod_eq_of_lt (by omega) (by omega), hcast]; rfl
  have hband := EvE.bin (op := .band) (t := some ⟨32, true⟩) hcst hshl
    (v := .int IntTy.i32 (mk &&& 2 ^ code)) (by simp [evalBin, isPtr, evalBinInt, binInt, intOf, IntTy.i32, Res.bind])
  have hne1 := EvE.bin (op := .ne) (t := some ⟨32, true⟩) hband (EvE.const (.int ⟨32, true⟩ 0))
    (v := boolVal (decide (mk &&& 2 ^ code ≠ 0)))
    (by simp [evalBin, isPtr, evalBinInt, binInt, intOf, IntTy.i32, IntTy.toInt, IntTy.modulus, Res.bind,
      boolVal, show ¬ (2147483648 ≤ mk &&& 2 ^ code) by omega])
  have hne2 := EvE.bin (op := .ne) (t := some ⟨32, true⟩) hne1 (EvE.const (.int ⟨32, true⟩ 0))
    (v := boolVal (decide (mk &&& 2 ^ code ≠ 0)))
    (by by_cases h : mk &&& 2 ^ code = 0 <;> simp [h, evalBin, isPtr, evalBinInt, binInt, intOf, IntTy.i32,
      IntTy.toInt, boolVal, Res.bind])
  refine EvE.cast hne2 ?_
  by_cases h : mk &&& 2 ^ code = 0 <;> simp [h, evalCast, boolVal, IntTy.i32, IntTy.u8, IntTy.toInt, IntTy.wrap,
    IntTy.modulus]

end Shogi.C.Proofs
