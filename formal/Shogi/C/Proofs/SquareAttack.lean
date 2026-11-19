/-
  T7 layer 2: `square_attacked` refines the spec's `attacked`, for every
  position, target square and attacker. Steps: `step_square_attacked`
  (StepAttack.lean), then the 8 rays from the target with the translated
  `attack_rays` / `attack_ray_length` / `attack_ray_masks` tables (decoded
  symbolically to the Lean `ray` and `rayMask`), against the target-centred
  form of the spec (`attacked_eq`, AttackSpec.lean).
-/
import Shogi.C.Proofs.StepAttack
import Shogi.C.Proofs.NoWrite
import Shogi.AttackSpec

namespace Shogi.C.Proofs
variable {posBlock : Nat}
open MiniC Shogi Shogi.C Shogi.Tables Shogi.Position

theorem ray_length_le (t : Square) (d : Int × Int) : (ray t d).length ≤ 8 := by
  unfold ray
  suffices h : ∀ n s, (ray.go d n s).length ≤ n by exact h 8 t
  intro n
  induction n with
  | zero => intro s; simp [ray.go]
  | succ n ih => intro s; simp only [ray.go]; split <;> simp <;> have := ih ‹_›; omega

theorem rayDirs_len : rayDirs.length = 8 := rfl

def rdir (r : Nat) : Int × Int := rayDirs.getD r (0, 0)

theorem rdir_mem (r : Nat) (hr : r < 8) : rdir r ∈ rayDirs := by
  unfold rdir; rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by rw [rayDirs_len]; exact hr)]
  exact List.getElem_mem _

theorem rayLen_byte (t : Square) (r : Nat) (hr : r < 8) :
    attackRayLengthBytes.getD (t.val * 8 + r) 0 = (raySquares t (rdir r)).length.toUInt8 := by
  unfold attackRayLengthBytes
  rw [getD_flatMap_uniform _ 8 (List.finRange 81) (fun x _ => by simp [rayDirs_len]) t.val r
    (by simp) hr]
  simp only [List.getElem_finRange, Fin.cast_mk, Fin.eta]
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by simp [rayDirs_len]; exact hr)]
  simp [rdir, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (show r < rayDirs.length by
    rw [rayDirs_len]; exact hr)]

theorem raySq_byte (t : Square) (r k : Nat) (hr : r < 8) (hk : k < (ray t (rdir r)).length) :
    attackRaysBytes.getD (t.val * 64 + (r * 8 + k)) 0 = ((ray t (rdir r))[k]).val.toUInt8 := by
  have h8 : ∀ d, (padTo 8 0 (raySquares t d)).length = 8 := by
    intro d; have := ray_length_le t d; simp [padTo, raySquares]; omega
  unfold attackRaysBytes
  rw [getD_flatMap_uniform _ 64 (List.finRange 81) (fun x _ => by
      rw [length_flatMap_uniform _ 8 _ (fun d _ => by
        have := ray_length_le x d; simp [padTo, raySquares]; omega)]; simp [rayDirs_len])
    t.val (r * 8 + k) (by simp) (by have := ray_length_le t (rdir r); omega)]
  simp only [List.getElem_finRange, Fin.cast_mk, Fin.eta]
  rw [getD_flatMap_uniform _ 8 rayDirs (fun d _ => by simp [h8]) r k (by rw [rayDirs_len]; exact hr)
    (by have := ray_length_le t (rdir r); omega)]
  have hrd : rayDirs[r]'(by rw [rayDirs_len]; exact hr) = rdir r := by
    simp [rdir, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (show r < rayDirs.length by
      rw [rayDirs_len]; exact hr)]
  rw [hrd]
  have hl8 := ray_length_le t (rdir r)
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by rw [List.length_map, h8]; omega)]
  simp [padTo, raySquares, hk]

theorem rayMask_lt' (c : Color) : ∀ d ∈ rayDirs, rayMask c d < 65536 := by
  cases c <;> decide

theorem rayMask_lt (c : Color) (r : Nat) (hr : r < 8) : rayMask c (rdir r) < 65536 :=
  rayMask_lt' c _ (rdir_mem r hr)

theorem rayMask_bytes (c : Color) (t : Square) (r : Nat) (hr : r < 8) :
    [attackRayMasksBytes.getD (c.idx * 1296 + t.val * 16 + r * 2) 0,
     attackRayMasksBytes.getD (c.idx * 1296 + t.val * 16 + r * 2 + 1) 0] = encodeLE 2 (rayMask c (rdir r)) := by
  have hci : c.idx < 2 := by cases c <;> decide
  have h16 : ∀ c' : Color, ((List.finRange 81).flatMap fun _ => rayDirs.flatMap fun d => le16 (rayMask c' d)).length = 1296 := by
    intro c'
    rw [length_flatMap_uniform _ 16 _ (fun x _ => by
      rw [length_flatMap_uniform _ 2 _ (fun d _ => rfl)]; rfl)]
    simp
  have hrd : rayDirs[r]'(by rw [rayDirs_len]; exact hr) = rdir r := by
    simp [rdir, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (show r < rayDirs.length by
      rw [rayDirs_len]; exact hr)]
  have key : ∀ q < 2, attackRayMasksBytes.getD (c.idx * 1296 + (t.val * 16 + (r * 2 + q))) 0 =
      (le16 (rayMask c (rdir r))).getD q 0 := by
    intro q hq
    unfold attackRayMasksBytes
    rw [getD_flatMap_uniform _ 1296 colors (fun x _ => h16 x) c.idx _ (by cases c <;> decide)
      (by have := t.isLt; omega)]
    rw [colors_getElem]
    rw [getD_flatMap_uniform _ 16 (List.finRange 81) (fun x _ => by
      rw [length_flatMap_uniform _ 2 _ (fun d _ => rfl)]; rfl) t.val _ (by simp) (by omega)]
    rw [getD_flatMap_uniform _ 2 rayDirs (fun d _ => rfl) r q (by rw [rayDirs_len]; exact hr) hq]
    rw [hrd]
  have k0 := key 0 (by decide)
  have k1 := key 1 (by decide)
  simp only [Nat.add_zero] at k0
  rw [show c.idx * 1296 + t.val * 16 + r * 2 = c.idx * 1296 + (t.val * 16 + r * 2) by omega,
    show c.idx * 1296 + (t.val * 16 + r * 2) + 1 = c.idx * 1296 + (t.val * 16 + (r * 2 + 1)) by omega,
    k0, k1]
  have hm := rayMask_lt c r hr
  simp [le16, encodeLE, List.getD]


theorem G3_len : Gen.global_attack_rays.length = 5184 := by decide +kernel
theorem G4_len : Gen.global_attack_ray_length.length = 648 := by decide +kernel
theorem G5_len : Gen.global_attack_ray_masks.length = 2592 := by decide +kernel

/- Generic `cast i32 (var v) <op> 0` style tests and loads, with variable slots. -/
section exprs
variable (s : State)

theorem evEq0 {v b : Nat} (hb : b < 256) (h : s.locals v = some (.int IntTy.u8 b)) :
    evalExpr Gen.prog 4 s (.bin .eq (some ⟨32, true⟩) (.cast ⟨32, true⟩ (.var v))
      (.const (.int ⟨32, true⟩ 0))) = .ok (boolVal (decide (b = 0))) := by
  simp [evalExpr, h, evalCast, evalBin, isPtr, evalBinInt, binInt, intOf, IntTy.toInt, IntTy.wrap,
    IntTy.modulus, IntTy.u8, Res.bind, Nat.mod_eq_of_lt (show b < 4294967296 by omega)]
  have : ¬ (2147483648 ≤ b) := by omega
  simp only [this, ite_false]
  by_cases hz : b = 0 <;> simp [hz, boolVal]

theorem evColor {v w b ab : Nat} (hb : b < 256) (hab : ab < 256) (h6 : s.locals v = some (.int IntTy.u8 b))
    (h3 : s.locals w = some (.int IntTy.u8 ab)) :
    evalExpr Gen.prog 5 s (.bin .eq (some ⟨32, false⟩) (.bin .band (some ⟨32, false⟩)
      (.cast ⟨32, false⟩ (.var v)) (.const (.int ⟨32, false⟩ 16))) (.cast ⟨32, false⟩ (.var w)))
      = .ok (boolVal (decide (b &&& 16 = ab))) := by
  simp [evalExpr, h6, h3, evalCast, evalBin, isPtr, evalBinInt, binInt, intOf, IntTy.u8, Res.bind,
    IntTy.modulus, Nat.mod_eq_of_lt (show b < 4294967296 by omega),
    Nat.mod_eq_of_lt (show ab < 4294967296 by omega)]

/-- The shift `1 << (b & 15)` as an i32. -/
theorem evShl {v b : Nat} (hb : b < 256) (h6 : s.locals v = some (.int IntTy.u8 b)) :
    evalExpr Gen.prog 4 s (.bin .shl (some ⟨32, true⟩) (.cast ⟨32, true⟩ (.cast ⟨16, false⟩
      (.const (.int ⟨32, false⟩ 1)))) (.bin .band (some ⟨32, false⟩) (.cast ⟨32, false⟩ (.var v))
      (.const (.int ⟨32, false⟩ 15)))) = .ok (.int IntTy.i32 (2 ^ (b &&& 15))) := by
  have hk : b &&& 15 < 16 := Nat.lt_of_le_of_lt Nat.and_le_right (by decide)
  generalize hkk : b &&& 15 = k at hk
  have hpow : 2 ^ k ≤ 32768 := by
    have : 2 ^ k ≤ 2 ^ 15 := Nat.pow_le_pow_right (by decide) (by omega)
    simpa using this
  simp [evalExpr, h6, evalCast, evalBin, isPtr, evalBinInt, binInt, intOf, IntTy.toInt, IntTy.wrap,
    IntTy.modulus, IntTy.u8, IntTy.i32, Res.bind, MiniC.guard, arith, IntTy.inRange, IntTy.minVal,
    IntTy.maxVal, Nat.mod_eq_of_lt (show b < 4294967296 by omega), hkk]
  have hk32 : (k : Int) < 32 := by omega
  have hcast : ((2 : Int) ^ k) = ((2 ^ k : Nat) : Int) := (Int.natCast_pow 2 k).symm
  have hpz0 : (0 : Int) ≤ (2 : Int) ^ k := by rw [hcast]; exact Int.natCast_nonneg _
  rw [if_pos hk32]
  simp only
  rw [if_pos ⟨by omega, by rw [hcast]; omega⟩]
  simp only [Res.ok.injEq, Val.int.injEq, true_and]
  rw [Int.emod_eq_of_lt hpz0 (by rw [hcast]; omega), hcast]; rfl

/-- `(mask[...] & (1 << (b & 15))) != 0`, the mask address given by `a`. -/
theorem evMask {v b mk : Nat} {a : Expr} (blk o : Nat) (hb : b < 256) (hmk : mk < 65536)
    (h6 : s.locals v = some (.int IntTy.u8 b)) (ha : EvE Gen.prog s a (.ptr blk o))
    (hr : readBytes s.mem blk o 2 = .ok (encodeLE 2 mk)) :
    EvE Gen.prog s (.bin .ne (some ⟨32, true⟩) (.bin .band (some ⟨32, true⟩)
      (.cast ⟨32, true⟩ (.load (.int ⟨16, false⟩) a))
      (.bin .shl (some ⟨32, true⟩) (.cast ⟨32, true⟩ (.cast ⟨16, false⟩ (.const (.int ⟨32, false⟩ 1))))
        (.bin .band (some ⟨32, false⟩) (.cast ⟨32, false⟩ (.var v)) (.const (.int ⟨32, false⟩ 15)))))
      (.const (.int ⟨32, true⟩ 0))) (boolVal (decide (mk &&& 2 ^ (b &&& 15) ≠ 0))) := by
  have hdec : decodeLE (encodeLE 2 mk) = mk := by simp [encodeLE, decodeLE]; omega
  have hk : b &&& 15 < 16 := Nat.lt_of_le_of_lt Nat.and_le_right (by decide)
  have hpow : 2 ^ (b &&& 15) ≤ 32768 := by
    have : 2 ^ (b &&& 15) ≤ 2 ^ 15 := Nat.pow_le_pow_right (by decide) (by omega)
    simpa using this
  have hand : mk &&& 2 ^ (b &&& 15) ≤ mk := Nat.and_le_left
  have hload : EvE Gen.prog s (.load (.int ⟨16, false⟩) a) (.int ⟨16, false⟩ mk) :=
    EvE.load ha (by simp [load, Ty.size, IntTy.bytes, hr, hdec])
  have hc : EvE Gen.prog s (.cast ⟨32, true⟩ (.load (.int ⟨16, false⟩) a)) (.int IntTy.i32 mk) :=
    EvE.cast hload (by simp [evalCast, IntTy.modulus, IntTy.i32]; omega)
  have hband := EvE.bin (op := .band) (t := some ⟨32, true⟩) hc (EvE_of_eval (evShl s hb h6))
    (v := .int IntTy.i32 (mk &&& 2 ^ (b &&& 15)))
    (by simp [evalBin, isPtr, evalBinInt, binInt, intOf, IntTy.i32, Res.bind])
  apply EvE.bin hband (EvE.const _)
  simp [evalBin, isPtr, evalBinInt, binInt, intOf, IntTy.i32, IntTy.toInt, IntTy.modulus, Res.bind,
    boolVal, show ¬ (2147483648 ≤ mk &&& 2 ^ (b &&& 15)) by omega]

end exprs


section rayexprs
variable (p : Position) (c : Color) (t : Square) (s : State) (r k : Nat)

/-- The translated tables, through the `*_refine` theorems (stated with a
    variable to keep the big literals out of rewriting). -/
theorem rayLen_G (G : List UInt8) (hG : G = attackRayLengthBytes) (hr : r < 8) :
    (G.getD (t.val * 8 + r) 0).toNat = (ray t (rdir r)).length := by
  rw [hG, rayLen_byte t r hr]
  have := ray_length_le t (rdir r)
  simp [raySquares, UInt8.toNat_ofNat]; omega

theorem raySq_G (G : List UInt8) (hG : G = attackRaysBytes) (hr : r < 8) (hk : k < (ray t (rdir r)).length) :
    (G.getD (t.val * 64 + (r * 8 + k)) 0).toNat = ((ray t (rdir r))[k]).val := by
  rw [hG, raySq_byte t r k hr hk]
  have := ((ray t (rdir r))[k]).isLt
  simp [UInt8.toNat_ofNat]; omega

theorem evRayCond (hr : r < 8) (hk : k < 256)
    (h6 : s.locals 6 = some (.int IntTy.u8 k)) (h1 : s.locals 1 = some (.int IntTy.u8 t.val))
    (h5 : s.locals 5 = some (.int IntTy.u32 r)) (hG : s.mem 8195 = some Gen.global_attack_ray_length) :
    evalExpr Gen.prog 6 s (.bin .lt (some ⟨32, true⟩) (.cast ⟨32, true⟩ (.var 6))
      (.cast ⟨32, true⟩ (.load (.int ⟨8, false⟩) (.index (.index (.const (.ptr 8195 0)) (.var 1) 8)
        (.var 5) 1)))) = .ok (boolVal (decide (k < (ray t (rdir r)).length))) := by
  have ht := t.isLt
  have hrb := readByte hG (t.val * 8 + r) (by rw [G4_len]; omega)
  have hl := rayLen_G t r _ attack_ray_length_refine hr
  have hl8 := ray_length_le t (rdir r)
  simp only [evalExpr, h6, h1, h5, Res.bind_eq, Res.bind_ok, IntTy.u32, IntTy.u8, Bool.false_eq_true,
    ite_false, Res.bind, ptrAddN, hG, G4_len, Nat.zero_add, Nat.mul_one]
  simp only [hG, G4_len, show t.val * 8 ≤ 648 by omega, show t.val * 8 + r ≤ 648 by omega,
    ite_true, Res.bind, load, Ty.size, IntTy.bytes, show (8:Nat) / 8 = 1 by rfl, hrb]
  have hc : (Gen.global_attack_ray_length[t.val * 8 + r]?.getD 0).toNat = (ray t (rdir r)).length := by
    rw [← List.getD_eq_getElem?_getD]; exact hl
  simp [decodeLE, hc, evalCast, evalBin, isPtr, evalBinInt, binInt, intOf, IntTy.toInt, IntTy.wrap,
    IntTy.modulus, boolVal, Nat.mod_eq_of_lt (show k < 4294967296 by omega),
    Nat.mod_eq_of_lt (show (ray t (rdir r)).length < 4294967296 by omega)]
  have a1 : ¬ (2147483648 ≤ k) := by omega
  have a2 : ¬ (2147483648 ≤ (ray t (rdir r)).length) := by omega
  simp only [a1, a2, ite_false]
  by_cases h : k < (ray t (rdir r)).length
  · simp [h, show (k : Int) < (ray t (rdir r)).length by omega]
  · simp [h, show ¬ ((k : Int) < (ray t (rdir r)).length) by omega]

theorem evRayPiece (hr : r < 8) (hk : k < (ray t (rdir r)).length)
    (h0 : s.locals 0 = some (posPtr' posBlock)) (h6 : s.locals 6 = some (.int IntTy.u8 k))
    (h1 : s.locals 1 = some (.int IntTy.u8 t.val)) (h5 : s.locals 5 = some (.int IntTy.u32 r))
    (hm : s.mem posBlock = some (encode p)) (hG : s.mem 8194 = some Gen.global_attack_rays) :
    evalExpr Gen.prog 8 s (.load (.int ⟨8, false⟩) (.index (.field (.var 0) 0)
      (.load (.int ⟨8, false⟩) (.index (.index (.index (.const (.ptr 8194 0)) (.var 1) 64) (.var 5) 8)
        (.var 6) 1)) 1)) = .ok (.int IntTy.u8 (bb p ((ray t (rdir r))[k]).val)) := by
  have ht := t.isLt
  have hl8 := ray_length_le t (rdir r)
  have hrb := readByte hG (t.val * 64 + (r * 8 + k)) (by rw [G3_len]; omega)
  have hsq := raySq_G t r k _ attack_rays_refine hr hk
  have hsqlt := ((ray t (rdir r))[k]).isLt
  have hle := encode_length p
  have hr2 := readBoard hm _ hsqlt
  have hbb : bb p ((ray t (rdir r))[k]).val = (pieceByte (p.pieceAt ⟨_, hsqlt⟩)).toNat := by
    simp [bb, hsqlt]
  simp only [evalExpr, h0, h6, h1, h5, Res.bind_eq, Res.bind_ok, IntTy.u32, IntTy.u8, Bool.false_eq_true,
    ite_false, Res.bind, ptrAddN, hG, G3_len, Nat.zero_add, Nat.mul_one, posPtr', hm, hle]
  simp only [hG, G3_len, show t.val * 64 ≤ 5184 by omega, show t.val * 64 + r * 8 ≤ 5184 by omega,
    show t.val * 64 + r * 8 + k ≤ 5184 by omega, ite_true, Res.bind, load, Ty.size, IntTy.bytes,
    show (8:Nat) / 8 = 1 by rfl, show (0:Nat) ≤ 114 by omega]
  have hrb' : readBytes s.mem 8194 (t.val * 64 + r * 8 + k) 1 =
      .ok [Gen.global_attack_rays.getD (t.val * 64 + (r * 8 + k)) 0] := by
    rw [show t.val * 64 + r * 8 + k = t.val * 64 + (r * 8 + k) by omega]; exact hrb
  simp only [hrb', Res.bind_eq, Res.bind_ok, decodeLE, Nat.mul_zero, Nat.add_zero, hsq, Bool.false_eq_true,
    ite_false, hm, hle, Nat.zero_add, show ((ray t (rdir r))[k]).val ≤ 114 by omega, ite_true,
    Res.bind, load, Ty.size, IntTy.bytes, show (8:Nat) / 8 = 1 by rfl, hr2, Res.pure_eq, ← hbb]

theorem evMaskAddr (hr : r < 8) (h2 : s.locals 2 = some (.int IntTy.u32 c.idx))
    (h1 : s.locals 1 = some (.int IntTy.u8 t.val)) (h5 : s.locals 5 = some (.int IntTy.u32 r))
    (hG : s.mem 8196 = some Gen.global_attack_ray_masks) :
    evalExpr Gen.prog 6 s (.index (.index (.index (.const (.ptr 8196 0)) (.var 2) 1296) (.var 1) 16)
      (.var 5) 2) = .ok (.ptr 8196 (c.idx * 1296 + t.val * 16 + r * 2)) := by
  have hci : c.idx < 2 := by cases c <;> decide
  have ht := t.isLt
  simp only [evalExpr, h2, h1, h5, Res.bind_eq, Res.bind_ok, IntTy.u32, IntTy.u8, Bool.false_eq_true,
    ite_false, Res.bind, ptrAddN, hG, G5_len, Nat.zero_add]
  simp only [hG, G5_len, show c.idx * 1296 ≤ 2592 by omega,
    show c.idx * 1296 + t.val * 16 ≤ 2592 by omega,
    show c.idx * 1296 + t.val * 16 + r * 2 ≤ 2592 by omega, ite_true, Res.bind]

theorem readMask (hr : r < 8) (hG : s.mem 8196 = some Gen.global_attack_ray_masks) :
    readBytes s.mem 8196 (c.idx * 1296 + t.val * 16 + r * 2) 2 = .ok (encodeLE 2 (rayMask c (rdir r))) := by
  have hci : c.idx < 2 := by cases c <;> decide
  have ht := t.isLt
  rw [readByte2 hG _ (by rw [G5_len]; omega)]
  have h := rayMask_bytes c t r hr
  rw [← attack_ray_masks_refine] at h
  rw [h]

end rayexprs

theorem isEmpty_bb (p : Position) (sq : Square) : p.isEmpty sq = decide (bb p sq.val = 0) := by
  simp only [Position.isEmpty, bb, sq.isLt, dite_true]
  cases p.pieceAt sq with
  | none => rfl
  | some pc =>
    obtain ⟨c, t⟩ := pc
    cases c <;> cases t <;> rfl

/-- One ray's verdict from index `k` on: the first occupied square holds a
    slider of `c` for this ray. -/
def rayHitFrom (p : Position) (c : Color) (t : Square) (r k : Nat) : Bool :=
  match firstOcc p ((ray t (rdir r)).drop k) with
  | some sq => match p.pieceAt sq with
    | some pc => pc.color == c && maskHas (rayMask c (rdir r)) pc.type
    | none => false
  | none => false

theorem rayHitFrom_end (p : Position) (c : Color) (t : Square) (r : Nat) :
    rayHitFrom p c t r (ray t (rdir r)).length = false := by
  unfold rayHitFrom; rw [List.drop_eq_nil_of_le (by omega)]; rfl

theorem rayHitFrom_step (p : Position) (c : Color) (t : Square) (r k : Nat)
    (hk : k < (ray t (rdir r)).length) :
    rayHitFrom p c t r k =
      if p.isEmpty ((ray t (rdir r))[k]) then rayHitFrom p c t r (k + 1)
      else match p.pieceAt ((ray t (rdir r))[k]) with
        | some pc => pc.color == c && maskHas (rayMask c (rdir r)) pc.type
        | none => false := by
  unfold rayHitFrom
  rw [List.drop_eq_getElem_cons hk]
  simp only [firstOcc]
  by_cases he : p.isEmpty ((ray t (rdir r))[k]) = true
  · simp only [he, ite_true]
  · simp only [he, Bool.false_eq_true, ite_false]

/-- The inner loop over one ray. -/
theorem ray_loop (p : Position) (c : Color) (t : Square) (r : Nat) (hr : r < 8) :
    ∀ d k (s : State), k + d = (ray t (rdir r)).length →
    s.locals 0 = some (posPtr' posBlock) → s.locals 1 = some (.int IntTy.u8 t.val) →
    s.locals 2 = some (.int IntTy.u32 c.idx) → s.locals 4 = some (.int IntTy.u8 (16 * c.idx)) →
    s.locals 5 = some (.int IntTy.u32 r) → s.locals 6 = some (.int IntTy.u8 k) →
    s.mem posBlock = some (encode p) → s.mem 8194 = some Gen.global_attack_rays →
    s.mem 8195 = some Gen.global_attack_ray_length → s.mem 8196 = some Gen.global_attack_ray_masks →
    if rayHitFrom p c t r k then ∃ s', ExS Gen.prog s Gen.square_attacked_loop0 (.ret (some true8)) s'
    else ∃ s', ExS Gen.prog s Gen.square_attacked_loop0 .normal s' ∧ s'.mem = s.mem ∧
      ∀ i, i ≠ 6 → i ≠ 7 → s'.locals i = s.locals i := by
  have hl8 := ray_length_le t (rdir r)
  have hci : c.idx < 2 := by cases c <;> decide
  intro d
  induction d with
  | zero =>
    intro k s hd h0 h1 h2 h4 h5 h6 hm hG3 hG4 hG5
    have hk : k = (ray t (rdir r)).length := by omega
    subst hk
    rw [rayHitFrom_end]
    simp only [Bool.false_eq_true, ite_false]
    refine ⟨s, ?_, rfl, fun _ _ _ => rfl⟩
    unfold Gen.square_attacked_loop0
    apply ExS.loop_brk
    exact ExS.ite (bc := false) (EvE_of_eval (evRayCond t s r _ hr (by omega) h6 h1 h5 hG4))
      (by simp [truthy_boolVal]) ExS.brk
  | succ d ih =>
    intro k s hd h0 h1 h2 h4 h5 h6 hm hG3 hG4 hG5
    have hk : k < (ray t (rdir r)).length := by omega
    have hcond := EvE_of_eval (evRayCond t s r k hr (by omega) h6 h1 h5 hG4)
    let sq := (ray t (rdir r))[k]
    let b := bb p sq.val
    let s7 : State := { s with locals := s.locals.upd 7 (.int IntTy.u8 b) }
    have hset7 : ExS Gen.prog s (.set 7 (.load (.int ⟨8, false⟩) (.index (.field (.var 0) 0)
        (.load (.int ⟨8, false⟩) (.index (.index (.index (.const (.ptr 8194 0)) (.var 1) 64) (.var 5) 8)
        (.var 6) 1)) 1))) .normal s7 :=
      ExS.set (EvE_of_eval (evRayPiece p t s r k hr hk h0 h6 h1 h5 hm hG3))
    have hb : b < 256 := bb_lt p _
    have h77 : s7.locals 7 = some (.int IntTy.u8 b) := by simp [s7, Locals.upd]
    have heq0 := EvE_of_eval (evEq0 s7 hb h77)
    rw [rayHitFrom_step p c t r k hk]
    by_cases hemp : p.isEmpty ((ray t (rdir r))[k]) = true
    · -- empty square: `continue`
      have hb0 : b = 0 := by rw [isEmpty_bb] at hemp; simpa [b, sq] using hemp
      simp only [hemp, ite_true]
      let s8 : State := { s7 with locals := s7.locals.upd 6 (.int IntTy.u8 (k + 1)) }
      have hbody : ExS Gen.prog s (.ite (.bin .lt (some ⟨32, true⟩) (.cast ⟨32, true⟩ (.var 6))
          (.cast ⟨32, true⟩ (.load (.int ⟨8, false⟩) (.index (.index (.const (.ptr 8195 0)) (.var 1) 8)
          (.var 5) 1)))) (.seq (.set 7 (.load (.int ⟨8, false⟩) (.index (.field (.var 0) 0)
          (.load (.int ⟨8, false⟩) (.index (.index (.index (.const (.ptr 8194 0)) (.var 1) 64) (.var 5) 8)
          (.var 6) 1)) 1))) (.seq (.ite (.bin .eq (some ⟨32, true⟩) (.cast ⟨32, true⟩ (.var 7))
          (.const (.int ⟨32, true⟩ 0))) .cont .skip) (.seq (.ite (.bin .eq (some ⟨32, false⟩) (.bin .band
          (some ⟨32, false⟩) (.cast ⟨32, false⟩ (.var 7)) (.const (.int ⟨32, false⟩ 16)))
          (.cast ⟨32, false⟩ (.var 4))) (.ite (.bin .ne (some ⟨32, true⟩) (.bin .band (some ⟨32, true⟩)
          (.cast ⟨32, true⟩ (.load (.int ⟨16, false⟩) (.index (.index (.index (.const (.ptr 8196 0)) (.var 2)
          1296) (.var 1) 16) (.var 5) 2))) (.bin .shl (some ⟨32, true⟩) (.cast ⟨32, true⟩ (.cast ⟨16, false⟩
          (.const (.int ⟨32, false⟩ 1)))) (.bin .band (some ⟨32, false⟩) (.cast ⟨32, false⟩ (.var 7))
          (.const (.int ⟨32, false⟩ 15))))) (.const (.int ⟨32, true⟩ 0))) (.ret (some (.cast ⟨8, false⟩
          (.bin .ne (some ⟨32, true⟩) (.const (.int ⟨32, true⟩ 1)) (.const (.int ⟨32, true⟩ 0)))))) .skip)
          .skip) .brk))) .brk) .cont s7 := by
        refine ExS.ite (bc := true) hcond (by simp [truthy_boolVal, hk]) ?_
        simp only [ite_true]
        refine ExS.seq hset7 (ExS.seq_cont ?_)
        exact ExS.ite (bc := true) heq0 (by simp [truthy_boolVal, hb0]) ExS.cont
      have hstep : ExS Gen.prog s7 (.set 6 (.cast ⟨8, false⟩ (.bin .add (some ⟨32, true⟩)
          (.cast ⟨32, true⟩ (.var 6)) (.const (.int ⟨32, true⟩ 1))))) .normal s8 :=
        ExS.set (EvE_of_eval (ev_succ s7 k (by omega) (by simp [s7, Locals.upd, h6])))
      have ihs := ih (k + 1) s8 (by omega) (by simp [s8, s7, Locals.upd, h0])
        (by simp [s8, s7, Locals.upd, h1]) (by simp [s8, s7, Locals.upd, h2])
        (by simp [s8, s7, Locals.upd, h4]) (by simp [s8, s7, Locals.upd, h5]) (by simp [s8, Locals.upd])
        hm hG3 hG4 hG5
      split at ihs
      · rename_i hh; rw [if_pos hh]; obtain ⟨s', hs'⟩ := ihs
        exact ⟨s', ExS.loop_next hbody (Or.inr rfl) hstep hs'⟩
      · rename_i hh; rw [if_neg hh]; obtain ⟨s', hs', hmem, hloc⟩ := ihs
        refine ⟨s', ExS.loop_next hbody (Or.inr rfl) hstep hs', hmem, fun i h6' h7' => ?_⟩
        rw [hloc i h6' h7']
        simp [s8, s7, Locals.upd, h6', h7']
    · -- occupied square: test, then `break`
      have hb0 : b ≠ 0 := by rw [isEmpty_bb] at hemp; simpa [b, sq] using hemp
      simp only [hemp, Bool.false_eq_true, ite_false]
      have hcol := EvE_of_eval (evColor s7 (v := 7) (w := 4) hb (show 16 * c.idx < 256 by omega) h77
        (by simp [s7, Locals.upd, h4]))
      have hmask := evMask s7 (v := 7) 8196 (c.idx * 1296 + t.val * 16 + r * 2) hb
        (rayMask_lt c r hr) h77
        (EvE_of_eval (evMaskAddr c t s7 r hr (by simp [s7, Locals.upd, h2]) (by simp [s7, Locals.upd, h1])
          (by simp [s7, Locals.upd, h5]) hG5)) (readMask c t s7 r hr hG5)
      have hval : (decide (b &&& 16 = 16 * c.idx) && decide (rayMask c (rdir r) &&& 2 ^ (b &&& 15) ≠ 0)) =
          (match p.pieceAt ((ray t (rdir r))[k]) with
            | some pc => pc.color == c && maskHas (rayMask c (rdir r)) pc.type
            | none => false) := by
        have hsq := ((ray t (rdir r))[k]).isLt
        have hbb : b = (pieceByte (p.pieceAt (ray t (rdir r))[k])).toNat := by simp [b, sq, bb, hsq]
        have := condVal_hit (p.pieceAt (ray t (rdir r))[k]) c (rayMask c (rdir r))
        unfold condVal at this
        rw [← hbb] at this
        simp only [hb0, decide_false, Bool.not_false, decide_true, Bool.true_and,
          show decide (b ≠ 0) = true by simp [hb0]] at this
        exact this
      have hpre : ExS Gen.prog s (.seq (.set 7 (.load (.int ⟨8, false⟩) (.index (.field (.var 0) 0)
          (.load (.int ⟨8, false⟩) (.index (.index (.index (.const (.ptr 8194 0)) (.var 1) 64) (.var 5) 8)
          (.var 6) 1)) 1))) (.ite (.bin .eq (some ⟨32, true⟩) (.cast ⟨32, true⟩ (.var 7))
          (.const (.int ⟨32, true⟩ 0))) .cont .skip)) .normal s7 :=
        ExS.seq hset7 (ExS.ite (bc := false) heq0 (by simp [truthy_boolVal, hb0]) ExS.skip)
      have hite0 : ExS Gen.prog s7 (.ite (.bin .eq (some ⟨32, true⟩) (.cast ⟨32, true⟩ (.var 7))
          (.const (.int ⟨32, true⟩ 0))) .cont .skip) .normal s7 :=
        ExS.ite (bc := false) heq0 (by simp [truthy_boolVal, hb0]) ExS.skip
      rw [← hval]
      by_cases hc1 : b &&& 16 = 16 * c.idx
      · by_cases hc2 : rayMask c (rdir r) &&& 2 ^ (b &&& 15) ≠ 0
        · simp only [hc1, hc2, decide_true, Bool.and_self, ite_true, ne_eq, not_false_eq_true]
          refine ⟨s7, ?_⟩
          unfold Gen.square_attacked_loop0
          apply ExS.loop_ret
          refine ExS.ite (bc := true) hcond (by simp [truthy_boolVal, hk]) ?_
          simp only [ite_true]
          refine ExS.seq hset7 (ExS.seq hite0 (ExS.seq_ret ?_))
          refine ExS.ite (bc := true) hcol (by simp [truthy_boolVal, hc1]) ?_
          simp only [ite_true]
          refine ExS.ite (bc := true) hmask (by simp [truthy_boolVal, hc2]) ?_
          exact ExS.ret (EvE_of_eval (ev_true8 _))
        · have hc2' : rayMask c (rdir r) &&& 2 ^ (b &&& 15) = 0 := by simpa using hc2
          simp only [hc1, hc2', decide_true, ne_eq, not_true_eq_false, decide_false, Bool.and_false,
            Bool.false_eq_true, ite_false]
          refine ⟨s7, ?_, rfl, fun i _ h7' => by simp [s7, Locals.upd, h7']⟩
          unfold Gen.square_attacked_loop0
          apply ExS.loop_brk
          refine ExS.ite (bc := true) hcond (by simp [truthy_boolVal, hk]) ?_
          simp only [ite_true]
          refine ExS.seq hset7 (ExS.seq hite0 (ExS.seq ?_ ExS.brk))
          refine ExS.ite (bc := true) hcol (by simp [truthy_boolVal, hc1]) ?_
          simp only [ite_true]
          exact ExS.ite (bc := false) hmask (by simp [truthy_boolVal, hc2']) ExS.skip
      · simp only [hc1, decide_false, Bool.false_and, Bool.false_eq_true, ite_false]
        refine ⟨s7, ?_, rfl, fun i _ h7' => by simp [s7, Locals.upd, h7']⟩
        unfold Gen.square_attacked_loop0
        apply ExS.loop_brk
        refine ExS.ite (bc := true) hcond (by simp [truthy_boolVal, hk]) ?_
        simp only [ite_true]
        refine ExS.seq hset7 (ExS.seq hite0 (ExS.seq ?_ ExS.brk))
        exact ExS.ite (bc := false) hcol (by simp [truthy_boolVal, hc1]) ExS.skip

/-- Rays `r, r+1, …, 7`: some first occupied square holds a matching slider. -/
def raysFrom (p : Position) (c : Color) (t : Square) (r : Nat) : Bool :=
  ((List.range 8).drop r).any fun r' => rayHitFrom p c t r' 0

theorem raysFrom_step (p : Position) (c : Color) (t : Square) (r : Nat) (hr : r < 8) :
    raysFrom p c t r = (rayHitFrom p c t r 0 || raysFrom p c t (r + 1)) := by
  unfold raysFrom
  rw [List.drop_eq_getElem_cons (by simpa using hr)]
  simp

theorem raysFrom_end (p : Position) (c : Color) (t : Square) : raysFrom p c t 8 = false := by
  unfold raysFrom; rfl

theorem rayDirs_eq : rayDirs = (List.range 8).map rdir := by decide

theorem raysFrom_zero (p : Position) (c : Color) (t : Square) :
    raysFrom p c t 0 = rayAttacked p t c := by
  unfold raysFrom rayAttacked rayHitFrom
  rw [rayDirs_eq, List.any_map]
  rfl

theorem evOuterCond (s : State) (r : Nat) (hr : r < 4294967296) (h5 : s.locals 5 = some (.int IntTy.u32 r)) :
    evalExpr Gen.prog 4 s (.bin .lt (some ⟨32, false⟩) (.var 5) (.cast ⟨32, false⟩ (.const (.int ⟨32, true⟩ 8))))
      = .ok (boolVal (decide (r < 8))) := by
  simp [evalExpr, h5, evalCast, evalBin, isPtr, evalBinInt, binInt, intOf, IntTy.u32, IntTy.wrap,
    IntTy.modulus, IntTy.toInt, Res.bind]

theorem evOuterStep (s : State) (r : Nat) (hr : r < 8) (h5 : s.locals 5 = some (.int IntTy.u32 r)) :
    evalExpr Gen.prog 4 s (.cast ⟨32, false⟩ (.bin .add (some ⟨32, false⟩) (.cast ⟨32, false⟩ (.var 5))
      (.const (.int ⟨32, false⟩ 1)))) = .ok (.int IntTy.u32 (r + 1)) := by
  simp [evalExpr, h5, evalCast, evalBin, isPtr, evalBinInt, binInt, intOf, IntTy.u32, IntTy.modulus,
    Res.bind, Nat.mod_eq_of_lt (show r < 4294967296 by omega), Nat.mod_eq_of_lt (show r + 1 < 4294967296 by omega)]

/-- The outer loop over the 8 rays. -/
theorem rays_loop (p : Position) (c : Color) (t : Square) :
    ∀ d r (s : State), r + d = 8 →
    s.locals 0 = some (posPtr' posBlock) → s.locals 1 = some (.int IntTy.u8 t.val) →
    s.locals 2 = some (.int IntTy.u32 c.idx) → s.locals 4 = some (.int IntTy.u8 (16 * c.idx)) →
    s.locals 5 = some (.int IntTy.u32 r) →
    s.mem posBlock = some (encode p) → s.mem 8194 = some Gen.global_attack_rays →
    s.mem 8195 = some Gen.global_attack_ray_length → s.mem 8196 = some Gen.global_attack_ray_masks →
    if raysFrom p c t r then ∃ s', ExS Gen.prog s Gen.square_attacked_loop1 (.ret (some true8)) s'
    else ∃ s', ExS Gen.prog s Gen.square_attacked_loop1 .normal s' := by
  intro d
  induction d with
  | zero =>
    intro r s hd h0 h1 h2 h4 h5 hm hG3 hG4 hG5
    have : r = 8 := by omega
    subst this
    rw [raysFrom_end]
    simp only [Bool.false_eq_true, ite_false]
    refine ⟨s, ?_⟩
    unfold Gen.square_attacked_loop1
    apply ExS.loop_brk
    exact ExS.ite (bc := false) (EvE_of_eval (evOuterCond s 8 (by decide) h5)) (by rfl) ExS.brk
  | succ d ih =>
    intro r s hd h0 h1 h2 h4 h5 hm hG3 hG4 hG5
    have hr : r < 8 := by omega
    have hcond := EvE_of_eval (evOuterCond s r (by omega) h5)
    let s6 : State := { s with locals := s.locals.upd 6 (.int IntTy.u8 0) }
    have hset6 : ExS Gen.prog s (.set 6 (.cast ⟨8, false⟩ (.const (.int ⟨32, true⟩ 0)))) .normal s6 :=
      ExS.set (EvE_of_eval (n := 3) rfl)
    have hin := ray_loop p c t r hr (ray t (rdir r)).length 0 s6 (by omega)
      (by simp [s6, Locals.upd, h0]) (by simp [s6, Locals.upd, h1]) (by simp [s6, Locals.upd, h2])
      (by simp [s6, Locals.upd, h4]) (by simp [s6, Locals.upd, h5]) (by simp [s6, Locals.upd]) hm hG3 hG4 hG5
    rw [raysFrom_step p c t r hr]
    split at hin
    · rename_i hh
      simp only [hh, Bool.true_or, ite_true]
      obtain ⟨s', hs'⟩ := hin
      refine ⟨s', ?_⟩
      unfold Gen.square_attacked_loop1
      apply ExS.loop_ret
      refine ExS.ite (bc := true) hcond (by simp [truthy_boolVal, hr]) ?_
      exact ExS.seq hset6 hs'
    · rename_i hh
      simp only [Bool.not_eq_true] at hh
      simp only [hh, Bool.false_or]
      obtain ⟨s', hs', hmem, hloc⟩ := hin
      have hl : ∀ i, i ≠ 6 → i ≠ 7 → s'.locals i = s.locals i := fun i a b => by
        rw [hloc i a b]; simp [s6, Locals.upd, a]
      let s7 : State := { s' with locals := s'.locals.upd 5 (.int IntTy.u32 (r + 1)) }
      have hstep : ExS Gen.prog s' (.set 5 (.cast ⟨32, false⟩ (.bin .add (some ⟨32, false⟩)
          (.cast ⟨32, false⟩ (.var 5)) (.const (.int ⟨32, false⟩ 1))))) .normal s7 :=
        ExS.set (EvE_of_eval (evOuterStep s' r hr (by rw [hl 5 (by decide) (by decide)]; exact h5)))
      have hm7 : s7.mem = s.mem := hmem
      have ihs := ih (r + 1) s7 (by omega)
        (by simp [s7, Locals.upd]; rw [hl 0 (by decide) (by decide)]; exact h0)
        (by simp [s7, Locals.upd]; rw [hl 1 (by decide) (by decide)]; exact h1)
        (by simp [s7, Locals.upd]; rw [hl 2 (by decide) (by decide)]; exact h2)
        (by simp [s7, Locals.upd]; rw [hl 4 (by decide) (by decide)]; exact h4)
        (by simp [s7, Locals.upd]) (by rw [hm7]; exact hm) (by rw [hm7]; exact hG3)
        (by rw [hm7]; exact hG4) (by rw [hm7]; exact hG5)
      have hbody : ExS Gen.prog s (.ite (.bin .lt (some ⟨32, false⟩) (.var 5) (.cast ⟨32, false⟩
          (.const (.int ⟨32, true⟩ 8)))) (.seq (.set 6 (.cast ⟨8, false⟩ (.const (.int ⟨32, true⟩ 0))))
          Gen.square_attacked_loop0) .brk) .normal s' :=
        ExS.ite (bc := true) hcond (by simp [truthy_boolVal, hr]) (ExS.seq hset6 hs')
      split at ihs
      · rename_i hh2; rw [if_pos hh2]; obtain ⟨s'', hs''⟩ := ihs
        exact ⟨s'', ExS.loop_next hbody (Or.inl rfl) hstep hs''⟩
      · rename_i hh2; rw [if_neg hh2]; obtain ⟨s'', hs''⟩ := ihs
        exact ⟨s'', ExS.loop_next hbody (Or.inl rfl) hstep hs''⟩

theorem stepAttacked_eqS (p : Position) (t : Square) (c : Color) :
    stepAttacked p t c = stepAttackedS p t c := rfl

/-- **`square_attacked` refines the spec's `attacked`.** For every position
    (in the memory with the translated tables), target square and attacker:
    no UB, terminates, and returns 1 iff the spec says `c` attacks `t`. -/
theorem square_attacked_refines (p : Position) (t : Square) (c : Color) (m : Mem)
    (hm : m posBlock = some (encode p))
    (hG1 : m 8192 = some Gen.global_step_attack_probes) (hG2 : m 8193 = some Gen.global_step_attack_probe_count)
    (hG3 : m 8194 = some Gen.global_attack_rays) (hG4 : m 8195 = some Gen.global_attack_ray_length)
    (hG5 : m 8196 = some Gen.global_attack_ray_masks) :
    ∃ s', ExS Gen.prog ⟨frameLocals Gen.square_attacked.params
        [posPtr' posBlock, .int IntTy.u8 t.val, .int IntTy.u32 c.idx], m, false⟩
      Gen.square_attacked.body (.ret (some (if p.attacked t c then true8 else false8))) s' ∧ s'.mem = m := by
  have hci : c.idx < 2 := by cases c <;> decide
  let L0 := frameLocals Gen.square_attacked.params [posPtr' posBlock, .int IntTy.u8 t.val, .int IntTy.u32 c.idx]
  let s0 : State := ⟨L0, m, false⟩
  obtain ⟨ss, hss, hssm⟩ := step_square_attacked_refines p t c m hm hG1 hG2
  let v3 := if stepAttacked p t c then true8 else false8
  let s1 : State := { s0 with mem := ss.mem, locals := s0.locals.upd 3 v3 }
  have hcall : ExS Gen.prog s0 (.call (some 3) 16 [(.var 0), (.var 1), (.var 2)]) .normal s1 :=
    ExS.call_dst (EvArgs_of_eval (n := 4) rfl) rfl rfl hss
  have hs1m : s1.mem = m := hssm
  rw [attacked_eq, ← stepAttacked_eqS]
  unfold Gen.square_attacked
  simp only
  by_cases hst : stepAttacked p t c = true
  · simp only [hst, Bool.true_or, ite_true]
    refine ⟨s1, ExS.seq_ret (ExS.seq hcall ?_), hs1m⟩
    refine ExS.ite (vc := v3) (bc := true) (EvE_of_eval (n := 2) (by simp [evalExpr, s1, Locals.upd]))
      (by simp [v3, hst, true8]; rfl) ?_
    exact ExS.ret (EvE_of_eval (ev_true8 _))
  · simp only [Bool.not_eq_true] at hst
    simp only [hst, Bool.false_or]
    have hite : ExS Gen.prog s1 (.ite (.var 3) (.ret (some (.cast ⟨8, false⟩ (.bin .ne (some ⟨32, true⟩)
        (.const (.int ⟨32, true⟩ 1)) (.const (.int ⟨32, true⟩ 0)))))) .skip) .normal s1 :=
      ExS.ite (vc := v3) (bc := false) (EvE_of_eval (n := 2) (by simp [evalExpr, s1, Locals.upd]))
        (by simp [v3, hst, false8]; rfl) ExS.skip
    let s2 : State := { s1 with locals := s1.locals.upd 4 (.int IntTy.u8 (16 * c.idx)) }
    have hset4 : ExS Gen.prog s1 (.set 4 (.cast ⟨8, false⟩ (.bin .shl (some ⟨32, false⟩)
        (.cast ⟨32, false⟩ (.var 2)) (.const (.int ⟨32, true⟩ 4))))) .normal s2 := by
      apply ExS.set; apply EvE_of_eval (n := 4); cases c <;> rfl
    let s3 : State := { s2 with locals := s2.locals.upd 5 (.int IntTy.u32 0) }
    have hset5 : ExS Gen.prog s2 (.set 5 (.cast ⟨32, false⟩ (.const (.int ⟨32, true⟩ 0)))) .normal s3 :=
      ExS.set (EvE_of_eval (n := 3) rfl)
    have hloop := rays_loop p c t 8 0 s3 (by omega) (by simp [s3, s2, s1, s0, L0, Locals.upd]; rfl)
      (by simp [s3, s2, s1, s0, L0, Locals.upd]; rfl) (by simp [s3, s2, s1, s0, L0, Locals.upd]; rfl)
      (by simp [s3, s2, Locals.upd]) (by simp [s3, Locals.upd])
      (by rw [show s3.mem = m from hs1m]; exact hm) (by rw [show s3.mem = m from hs1m]; exact hG3)
      (by rw [show s3.mem = m from hs1m]; exact hG4) (by rw [show s3.mem = m from hs1m]; exact hG5)
    rw [raysFrom_zero] at hloop
    split
    · rename_i hr
      rw [if_pos hr] at hloop
      obtain ⟨s', hs'⟩ := hloop
      have hw := (ExS_noWrite (by decide) hs').1
      exact ⟨s', ExS.seq (ExS.seq hcall hite) (ExS.seq hset4 (ExS.seq_ret (ExS.seq hset5 hs'))), by rw [hw]; exact hs1m⟩
    · rename_i hr
      rw [if_neg hr] at hloop
      obtain ⟨s', hs'⟩ := hloop
      have hw := (ExS_noWrite (by decide) hs').1
      exact ⟨s', ExS.seq (ExS.seq hcall hite) (ExS.seq hset4 (ExS.seq (ExS.seq hset5 hs')
        (ExS.ret (EvE_of_eval (n := 5) rfl)))), by rw [hw]; exact hs1m⟩

end Shogi.C.Proofs
