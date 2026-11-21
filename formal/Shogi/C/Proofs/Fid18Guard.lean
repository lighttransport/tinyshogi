import Shogi.C.Proofs.Fid18Spec
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false
namespace Shogi.C.Proofs
open MiniC Shogi Shogi.C

def pieceAttacksSpec (p : Position) (f t : Square) : Bool :=
  f != t && match p.pieceAt f with
  | none => false
  | some pc => (p.attackSquares f pc).contains t

-- helper: frame-state equality for fid15 call
theorem frame15 (m : Mem) (code : Nat) (dr dc fwd : Int) :
    (⟨frameLocals Gen.step_piece_attacks.params [u32 code, i32 dr, i32 dc, i32 fwd], m, false⟩ : State) =
    s15s m code dr dc fwd := by
  congr 1
  funext i
  have hi : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ 4 ≤ i := by omega
  rcases hi with rfl | rfl | rfl | rfl | hge
  · simp [frameLocals, s15s, Gen.step_piece_attacks, List.idxOf?, List.findIdx?, List.findIdx?.go]
  · simp [frameLocals, s15s, Gen.step_piece_attacks, List.idxOf?, List.findIdx?, List.findIdx?.go]
  · simp [frameLocals, s15s, Gen.step_piece_attacks, List.idxOf?, List.findIdx?, List.findIdx?.go]
  · simp [frameLocals, s15s, Gen.step_piece_attacks, List.idxOf?, List.findIdx?, List.findIdx?.go]
  · simp [frameLocals, s15s, Gen.step_piece_attacks, List.idxOf?, List.findIdx?, List.findIdx?.go,
      show i ≠ 0 by omega, show i ≠ 1 by omega, show i ≠ 2 by omega, show i ≠ 3 by omega,
      show 0 ≠ i by omega, show 1 ≠ i by omega, show 2 ≠ i by omega, show 3 ≠ i by omega]


theorem cast_i32_u8_of_fin (v : Fin 81) : evalCast ⟨32,true⟩ (u8 v.val) = .ok (i32 (v.val : Int)) := by
  simp [evalCast, u8, i32, IntTy.i32, IntTy.u8, IntTy.modulus, IntTy.wrap,
    Nat.mod_eq_of_lt (show v.val < 4294967296 by omega)]
  have h1 : (v.val : Int) % (4294967296 : Int) = v.val := by
    exact Int.emod_eq_of_lt (by omega) (by omega)
  rw [h1]
  simp

theorem ev_cast_local {s : State} {i : Nat} (v : Fin 81) (hi : s.locals i = some (u8 v.val)) :
    EvE Gen.prog s (.cast ⟨32,true⟩ (.var i)) (i32 (v.val : Int)) := by
  apply EvE_of_eval (n := 3)
  simp [evalExpr, hi, cast_i32_u8_of_fin v]

theorem guard_ev (p : Position) (f t : Square) (m : Mem) :
    let s0 : State := ⟨frameLocals Gen.shogi_piece_attacks_square.params
      [posPtr' posBlock, u8 f.val, u8 t.val], m, false⟩
    EvE Gen.prog s0
      (.lor (.lor (.lor (.bin .eq none (.var 0) (.const .null))
                         (.bin .ge (some ⟨32, true⟩) (.cast ⟨32, true⟩ (.var 1)) (.const (.int ⟨32, true⟩ 81))))
                (.bin .ge (some ⟨32, true⟩) (.cast ⟨32, true⟩ (.var 2)) (.const (.int ⟨32, true⟩ 81))))
          (.bin .eq (some ⟨32, true⟩) (.cast ⟨32, true⟩ (.var 1)) (.cast ⟨32, true⟩ (.var 2))))
      (boolVal (f = t)) := by
  dsimp only
  let s0 : State := ⟨frameLocals Gen.shogi_piece_attacks_square.params
      [posPtr' posBlock, u8 f.val, u8 t.val], m, false⟩
  have hl1 : s0.locals 1 = some (u8 f.val) := by simp [s0, frameLocals, Gen.shogi_piece_attacks_square, List.idxOf?, List.findIdx?, List.findIdx?.go]
  have hl2 : s0.locals 2 = some (u8 t.val) := by simp [s0, frameLocals, Gen.shogi_piece_attacks_square, List.idxOf?, List.findIdx?, List.findIdx?.go]
  have hl0 : s0.locals 0 = some (posPtr' posBlock) := by simp [s0, frameLocals, Gen.shogi_piece_attacks_square, List.idxOf?, List.findIdx?, List.findIdx?.go]
  have hc1 := ev_cast_local f hl1
  have hc2 := ev_cast_local t hl2
  have hnull : EvE Gen.prog s0 (.bin .eq none (.var 0) (.const .null)) (boolVal false) := by
    refine EvE.bin (EvE.var hl0) (EvE.const Val.null) ?_
    simp [evalBin, isPtr, posPtr', MiniC.ptrEq]
  have hge1 : EvE Gen.prog s0 (.bin .ge (some ⟨32,true⟩) (.cast ⟨32,true⟩ (.var 1)) (.const (.int ⟨32,true⟩ 81))) (boolVal false) := by
    refine EvE.bin hc1 (EvE.const (.int ⟨32,true⟩ 81)) ?_
    simp [evalBin, isPtr, evalBinInt, binInt, intOf, i32, IntTy.i32, Res.bind,
      toInt_wrap32 (f.val : Int) (by omega) (by omega), show IntTy.toInt ⟨32,true⟩ 81 = 81 by simp [IntTy.toInt, IntTy.modulus], show ¬(81 ≤ (f.val : Int)) by omega]
  have hge2 : EvE Gen.prog s0 (.bin .ge (some ⟨32,true⟩) (.cast ⟨32,true⟩ (.var 2)) (.const (.int ⟨32,true⟩ 81))) (boolVal false) := by
    refine EvE.bin hc2 (EvE.const (.int ⟨32,true⟩ 81)) ?_
    simp [evalBin, isPtr, evalBinInt, binInt, intOf, i32, IntTy.i32, Res.bind,
      toInt_wrap32 (t.val : Int) (by omega) (by omega), show IntTy.toInt ⟨32,true⟩ 81 = 81 by simp [IntTy.toInt, IntTy.modulus], show ¬(81 ≤ (t.val : Int)) by omega]
  have heq : EvE Gen.prog s0 (.bin .eq (some ⟨32,true⟩) (.cast ⟨32,true⟩ (.var 1)) (.cast ⟨32,true⟩ (.var 2)))
      (boolVal (f = t)) := by
    refine EvE.bin hc1 hc2 ?_
    by_cases hft : f = t
    · subst hft
      simp [evalBin, isPtr, evalBinInt, binInt, intOf, i32, IntTy.i32, Res.bind,
        toInt_wrap32 (f.val : Int) (by omega) (by omega)]
    · have hv : f.val ≠ t.val := by intro h; exact hft (Fin.ext h)
      have hvf : (f.val : Int) ≠ (t.val : Int) := by intro h; apply hv; omega
      simp [evalBin, isPtr, evalBinInt, binInt, intOf, i32, IntTy.i32, Res.bind,
        toInt_wrap32 (f.val : Int) (by omega) (by omega),
        toInt_wrap32 (t.val : Int) (by omega) (by omega), hv, hvf, hft]
  have h3 := EvE.lor_false hnull (by rfl) hge1 (by rfl)
  have h2 := EvE.lor_false h3 (by rfl) hge2 (by rfl)
  exact EvE.lor_false h2 (by rfl) heq (truthy_boolVal (f = t))


end Shogi.C.Proofs
