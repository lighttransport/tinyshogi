import Shogi.C.Proofs.Fid18GeomAux
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false
namespace Shogi.C.Proofs
open MiniC Shogi Shogi.C

theorem eve_u8_of_sig {s : State} {e : Expr} {N k : Nat}
    (h : evalSig (evalExpr Gen.prog N s e) = some (IntTy.u8, k)) :
    EvE Gen.prog s e (u8 k) := by
  apply EvE_of_eval (n := N)
  cases he : evalExpr Gen.prog N s e with
  | ok v =>
    cases v with
    | int t n =>
      simp [evalSig, he] at h
      rcases h with ⟨rfl, rfl⟩
      rfl
    | ptr b o => simp [evalSig, he] at h
    | null => simp [evalSig, he] at h
    | f64 x => simp [evalSig, he] at h
  | ub => simp [evalSig, he] at h
  | timeout => simp [evalSig, he] at h

theorem eve_i32_of_sig {s : State} {e : Expr} {N k : Nat} (hk : k < 2147483648)
    (h : evalSig (evalExpr Gen.prog N s e) = some (IntTy.i32, k)) :
    EvE Gen.prog s e (i32 (k : Int)) := by
  apply EvE_of_eval (n := N)
  cases he : evalExpr Gen.prog N s e with
  | ok v =>
    cases v with
    | int t n =>
      simp [evalSig, he] at h
      rcases h with ⟨rfl, rfl⟩
      have hmod : ((n : Int) % (4294967296 : Int)).toNat = n := by
        rw [Int.emod_eq_of_lt (a := (n : Int)) (b := (4294967296 : Int)) (by omega) (by omega)]
        simp
      simpa [i32, IntTy.wrap, IntTy.modulus, IntTy.i32] using hmod.symm
    | ptr b o => simp [evalSig, he] at h
    | null => simp [evalSig, he] at h
    | f64 x => simp [evalSig, he] at h
  | ub => simp [evalSig, he] at h
  | timeout => simp [evalSig, he] at h

theorem shogi_piece_attacks_square_spec (p : Position) (f t : Square) (m : Mem)
    (hm : m posBlock = some (encode p)) :
    ∃ s', ExS Gen.prog
      ⟨frameLocals Gen.shogi_piece_attacks_square.params
        [posPtr' posBlock, u8 f.val, u8 t.val], m, false⟩
      Gen.shogi_piece_attacks_square.body
      (.ret (some (if pieceAttacksSpec p f t then true8 else false8))) s' ∧ s'.mem = m := by
  let s0 : State := ⟨frameLocals Gen.shogi_piece_attacks_square.params
      [posPtr' posBlock, u8 f.val, u8 t.val], m, false⟩
  by_cases hft : f = t
  · subst hft
    refine ⟨s0, ?_, ?_⟩
    · have hg := guard_ev p f f m
      dsimp at hg
      refine ExS.seq_ret ?_
      refine ExS.ite (bc := true) hg (by simp [truthy_boolVal]) ?_
      apply ExS.ret
      apply EvE_of_eval (n := 3)
      have hp : pieceAttacksSpec p f f = false := by simp [pieceAttacksSpec]
      simp [evalExpr, evalBin, evalCast, false8, boolVal, IntTy.i32, IntTy.u8, IntTy.toInt,
        isPtr, evalBinInt, binInt, intOf, Res.bind, hp, IntTy.wrap]
    · simp [s0]
  · have hg := guard_ev p f t m
    dsimp at hg
    have hgf : EvE Gen.prog s0
        (.lor (.lor (.lor (.bin .eq none (.var 0) (.const .null))
                           (.bin .ge (some ⟨32, true⟩) (.cast ⟨32, true⟩ (.var 1)) (.const (.int ⟨32, true⟩ 81))))
                  (.bin .ge (some ⟨32, true⟩) (.cast ⟨32, true⟩ (.var 2)) (.const (.int ⟨32, true⟩ 81))))
            (.bin .eq (some ⟨32, true⟩) (.cast ⟨32, true⟩ (.var 1)) (.cast ⟨32, true⟩ (.var 2))))
        (boolVal false) := by simpa [hft] using hg
    have hskip : ExS Gen.prog s0
        (.ite (.lor (.lor (.lor (.bin .eq none (.var 0) (.const .null))
                           (.bin .ge (some ⟨32, true⟩) (.cast ⟨32, true⟩ (.var 1)) (.const (.int ⟨32, true⟩ 81))))
                  (.bin .ge (some ⟨32, true⟩) (.cast ⟨32, true⟩ (.var 2)) (.const (.int ⟨32, true⟩ 81))))
            (.bin .eq (some ⟨32, true⟩) (.cast ⟨32, true⟩ (.var 1)) (.cast ⟨32, true⟩ (.var 2))))
          (.ret (some (.cast ⟨8, false⟩ (.bin .ne (some ⟨32, true⟩) (.const (.int ⟨32, true⟩ 0)) (.const (.int ⟨32, true⟩ 0)))))) .skip)
        .normal s0 := by
      refine ExS.ite (bc := false) hgf (by simp [truthy_boolVal]) ?_
      exact ExS.skip
    -- piece load at f
    have hl0 : s0.locals 0 = some (posPtr' posBlock) := by simp [s0, frameLocals, Gen.shogi_piece_attacks_square, List.idxOf?, List.findIdx?, List.findIdx?.go]
    have hl1 : s0.locals 1 = some (u8 f.val) := by simp [s0, frameLocals, Gen.shogi_piece_attacks_square, List.idxOf?, List.findIdx?, List.findIdx?.go]
    let b : Nat := (pieceByte (p.pieceAt f)).toNat
    have hbsmall : b < 256 := by exact UInt8.toNat_lt _
    let s3 : State := {s0 with locals := s0.locals.upd 3 (u8 b)}
    have hload : EvE Gen.prog s0
        (.load (.int ⟨8, false⟩) (.index (.field (.var 0) 0) (.var 1) 1)) (u8 b) := by
      have hlen : (encode p).length = 114 := encode_length p
      refine EvE.load (pa := .ptr posBlock f.val) (EvE.index (pb := .ptr posBlock (0+0)) (r := .ptr posBlock f.val)
        (EvE.field (EvE.var (v := posPtr' posBlock) hl0) (by simp [ptrAddN, posPtr', s0, hm, hlen]))
        (EvE.var (v := u8 f.val) hl1) ?_) ?_
      · have hf81 : f.val ≤ 114 := by omega
        simp [IntTy.u8, ptrAddN, hm, hlen, IntTy.toInt, s0, hf81]
      · simp only [load, Ty.size, IntTy.bytes, show (8:Nat)/8 = 1 by rfl]
        rw [readBoard hm f.val f.isLt]
        simp [decodeLE, Res.bind, b, u8, IntTy.u8]
    have hset3 : ExS Gen.prog s0 (.set 3 (.load (.int ⟨8,false⟩) (.index (.field (.var 0) 0) (.var 1) 1))) .normal s3 :=
      ExS.set hload
    have hcond3 : EvE Gen.prog s3
        (.bin .eq (some ⟨32,true⟩) (.cast ⟨32,true⟩ (.var 3)) (.const (.int ⟨32,true⟩ 0)))
        (boolVal (p.pieceAt f = none)) := by
      have hc3 : EvE Gen.prog s3 (.cast ⟨32,true⟩ (.var 3)) (i32 (b : Int)) := by
        apply EvE_of_eval (n := 3)
        simp [evalExpr, s3, Locals.upd, evalCast, i32, u8, IntTy.i32, IntTy.u8, IntTy.modulus,
          IntTy.wrap, Nat.mod_eq_of_lt (show b < 4294967296 by omega)]
        have h1 : (b : Int) % (4294967296 : Int) = b := Int.emod_eq_of_lt (by omega) (by omega)
        rw [h1]
        simp
      refine EvE.bin hc3 (EvE.const (.int ⟨32,true⟩ 0)) ?_
      have hbval : b = (pieceByte (p.pieceAt f)).toNat := rfl
      have hsmall : (b : Int) < 2147483648 := by omega
      have hb0 : (b = 0) ↔ p.pieceAt f = none := by
        rw [hbval, pieceByte_toNat]
        cases hpf : p.pieceAt f with
        | none => simp
        | some q =>
          simp [piece_code_ne_zero q]
      by_cases hb : b = 0
      · have hp : p.pieceAt f = none := hb0.mp hb
        simp [evalBin, isPtr, evalBinInt, binInt, intOf, i32, IntTy.i32, Res.bind,
          toInt_wrap32 (b : Int) (by omega) (by omega), hb, hp, IntTy.wrap, IntTy.modulus]
      · have hp : p.pieceAt f ≠ none := by intro h; exact hb (hb0.mpr h)
        have hbz : b ≠ 0 := hb
        simp [evalBin, isPtr, evalBinInt, binInt, intOf, i32, IntTy.i32, Res.bind,
          toInt_wrap32 (b : Int) (by omega) (by omega), hbz, hp, IntTy.wrap, IntTy.modulus,
          show b % 4294967296 = b by omega, show (b : Int) % 4294967296 = b by omega,
          show IntTy.toInt ⟨32,true⟩ b = (b : Int) by
            simp [IntTy.toInt, IntTy.modulus]
            omega,
          show (b : Int) ≠ 0 by omega,
          show IntTy.toInt ⟨32,true⟩ 0 = 0 by simp [IntTy.toInt, IntTy.modulus]]
    by_cases hempty : p.pieceAt f = none
    · refine ⟨s3, ?_, ?_⟩
      · refine ExS.seq hskip ?_
        refine ExS.seq hset3 ?_
        refine ExS.seq_ret ?_
        refine ExS.ite (bc := true) hcond3 (by simp [truthy_boolVal, hempty]) ?_
        apply ExS.ret
        apply EvE_of_eval (n := 3)
        have hp : pieceAttacksSpec p f t = false := by simp [pieceAttacksSpec, hempty]
        simp [evalExpr, evalBin, evalCast, false8, boolVal, IntTy.i32, IntTy.u8, IntTy.toInt,
          isPtr, evalBinInt, binInt, intOf, Res.bind, hp, IntTy.wrap]
      · simp [s3, s0]
    · obtain ⟨pc, hpc⟩ : ∃ pc : Piece, p.pieceAt f = some pc := by
        cases hpf : p.pieceAt f with
        | none => exact False.elim (hempty hpf)
        | some q => exact ⟨q, rfl⟩
      have hbcode : b = pc.code := by simpa [b, hpc, pieceByte_toNat]
      let s4a : State := {s3 with locals := s3.locals.upd 5 (u32 pc.type.code)}
      have hcall5 : ExS Gen.prog s3 (.call (some 5) 2 [(.var 3)]) .normal s4a := by
        have h3loc : s3.locals 3 = some (u8 b) := by simp [s3, Locals.upd]
        have harg : EvE Gen.prog s3 (.var 3) (u8 pc.code) := by
          rw [← hbcode]
          exact EvE.var h3loc
        exact call_pure (s := s3) (d := 5) (f := 2) rfl rfl rfl rfl
          (by simpa [piece_code_mod16 pc, Gen.fid_shogi_piece_type] using shogi_piece_type_total ⟨pc.code, piece_code_lt256 pc⟩)
          (EvArgs.cons harg EvArgs.nil)
      let s4 : State := {s4a with locals := s4a.locals.upd 4 (u32 pc.type.code)}
      have hset4 : ExS Gen.prog s4a (.set 4 (.var 5)) .normal s4 := by
        apply ExS.set; apply EvE.var; simp [s4a, Locals.upd]
      -- row_of(t) -> 7, row_of(f) -> 8, dr -> 6
      let s7 : State := {s4 with locals := s4.locals.upd 7 (i32 (t.row : Int))}
      have hcall7 : ExS Gen.prog s4 (.call (some 7) 7 [(.var 2)]) .normal s7 := by
        have harg : EvE Gen.prog s4 (.var 2) (u8 t.val) := EvE.var (by simp [s4, s4a, s3, s0, Locals.upd, frameLocals, Gen.shogi_piece_attacks_square, List.idxOf?, List.findIdx?, List.findIdx?.go])
        exact call_pure (s := s4) (d := 7) (f := 7) rfl rfl rfl rfl (row_of_refines t) (EvArgs.cons harg EvArgs.nil)
      let s8 : State := {s7 with locals := s7.locals.upd 8 (i32 (f.row : Int))}
      have hcall8 : ExS Gen.prog s7 (.call (some 8) 7 [(.var 1)]) .normal s8 := by
        have harg : EvE Gen.prog s7 (.var 1) (u8 f.val) := EvE.var (by simp [s7, s4, s4a, s3, s0, Locals.upd, frameLocals, Gen.shogi_piece_attacks_square, List.idxOf?, List.findIdx?, List.findIdx?.go])
        exact call_pure (s := s7) (d := 8) (f := 7) rfl rfl rfl rfl (row_of_refines f) (EvArgs.cons harg EvArgs.nil)
      let dr : Int := (t.row : Int) - f.row
      let s6 : State := {s8 with locals := s8.locals.upd 6 (i32 dr)}
      have hset6 : ExS Gen.prog s8 (.set 6 (.bin .sub (some ⟨32,true⟩) (.var 7) (.var 8))) .normal s6 := by
        apply ExS.set
        exact evI_sub (EvE.var (by simp [s6, s8, s7, Locals.upd])) (EvE.var (by simp [s6, s8, Locals.upd, s7]))
          (by unfold Sm; have ht := t.isLt; simp [Square.row] at *; omega)
          (by unfold Sm; have hf2 := f.isLt; simp [Square.row] at *; omega)
      -- col_of(t) -> 10, col_of(f) -> 11, dc -> 9
      let s10 : State := {s6 with locals := s6.locals.upd 10 (i32 (t.col : Int))}
      have hcall10 : ExS Gen.prog s6 (.call (some 10) 8 [(.var 2)]) .normal s10 := by
        have harg : EvE Gen.prog s6 (.var 2) (u8 t.val) := EvE.var (by simp [s6, s8, s7, s4, s4a, s3, s0, Locals.upd, frameLocals, Gen.shogi_piece_attacks_square, List.idxOf?, List.findIdx?, List.findIdx?.go])
        exact call_pure (s := s6) (d := 10) (f := 8) rfl rfl rfl rfl (col_of_refines t) (EvArgs.cons harg EvArgs.nil)
      let s11 : State := {s10 with locals := s10.locals.upd 11 (i32 (f.col : Int))}
      have hcall11 : ExS Gen.prog s10 (.call (some 11) 8 [(.var 1)]) .normal s11 := by
        have harg : EvE Gen.prog s10 (.var 1) (u8 f.val) := EvE.var (by simp [s10, s6, s8, s7, s4, s4a, s3, s0, Locals.upd, frameLocals, Gen.shogi_piece_attacks_square, List.idxOf?, List.findIdx?, List.findIdx?.go])
        exact call_pure (s := s10) (d := 11) (f := 8) rfl rfl rfl rfl (col_of_refines f) (EvArgs.cons harg EvArgs.nil)
      let dc : Int := (t.col : Int) - f.col
      let s9 : State := {s11 with locals := s11.locals.upd 9 (i32 dc)}
      have hset9 : ExS Gen.prog s11 (.set 9 (.bin .sub (some ⟨32,true⟩) (.var 10) (.var 11))) .normal s9 := by
        apply ExS.set
        exact evI_sub (EvE.var (by simp [s9, s11, s10, Locals.upd]))
          (EvE.var (by simp [s9, s11, s10, Locals.upd]))
          (by unfold Sm; have ht := t.isLt; simp [Square.col] at *; omega)
          (by unfold Sm; have hf2 := f.isLt; simp [Square.col] at *; omega)
      -- fid1 color -> 13, fwd -> 12
      let s13 : State := {s9 with locals := s9.locals.upd 13 (u32 pc.color.idx)}
      have hcall13 : ExS Gen.prog s9 (.call (some 13) 1 [(.var 3)]) .normal s13 := by
        have harg : EvE Gen.prog s9 (.var 3) (u8 pc.code) := by
          rw [← hbcode]
          exact EvE.var (by simp [s9, s11, s10, s6, s8, s7, s4, s4a, s3, Locals.upd])
        have hrun : run 1 [u8 pc.code] = some (some (u32 pc.color.idx)) := by
          obtain ⟨c, ty⟩ := pc
          cases c <;> cases ty <;> decide +kernel
        exact call_pure (s := s9) (d := 13) (f := 1) rfl rfl rfl rfl hrun (EvArgs.cons harg EvArgs.nil)
      let fwd : Int := pc.color.fwd
      let s12 : State := {s13 with locals := s13.locals.upd 12 (i32 fwd)}
      have hset12 : ExS Gen.prog s13
          (.set 12 (.cond (.bin .eq (some ⟨32,false⟩) (.cast ⟨32,false⟩ (.var 13)) (.cast ⟨32,false⟩ (.const (.int ⟨32,true⟩ 0))))
             (.un .neg ⟨32,true⟩ (.const (.int ⟨32,true⟩ 1))) (.const (.int ⟨32,true⟩ 1)))) .normal s12 := by
        apply ExS.set
        apply EvE_of_eval (n := 6)
        obtain ⟨c, ty⟩ := pc
        cases c <;> simp [evalExpr, s13, Locals.upd, evalCast, evalBin, isPtr, evalBinInt, binInt,
          intOf, i32, u32, IntTy.i32, IntTy.u32, IntTy.toInt, IntTy.modulus, IntTy.wrap, Res.bind,
          fwd, Color.fwd, truthy, boolVal, evalUn, arith, IntTy.inRange, IntTy.minVal, IntTy.maxVal, Nat.mod_eq_of_lt, Color.idx,
          show (0 : Nat) % 4294967296 = 0 by rfl, show (1 : Nat) % 4294967296 = 1 by rfl]
      -- fid15 call
      let stepbool : Bool := cformula pc.type.code dr dc fwd
      have hcode : pc.type.code < 128 := by
        obtain ⟨c, ty⟩ := pc
        cases c <;> cases ty <;> decide
      have hdr : -2147483648 ≤ dr ∧ dr < 2147483648 := by
        unfold dr; have ht := t.isLt; have hf2 := f.isLt; simp [Square.row] at *; omega
      have hdc : -2147483648 ≤ dc ∧ dc < 2147483648 := by
        unfold dc; have ht := t.isLt; have hf2 := f.isLt; simp [Square.col] at *; omega
      have hfwd : fwd = 1 ∨ fwd = -1 := by
        obtain ⟨c, ty⟩ := pc
        cases c <;> simp [fwd, Color.fwd]
      have hsdr : -8 ≤ dr ∧ dr ≤ 8 := by
        unfold dr
        have ht := t.isLt; have hf2 := f.isLt
        simp [Square.row] at *
        omega
      have hsdc : -8 ≤ dc ∧ dc ≤ 8 := by
        unfold dc
        have ht := t.isLt; have hf2 := f.isLt
        simp [Square.col] at *
        omega
      obtain ⟨v, hsf, hv⟩ := fid15_body_eq pc.type.code m hcode dr dc fwd hdr hdc hfwd hsdr hsdc
      let sf : State := s15s m pc.type.code dr dc fwd
      let s14 : State := {s12 with locals := s12.locals.upd 14 v, mem := m}
      have hsf' : ExS Gen.prog
          (⟨frameLocals Gen.step_piece_attacks.params [u32 pc.type.code, i32 dr, i32 dc, i32 fwd], m, false⟩ : State)
          Gen.step_piece_attacks.body (.ret (some v)) sf := by
        rwa [frame15]
      have hcall14 : ExS Gen.prog s12 (.call (some 14) 15 [(.var 4), (.var 6), (.var 9), (.var 12)]) .normal s14 := by
        have harg4 : EvE Gen.prog s12 (.var 4) (u32 pc.type.code) := EvE.var (by simp [s12, s13, s9, s11, s10, s6, s8, s7, s4, s4a, s3, Locals.upd])
        have harg6 : EvE Gen.prog s12 (.var 6) (i32 dr) := EvE.var (by simp [s12, s13, s9, s11, s10, s6, s8, s7, s4, s4a, s3, Locals.upd])
        have harg9 : EvE Gen.prog s12 (.var 9) (i32 dc) := EvE.var (by simp [s12, s13, s9, s11, s10, Locals.upd])
        have harg12 : EvE Gen.prog s12 (.var 12) (i32 fwd) := EvE.var (by simp [s12, Locals.upd])
        have hargs : EvArgs Gen.prog s12 [(.var 4), (.var 6), (.var 9), (.var 12)]
            [u32 pc.type.code, i32 dr, i32 dc, i32 fwd] :=
          EvArgs.cons harg4 (EvArgs.cons harg6 (EvArgs.cons harg9 (EvArgs.cons harg12 EvArgs.nil)))
        simpa [s14, sf, s15s] using
          (ExS.call_dst (d := 14) (f := 15) (fn := Gen.step_piece_attacks) (v := v) (s' := sf)
            hargs rfl rfl hsf')
      -- step attack branch: ite var14 -> ret true
      have h14val : EvE Gen.prog s14 (.var 14) v := EvE.var (by simp [s14, Locals.upd])
      have hv_eq : v = fid15_u8bool stepbool := hv
      by_cases hstep : stepbool = true
      · refine ⟨s14, ?_, ?_⟩
        · refine ExS.seq hskip ?_
          refine ExS.seq hset3 ?_
          refine ExS.seq (s1 := s3) ?_ ?_
          · exact ExS.ite (bc := false) hcond3 (by simp [truthy_boolVal, hempty]) ExS.skip
          · refine ExS.seq (ExS.seq hcall5 hset4) ?_
            refine ExS.seq (ExS.seq hcall7 (ExS.seq hcall8 (ExS.seq hset6
              (ExS.seq hcall10 (ExS.seq hcall11 hset9))))) ?_
            refine ExS.seq (ExS.seq hcall13 hset12) ?_
            refine ExS.seq_ret ?_
            refine ExS.seq hcall14 ?_
            refine ExS.ite (bc := true) (by simpa [hv_eq, hstep, fid15_u8bool] using h14val)
              (by simp [fid15_u8bool, truthy]) ?_
            apply ExS.ret
            apply EvE_of_eval (n := 3)
            have hp : pieceAttacksSpec p f t = true := by
              have hc := (cformula_spec pc.type.code hcode dr dc fwd hfwd hsdr hsdc).1 hstep
              obtain ⟨ty', hty', hoff⟩ := hc
              have hty : ty' = pc.type := by
                cases hpt : pc.type <;> cases ty' <;> simp [PieceType.ofCode, PieceType.code, hpt] at hty' ⊢
              have hoff' : (dr, dc) ∈ stepOffsets fwd pc.type := by simpa [hty] using hoff
              unfold pieceAttacksSpec
              simp [hpc, Position.attackSquares]
              refine ⟨hft, Or.inl ?_⟩
              refine ⟨dr, dc, hoff', ?_⟩
              unfold dr dc Square.offset
              have hrow : (f.row : Int) + ((t.row : Int) - f.row) = t.row := by omega
              have hcol : (f.col : Int) + ((t.col : Int) - f.col) = t.col := by omega
              rw [hrow, hcol]
              exact Shogi.C.Proofs.sq_mk_self t
            simp [evalExpr, evalBin, evalCast, true8, boolVal, IntTy.i32, IntTy.u8, IntTy.toInt,
              isPtr, evalBinInt, binInt, intOf, Res.bind, hp, IntTy.wrap,
            IntTy.modulus, Nat.mod_eq_of_lt (show 1 < 256 by decide)]
        · simp [s14, s12, s13, s9, s11, s10, s6, s8, s7, s4, s4a, s3, s0]
      · -- slider branch
        -- set 15 (diagonal) and set 16 (straight)
        let diagB : Bool := decide ((if dr < 0 then -dr else dr) = (if dc < 0 then -dc else dc))
        let straightB : Bool := decide (dr = 0 ∨ dc = 0)
        let s15 : State := {s14 with locals := s14.locals.upd 15 (u8 (if diagB then 1 else 0))}
        let dri : Fin 17 := ⟨Int.toNat (dr + 8), by omega⟩
        let dci : Fin 17 := ⟨Int.toNat (dc + 8), by omega⟩
        have hdri : (dri.val : Int) - 8 = dr := by dsimp [dri]; omega
        have hdci : (dci.val : Int) - 8 = dc := by dsimp [dci]; omega
        have hset15 : ExS Gen.prog s14
            (.set 15 (.cast ⟨8,false⟩ (.bin .ne (some ⟨32,true⟩)
              (.bin .eq (some ⟨32,true⟩)
                (.cond (.bin .lt (some ⟨32,true⟩) (.var 6) (.const (.int ⟨32,true⟩ 0))) (.un .neg ⟨32,true⟩ (.var 6)) (.var 6))
                (.cond (.bin .lt (some ⟨32,true⟩) (.var 9) (.const (.int ⟨32,true⟩ 0))) (.un .neg ⟨32,true⟩ (.var 9)) (.var 9)))
              (.const (.int ⟨32,true⟩ 0))))) .normal s15 := by
          apply ExS.set
          apply eve_u8_of_sig (N := 10)
          change evalSig (evalExpr Gen.prog 10 s14 set15expr) = some (IntTy.u8, if diagB then 1 else 0)
          have h := set15_eval_finite dri dci
          rw [show evalExpr Gen.prog 10 s14 set15expr =
                  evalExpr Gen.prog 10 (sTest dr dc) set15expr by
            simp [set15expr, evalExpr, s14, s12, s13, s9, s11, s10, s6, s8, s7, s4, s4a, s3,
              Locals.upd, sTest]]
          simpa [hdri, hdci, absI, diagB, dr, dc] using h
        let s16 : State := {s15 with locals := s15.locals.upd 16 (u8 (if straightB then 1 else 0))}
        have hset16 : ExS Gen.prog s15
            (.set 16 (.cast ⟨8,false⟩ (.bin .ne (some ⟨32,true⟩)
              (.lor (.bin .eq (some ⟨32,true⟩) (.var 6) (.const (.int ⟨32,true⟩ 0)))
                    (.bin .eq (some ⟨32,true⟩) (.var 9) (.const (.int ⟨32,true⟩ 0))))
              (.const (.int ⟨32,true⟩ 0))))) .normal s16 := by
          apply ExS.set
          apply eve_u8_of_sig (N := 10)
          change evalSig (evalExpr Gen.prog 10 s15 set16expr) = some (IntTy.u8, if straightB then 1 else 0)
          have h := set16_eval_finite dri dci
          rw [show evalExpr Gen.prog 10 s15 set16expr =
                  evalExpr Gen.prog 10 (sTest dr dc) set16expr by
            simp [set16expr, evalExpr, s15, s14, s12, s13, s9, s11, s10, s6, s8, s7, s4, s4a, s3,
              Locals.upd, sTest]]
          simpa [hdri, hdci, straightB, dr, dc] using h
        -- guard value via finite evaluation
        let gv : Nat := guardSpec pc.type.code dr dc fwd (if diagB then 1 else 0) (if straightB then 1 else 0)
        have hgeval : evalSig (evalExpr Gen.prog 12 s16 guardExpr) = some (IntTy.i32, gv) := by
          have hdrb : -8 ≤ dr ∧ dr ≤ 8 := hsdr
          have hdcb : -8 ≤ dc ∧ dc ≤ 8 := hsdc
          let dri : Fin 17 := ⟨Int.toNat (dr + 8), by omega⟩
          let dci : Fin 17 := ⟨Int.toNat (dc + 8), by omega⟩
          have hty16 : pc.type.code < 16 := by
            obtain ⟨c, ty⟩ := pc
            cases c <;> cases ty <;> decide
          let tyi : Fin 16 := ⟨pc.type.code, hty16⟩
          let fwdi : Fin 2 := ⟨if fwd = 1 then 0 else 1, by split <;> omega⟩
          let diagi : Fin 2 := ⟨if diagB then 1 else 0, by split <;> omega⟩
          let straighti : Fin 2 := ⟨if straightB then 1 else 0, by split <;> omega⟩
          have h := guard_eval_finite tyi dri dci fwdi diagi straighti
          rw [show evalExpr Gen.prog 12 s16 guardExpr =
                evalExpr Gen.prog 12
                  (guardState pc.type.code dr dc fwd
                    (if diagB then 1 else 0) (if straightB then 1 else 0)) guardExpr by
            simp [guardExpr, evalExpr, s16, s15, s14, s12, s13, s9, s11, s10, s6, s8, s7,
              s4, s4a, s3, Locals.upd, guardState]]
          rw [hdri, hdci] at h
          have hfwdi : (if (fwdi.val = 0) then 1 else -1) = fwd := by
            dsimp [fwdi]
            cases hfwd with | inl h => simp [h] | inr h => simp [h]
          have hdiagi : diagi.val = (if diagB then 1 else 0) := by rfl
          have hstraighti : straighti.val = (if straightB then 1 else 0) := by rfl
          rw [hfwdi, hdiagi, hstraighti] at h
          simpa [guardSpec, gv, tyi, diagB, straightB, absI, dr, dc] using h
        have hguard_ev : EvE Gen.prog s16 guardExpr (i32 (gv : Int)) := by
          have hgvsmall : gv < 2147483648 := by
            dsimp [gv]
            exact guardSpec_lt _ _ _ _ _ _
          apply eve_i32_of_sig (N := 12) hgvsmall
          exact hgeval
        by_cases hg0 : gv = 0
        · -- guard FALSE: slider path
          have hspec0 : guardSpec pc.type.code dr dc fwd (if diagB then 1 else 0)
              (if straightB then 1 else 0) = 0 := by simpa [gv] using hg0
          have hdisj := guard0_spec hspec0
          -- derive slider geometry and direction for each case
          let rs : Int := if dr > 0 then 1 else if dr < 0 then -1 else 0
          let cs : Int := if dc > 0 then 1 else if dc < 0 then -1 else 0
          let k : Nat := max dr.natAbs dc.natAbs
          let d : Nat := k - 1
          have hrs : -1 ≤ rs ∧ rs ≤ 1 := by dsimp [rs]; split <;> omega
          have hcs' : -1 ≤ cs ∧ cs ≤ 1 := by dsimp [cs]; split <;> omega
          have hrs_cases : rs = -1 ∨ rs = 0 ∨ rs = 1 := by omega
          have hcs_cases : cs = -1 ∨ cs = 0 ∨ cs = 1 := by omega
          have hstepNZ : rs ≠ 0 ∨ cs ≠ 0 := by
            by_cases hrs0 : rs = 0
            · by_cases hcs0 : cs = 0
              · exfalso
                have hdr0 : dr = 0 := by
                  dsimp [rs] at hrs0
                  by_cases hpos : dr > 0
                  · simp [hpos] at hrs0
                  · by_cases hneg : dr < 0
                    · simp [hpos, hneg] at hrs0
                    · omega
                have hdc0 : dc = 0 := by
                  dsimp [cs] at hcs0
                  by_cases hpos : dc > 0
                  · simp [hpos] at hcs0
                  · by_cases hneg : dc < 0
                    · simp [hpos, hneg] at hcs0
                    · omega
                apply hft
                apply Fin.ext
                simp [dr, dc, Square.row, Square.col] at hdr0 hdc0 ⊢
                omega
              · exact Or.inr hcs0
            · exact Or.inl hrs0
          have hdirs : ∃ r : Fin 8, rdir r.val = (rs, cs) :=
            exists_rdir rs cs hrs_cases hcs_cases hstepNZ
          -- helper to finish the slider path from geometry + direction membership
          have slide_finish (hsg : (((if dr < 0 then -dr else dr) = (if dc < 0 then -dc else dc) ∧ dr ≠ 0) ∨
                (dr = 0 ∧ dc ≠ 0) ∨ (dc = 0 ∧ dr ≠ 0)))
              (hdir : (rs, cs) ∈ slideDirs fwd pc.type) (hr : ∃ r : Fin 8, rdir r.val = (rs, cs)) :
              ∃ s', ExS Gen.prog s16
                (.seq (.set 17 (.bin .sub (some ⟨32,true⟩) (.bin .gt (some ⟨32,true⟩) (.var 6) (.const (.int ⟨32,true⟩ 0)))
                    (.bin .lt (some ⟨32,true⟩) (.var 6) (.const (.int ⟨32,true⟩ 0)))))
                  (.seq (.set 18 (.bin .sub (some ⟨32,true⟩) (.bin .gt (some ⟨32,true⟩) (.var 9) (.const (.int ⟨32,true⟩ 0)))
                    (.bin .lt (some ⟨32,true⟩) (.var 9) (.const (.int ⟨32,true⟩ 0)))))
                    (.seq (.seq (.call (some 20) 7 [(.var 1)])
                        (.seq (.set 19 (.bin .add (some ⟨32,true⟩) (.var 20) (.var 17)))
                          (.seq (.call (some 22) 8 [(.var 1)]) (.set 21 (.bin .add (some ⟨32,true⟩) (.var 22) (.var 18))))))
                      (.seq Gen.shogi_piece_attacks_square_loop0
                        (.ret (some (.cast ⟨8,false⟩ (.bin .ne (some ⟨32,true⟩) (.const (.int ⟨32,true⟩ 1)) (.const (.int ⟨32,true⟩ 0))))))))))
                (.ret (some (if pieceAttacksSpec p f t then true8 else false8))) s' ∧ s'.mem = m := by
            have hgeom := slide_geom_finite f t hft hsg
            have hlen := ray_len_ge_finite f t hft hsg
            dsimp [rs, cs, k, d] at hgeom hlen
            obtain ⟨r, hrdir⟩ := hr
            -- set 17 and 18
            have hdri' : ((Int.toNat (dr + 8) : Nat) : Int) - 8 = dr := by omega
            have hdci' : ((Int.toNat (dc + 8) : Nat) : Int) - 8 = dc := by omega
            let s17 : State := {s16 with locals := s16.locals.upd 17 (i32 rs)}
            have hset17 : ExS Gen.prog s16
                (.set 17 (.bin .sub (some ⟨32,true⟩) (.bin .gt (some ⟨32,true⟩) (.var 6) (.const (.int ⟨32,true⟩ 0)))
                    (.bin .lt (some ⟨32,true⟩) (.var 6) (.const (.int ⟨32,true⟩ 0))))) .normal s17 := by
              apply ExS.set
              apply eve_i32z_of_sig (z := rs)
              change evalSig (evalExpr Gen.prog 8 s16 (signExpr 6)) =
                some (IntTy.i32, (rs % (4294967296 : Int)).toNat)
              have h := sign_eval_finite ⟨Int.toNat (dr + 8), by omega⟩
              rw [show evalExpr Gen.prog 8 s16 (signExpr 6) =
                      evalExpr Gen.prog 8 (sSign dr) (signExpr 6) by
                simp [signExpr, evalExpr, s16, s15, s14, s12, s13, s9, s11, s10, s6, s8, s7,
                  s4, s4a, s3, Locals.upd, sSign]]
              rw [hdri'] at h
              rw [h]
            let s18 : State := {s17 with locals := s17.locals.upd 18 (i32 cs)}
            have hset18 : ExS Gen.prog s17
                (.set 18 (.bin .sub (some ⟨32,true⟩) (.bin .gt (some ⟨32,true⟩) (.var 9) (.const (.int ⟨32,true⟩ 0)))
                    (.bin .lt (some ⟨32,true⟩) (.var 9) (.const (.int ⟨32,true⟩ 0))))) .normal s18 := by
              apply ExS.set
              apply eve_i32z_of_sig (z := cs)
              change evalSig (evalExpr Gen.prog 8 s17 (signExpr 9)) =
                some (IntTy.i32, (cs % (4294967296 : Int)).toNat)
              have h := sign_eval_finite ⟨Int.toNat (dc + 8), by omega⟩
              rw [show evalExpr Gen.prog 8 s17 (signExpr 9) =
                      evalExpr Gen.prog 8 (sSign dc) (signExpr 6) by
                simp [signExpr, evalExpr, s17, s16, s15, s14, s12, s13, s9, s11, s10, s6, s8, s7,
                  s4, s4a, s3, Locals.upd, sSign]]
              rw [hdci'] at h
              rw [h]
            -- row_of(f) -> 20, set19
            let s20 : State := {s18 with locals := s18.locals.upd 20 (i32 (f.row : Int))}
            have hcall20 : ExS Gen.prog s18 (.call (some 20) 7 [(.var 1)]) .normal s20 := by
              have harg : EvE Gen.prog s18 (.var 1) (u8 f.val) := EvE.var (by
                simp [s18, s17, s16, s15, s14, s12, s13, s9, s11, s10, s6, s8, s7, s4, s4a, s3, s0,
                  Locals.upd, frameLocals, Gen.shogi_piece_attacks_square, List.idxOf?, List.findIdx?, List.findIdx?.go])
              exact call_pure (s := s18) (d := 20) (f := 7) rfl rfl rfl rfl (row_of_refines f) (EvArgs.cons harg EvArgs.nil)
            have hsmrs : Sm rs := by unfold Sm; omega
            have hsmrow : Sm (f.row : Int) := sm_sqrow f
            have hsmcs : Sm cs := by unfold Sm; omega
            have hsmcol : Sm (f.col : Int) := sm_sqcol f
            let s19 : State := {s20 with locals := s20.locals.upd 19 (i32 ((f.row : Int) + rs))}
            have hset19 : ExS Gen.prog s20 (.set 19 (.bin .add (some ⟨32,true⟩) (.var 20) (.var 17))) .normal s19 := by
              apply ExS.set
              exact evI_add (EvE.var (show s20.locals 20 = some (i32 (f.row : Int)) by rfl))
                (EvE.var (show s20.locals 17 = some (i32 rs) by rfl))
                hsmrow hsmrs
            -- col_of(f) -> 22, set21
            let s22 : State := {s19 with locals := s19.locals.upd 22 (i32 (f.col : Int))}
            have hcall22 : ExS Gen.prog s19 (.call (some 22) 8 [(.var 1)]) .normal s22 := by
              have harg : EvE Gen.prog s19 (.var 1) (u8 f.val) := EvE.var (by
                simp [s22, s19, s20, s18, s17, s16, s15, s14, s12, s13, s9, s11, s10, s6, s8, s7, s4, s4a, s3, s0,
                  Locals.upd, frameLocals, Gen.shogi_piece_attacks_square, List.idxOf?, List.findIdx?, List.findIdx?.go])
              exact call_pure (s := s19) (d := 22) (f := 8) rfl rfl rfl rfl (col_of_refines f) (EvArgs.cons harg EvArgs.nil)
            let s21 : State := {s22 with locals := s22.locals.upd 21 (i32 ((f.col : Int) + cs))}
            have hset21 : ExS Gen.prog s22 (.set 21 (.bin .add (some ⟨32,true⟩) (.var 22) (.var 18))) .normal s21 := by
              apply ExS.set
              exact evI_add (EvE.var (show s22.locals 22 = some (i32 (f.col : Int)) by rfl))
                (EvE.var (show s22.locals 18 = some (i32 cs) by rfl))
                hsmcol hsmcs
            -- build loop state and call slider_loop_exs
            let sL : State := ⟨(fun i => match i with
              | 0 => some (posPtr' posBlock) | 2 => some (u8 t.val)
              | 17 => some (i32 rs) | 18 => some (i32 cs)
              | 19 => some (i32 ((f.row : Int) + rs)) | 21 => some (i32 ((f.col : Int) + cs))
              | _ => none), m, false⟩
            have hl21_0 : s21.locals 0 = some (posPtr' posBlock) := by
              simp [s21, s22, s19, s20, s18, s17, s16, s15, s14, s12, s13, s9, s11, s10,
                s6, s8, s7, s4, s4a, s3, s0, Locals.upd, frameLocals, Gen.shogi_piece_attacks_square,
                List.idxOf?, List.findIdx?, List.findIdx?.go]
            have hl21_2 : s21.locals 2 = some (u8 t.val) := by
              simp [s21, s22, s19, s20, s18, s17, s16, s15, s14, s12, s13, s9, s11, s10,
                s6, s8, s7, s4, s4a, s3, s0, Locals.upd, frameLocals, Gen.shogi_piece_attacks_square,
                List.idxOf?, List.findIdx?, List.findIdx?.go]
            have hl21_17 : s21.locals 17 = some (i32 rs) := by rfl
            have hl21_18 : s21.locals 18 = some (i32 cs) := by rfl
            have hl21_19 : s21.locals 19 = some (i32 ((f.row : Int) + rs)) := by rfl
            have hl21_21 : s21.locals 21 = some (i32 ((f.col : Int) + cs)) := by rfl
            have hl21_mem : s21.mem = m := rfl
            obtain ⟨hrow, hcol, hbnd, hstepNZ, hk⟩ := hgeom
            have hloop := slider_loop_exs p f t m hm rs cs d r hrdir hrow hcol hbnd hstepNZ hrs hcs' hlen
              s21 hl21_0 hl21_2 hl21_17 hl21_18 hl21_19 hl21_21 hl21_mem
            obtain ⟨sf, hsf, hmemf⟩ := hloop
            -- walkErr_slide
            have hwslide := walkErr_slide p f r d hlen
            -- assemble
            by_cases hw : walkErr p rs cs t d ((f.row : Int) + rs) ((f.col : Int) + cs) = true
            · -- walkErr true -> loop returns false -> spec false
              refine ⟨sf, ?_, ?_⟩
              · refine ExS.seq hset17 ?_
                refine ExS.seq hset18 ?_
                refine ExS.seq (ExS.seq hcall20 hset19) ?_
                refine ExS.seq (ExS.seq hcall22 hset21) ?_
                simpa [hw] using hsf
              · exact hmemf
            · -- walkErr false -> loop returns true -> spec true
              have hslide : t ∈ p.slideTargets f (rs, cs) := by
                have hweq : walkErr p rs cs t d ((f.row : Int) + rs) ((f.col : Int) + cs) = false := by
                  cases h : walkErr p rs cs t d ((f.row : Int) + rs) ((f.col : Int) + cs) <;> simp_all
                rw [← hwslide]
                exact hweq
              have hpspec : pieceAttacksSpec p f t = true := by
                unfold pieceAttacksSpec
                simp [hpc, Position.attackSquares]
                refine ⟨hft, Or.inr ?_⟩
                refine ⟨(rs, cs), hdir, hslide⟩
              refine ⟨sf, ?_, hmemf⟩
              refine ExS.seq hset17 ?_
              refine ExS.seq hset18 ?_
              refine ExS.seq (ExS.seq hcall20 hset19) ?_
              refine ExS.seq (ExS.seq hcall22 hset21) ?_
              simpa [hw, hpspec] using hsf
          -- now handle each guard disjunct
          rcases hdisj with h12 | h3
          · rcases h12 with hdiag | hstraight
            · -- diagonal: type 6/13, diagB
              have hty : pc.type.code = 6 ∨ pc.type.code = 13 := hdiag.2
              have hsg : (((if dr < 0 then -dr else dr) = (if dc < 0 then -dc else dc) ∧ dr ≠ 0) ∨
                  (dr = 0 ∧ dc ≠ 0) ∨ (dc = 0 ∧ dr ≠ 0)) := by
                left
                constructor
                · simpa [diagB] using hdiag.1
                · intro hdr0
                  have : dr.natAbs = 0 := by omega
                  -- dc also 0 from diag; then f=t
                  have hdc0 : dc = 0 := by
                    have hd := hdiag.1
                    simp [diagB] at hd
                    omega
                  apply hft
                  apply Fin.ext
                  simp [dr, dc] at hdr0 hdc0
                  omega
              have hdir : (rs, cs) ∈ slideDirs fwd pc.type := by
                cases hty with
                | inl h6 =>
                  have ht : pc.type = PieceType.bishop := by
                    obtain ⟨c, ty⟩ := pc; cases c <;> cases ty <;> simp [PieceType.code] at h6 ⊢
                  subst ht
                  simp [slideDirs, diagonals, rs, cs]
                | inr h13 =>
                  have ht : pc.type = PieceType.horse := by
                    obtain ⟨c, ty⟩ := pc; cases c <;> cases ty <;> simp [PieceType.code] at h13 ⊢
                  subst ht
                  simp [slideDirs, diagonals, rs, cs]
              exact slide_finish hsg hdir hdirs
            · -- straight: type 7/14, straightB
              have hty : pc.type.code = 7 ∨ pc.type.code = 14 := hstraight.2
              have hsg : (((if dr < 0 then -dr else dr) = (if dc < 0 then -dc else dc) ∧ dr ≠ 0) ∨
                  (dr = 0 ∧ dc ≠ 0) ∨ (dc = 0 ∧ dr ≠ 0)) := by
                have hst : dr = 0 ∨ dc = 0 := by simpa [straightB] using hstraight.1
                rcases hst with hdr0 | hdc0
                · right; left; exact ⟨hdr0, by intro h; apply hft; apply Fin.ext; simp [dr, dc] at hdr0 h; omega⟩
                · right; right; exact ⟨hdc0, by intro h; apply hft; apply Fin.ext; simp [dr, dc] at hdc0 h; omega⟩
              have hdir : (rs, cs) ∈ slideDirs fwd pc.type := by
                cases hty with
                | inl h7 =>
                  have ht : pc.type = PieceType.rook := by
                    obtain ⟨c, ty⟩ := pc; cases c <;> cases ty <;> simp [PieceType.code] at h7 ⊢
                  subst ht
                  simp [slideDirs, orthogonals, rs, cs]
                | inr h14 =>
                  have ht : pc.type = PieceType.dragon := by
                    obtain ⟨c, ty⟩ := pc; cases c <;> cases ty <;> simp [PieceType.code] at h14 ⊢
                  subst ht
                  simp [slideDirs, orthogonals, rs, cs]
              exact slide_finish hsg hdir hdirs
          · -- lance: type 2, dc=0, dr*fwd>0
              have hty : pc.type.code = 2 := h3.2
              have hsg : (((if dr < 0 then -dr else dr) = (if dc < 0 then -dc else dc) ∧ dr ≠ 0) ∨
                  (dr = 0 ∧ dc ≠ 0) ∨ (dc = 0 ∧ dr ≠ 0)) := by
                right; right
                constructor
                · exact h3.1.1
                · intro hdr0
                  have : dr * fwd = 0 := by simp [hdr0]
                  omega
              have hdir : (rs, cs) ∈ slideDirs fwd pc.type := by
                have ht : pc.type = PieceType.lance := by
                  obtain ⟨c, ty⟩ := pc; cases c <;> cases ty <;> simp [PieceType.code] at hty ⊢
                subst ht
                have hrsfwd : rs = fwd := by
                  dsimp [rs]
                  rcases hfwd with hfwd | hfwd <;> simp [hfwd] at h3 ⊢ <;> omega
                simp [slideDirs, hrsfwd, cs, h3.1.1]
              exact slide_finish hsg hdir hdirs
        · -- guard TRUE: ret false, spec false
          refine ⟨s16, ?_, ?_⟩
          · refine ExS.seq hprefix ?_
            refine ExS.ite (vc := i32 (gv : Int)) (bc := true) ?_
              (by
                have hgv01 : gv = 0 ∨ gv = 1 := by
                  dsimp [gv]
                  unfold guardSpec
                  dsimp
                  split <;> simp
                rcases hgv01 with hgv0 | hgv1
                · contradiction
                · simp [hgv1, i32, IntTy.wrap, IntTy.modulus, truthy]) ?_
            · simpa [hg0] using hguard_ev
            apply ExS.ret
            apply EvE_of_eval (n := 3)
            have hpspec : pieceAttacksSpec p f t = false := by
              -- no step (hstep) and no slide (guard true)
              unfold pieceAttacksSpec
              simp [hpc]
              constructor
              · exact hft
              · constructor
                · intro hstepmem
                  have hcf := (cformula_spec pc.type.code hcode dr dc fwd hfwd hsdr hsdc).2 ?_
                  · exact hstep hcf
                  · obtain ⟨ty', hty', hoff⟩ := hstepmem
                    exact ⟨ty', rfl, hoff⟩
                · intro hslidemem
                  obtain ⟨d, hdmem, htd⟩ := hslidemem
                  have hray : t ∈ ray f d := slideTargets_sub p f d htd
                  -- guardSpec=0 contradicts gv≠0 once we show geometry forces a guard disjunct
                  have hgs : guardSpec pc.type.code dr dc fwd
                      (if diagB then 1 else 0) (if straightB then 1 else 0) = 0 := by
                    -- case split on the piece type
                    obtain ⟨c, ty⟩ := pc
                    cases c <;> cases ty <;> simp [slideDirs, diagonals, orthogonals] at hdmem ⊢ <;>
                      try { rcases hdmem with rfl | rfl | rfl | rfl }
                    all_goals
                      simp [guardSpec, diagB, straightB, absI, dr, dc] at *
                      try omega
                  have : gv = 0 := by simpa [gv] using hgs
                  exact hg0 this
            simp [evalExpr, evalBin, evalCast, false8, boolVal, IntTy.i32, IntTy.u8, IntTy.toInt,
              isPtr, evalBinInt, binInt, intOf, Res.bind, hpspec, IntTy.wrap, IntTy.modulus]
          · simp [s16, s15, s14, s12, s13, s9, s11, s10, s6, s8, s7, s4, s4a, s3, s0]


end Shogi.C.Proofs
