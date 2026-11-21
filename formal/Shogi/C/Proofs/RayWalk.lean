import Shogi.C.Proofs.StepPieceAttacksSpec
import Shogi.C.Proofs.SameRay
set_option maxHeartbeats 8000000
set_option linter.unusedSimpArgs false
namespace Shogi.C.Proofs
open MiniC Shogi Shogi.C

variable {posBlock : Nat}

def rstate (m : Mem) (to : Square) (rs cs row col : Int) : State :=
  ⟨(fun i => match i with
      | 0 => some (posPtr' posBlock) | 2 => some (u8 to.val)
      | 17 => some (i32 rs) | 18 => some (i32 cs)
      | 19 => some (i32 row) | 21 => some (i32 col) | _ => none),
   m, false⟩

theorem call_row_of (m : Mem) (to : Square) (rs cs row col : Int) (d : Nat) :
    ∃ s', ExS Gen.prog (rstate (posBlock := posBlock) m to rs cs row col)
      (.call (some d) 7 [(.var 2)]) .normal s' ∧
      s'.locals d = some (i32 (Square.row to)) ∧
      (∀ i, i ≠ d → s'.locals i = (rstate (posBlock := posBlock) m to rs cs row col).locals i) ∧
      s'.mem = m := by
  have harg : EvE Gen.prog (rstate (posBlock := posBlock) m to rs cs row col) (.var 2) (u8 to.val) := by
    apply EvE.var; simp [rstate]
  have h := call_pure (s := rstate (posBlock := posBlock) m to rs cs row col) (d := d) (f := 7)
    rfl rfl rfl rfl (row_of_refines to) (EvArgs.cons harg EvArgs.nil)
  refine ⟨_, h, ?_, ?_, ?_⟩
  · simp [rstate, Locals.upd]
  · intro i hi; simp [rstate, Locals.upd, hi]
  · rfl

theorem call_col_of (m : Mem) (to : Square) (rs cs row col : Int) (d : Nat) :
    ∃ s', ExS Gen.prog (rstate (posBlock := posBlock) m to rs cs row col)
      (.call (some d) 8 [(.var 2)]) .normal s' ∧
      s'.locals d = some (i32 (Square.col to)) ∧
      (∀ i, i ≠ d → s'.locals i = (rstate (posBlock := posBlock) m to rs cs row col).locals i) ∧
      s'.mem = m := by
  have harg : EvE Gen.prog (rstate (posBlock := posBlock) m to rs cs row col) (.var 2) (u8 to.val) := by
    apply EvE.var; simp [rstate]
  have h := call_pure (s := rstate (posBlock := posBlock) m to rs cs row col) (d := d) (f := 8)
    rfl rfl rfl rfl (col_of_refines to) (EvArgs.cons harg EvArgs.nil)
  refine ⟨_, h, ?_, ?_, ?_⟩
  · simp [rstate, Locals.upd]
  · intro i hi; simp [rstate, Locals.upd, hi]
  · rfl

theorem load_piece (p : Position) (m : Mem) (hm : m posBlock = some (encode p))
    (to : Square) (rs cs row col : Int)
    (hr : 0 ≤ row ∧ row < 9) (hc : 0 ≤ col ∧ col < 9)
    {s : State}
    (h0 : s.locals 0 = some (posPtr' posBlock))
    (h19 : s.locals 19 = some (i32 row))
    (h21 : s.locals 21 = some (i32 col))
    (hmem : s.mem = m) :
    let sq : Square := ⟨row.toNat * 9 + col.toNat, by
      have hrn : row.toNat < 9 := by omega
      have hcn : col.toNat < 9 := by omega
      omega⟩
    EvE Gen.prog s
      (.load (.int ⟨8, false⟩) (.index (.field (.var 0) 0)
        (.bin .add (some ⟨32, true⟩) (.bin .mul (some ⟨32, true⟩) (.var 19) (.const (.int ⟨32, true⟩ 9))) (.var 21)) 1))
      (u8 (pieceByte (p.pieceAt sq)).toNat) := by
  dsimp only
  let sq : Square := ⟨row.toNat * 9 + col.toNat, by
    have hrn : row.toNat < 9 := by omega
    have hcn : col.toNat < 9 := by omega
    omega⟩
  have hsqval : sq.val = row.toNat * 9 + col.toNat := rfl
  have hfield : EvE Gen.prog s
      (.field (.var 0) 0) (.ptr posBlock (0 + 0)) := by
    refine EvE.field (EvE.var (v := posPtr' posBlock) h0) ?_
    simp [ptrAddN, posPtr', hmem, hm]
  have hrow : EvE Gen.prog s (.var 19) (i32 row) := EvE.var h19
  have hcol : EvE Gen.prog s (.var 21) (i32 col) := EvE.var h21
  have hmul : EvE Gen.prog s
      (.bin .mul (some ⟨32, true⟩) (.var 19) (.const (.int ⟨32, true⟩ 9))) (i32 (row * 9)) :=
    evI_mul hrow (EvE.const (.int ⟨32, true⟩ 9)) (by unfold Sm; omega) (by unfold Sm; omega)
  have hadd : EvE Gen.prog s
      (.bin .add (some ⟨32, true⟩) (.bin .mul (some ⟨32, true⟩) (.var 19) (.const (.int ⟨32, true⟩ 9))) (.var 21))
      (i32 (row * 9 + col)) :=
    evI_add hmul hcol (by unfold Sm; omega) (by unfold Sm; omega)
  have hind : EvE Gen.prog s
      (.index (.field (.var 0) 0)
        (.bin .add (some ⟨32, true⟩) (.bin .mul (some ⟨32, true⟩) (.var 19) (.const (.int ⟨32, true⟩ 9))) (.var 21)) 1)
      (.ptr posBlock (row.toNat * 9 + col.toNat)) := by
    refine EvE.index hfield hadd ?_
    simp only [IntTy.i32]
    rw [toInt_wrap32 (row * 9 + col) (by omega) (by omega)]
    have henc : (encode p).length = 114 := by exact encode_length p
    simp [ptrAdd, hsqval, hmem, hm, henc]
    have hcond : 0 ≤ row * 9 + col ∧ row * 9 + col ≤ 114 := by omega
    rw [if_pos hcond]
    congr 2
    omega
  refine EvE.load hind ?_
  simp only [load, Ty.size, IntTy.bytes, show (8 : Nat) / 8 = 1 by rfl]
  rw [show s.mem = m from hmem]
  rw [readBoard hm sq.val sq.isLt]
  simp [decodeLE, Res.bind, hsqval, u8, IntTy.u8]

theorem evI_ne {s e1 e2 a b} (h1 : EvE Gen.prog s e1 (i32 a)) (h2 : EvE Gen.prog s e2 (i32 b))
    (ha : Sm a) (hb : Sm b) :
    EvE Gen.prog s (.bin .ne (some ⟨32, true⟩) e1 e2) (boolVal (decide (a ≠ b))) := by
  refine EvE.bin h1 h2 ?_
  have hwa := toInt_wrap32 a (by unfold Sm at ha; omega) (by unfold Sm at ha; omega)
  have hwb := toInt_wrap32 b (by unfold Sm at hb; omega) (by unfold Sm at hb; omega)
  simp [evalBin, isPtr, evalBinInt, binInt, intOf, i32, IntTy.i32, Res.bind, hwa, hwb]

theorem evLor0 {s e x} (h : EvE Gen.prog s e (boolVal x)) :
    EvE Gen.prog s (.lor (.const (.int ⟨32, true⟩ 0)) e) (boolVal x) := by
  have hf : truthy (.int IntTy.i32 0) = .ok false := by rfl
  simpa using (EvE.lor_false (p := Gen.prog) (s := s) (EvE.const (.int ⟨32, true⟩ 0)) hf h (truthy_boolVal x))

theorem ev_ne0e2 {s : State} {e : Expr} {b : Nat} (hb : b < 256) (h : EvE Gen.prog s e (u8 b)) :
    EvE Gen.prog s (.bin .ne (some ⟨32, true⟩) (.cast ⟨32, true⟩ e) (.const (.int ⟨32, true⟩ 0)))
      (boolVal (decide (b ≠ 0))) := by
  refine EvE.bin (EvE.cast h rfl) (EvE.const _) ?_
  simp [evalBin, isPtr, evalBinInt, binInt, intOf, IntTy.u8, evalCast, IntTy.modulus, IntTy.toInt, Res.bind,
    Nat.mod_eq_of_lt (show b < 4294967296 by omega), show ¬ (2147483648 ≤ b) by omega]

-- spec of the ray walk: true if any square strictly between `from` and `to` (on the ray) is occupied
def walkErr (p : Position) (rs cs : Int) (to : Square) : Nat → Int → Int → Bool
  | 0, _, _ => false
  | d+1, row, col =>
      if row = (Square.row to : Int) ∧ col = (Square.col to : Int) then false
      else
        match Square.mk? row col with
        | none => true
        | some sq => if p.isEmpty sq then walkErr p rs cs to d (row + rs) (col + cs) else true


theorem call_row_of_gen {s : State} (to : Square) (h2 : s.locals 2 = some (u8 to.val)) (d : Nat) :
    ExS Gen.prog s (.call (some d) 7 [(.var 2)]) .normal {s with locals := s.locals.upd d (i32 (Square.row to))} := by
  apply call_pure rfl rfl rfl rfl (row_of_refines to)
  exact EvArgs.cons (EvE.var h2) EvArgs.nil

theorem call_col_of_gen {s : State} (to : Square) (h2 : s.locals 2 = some (u8 to.val)) (d : Nat) :
    ExS Gen.prog s (.call (some d) 8 [(.var 2)]) .normal {s with locals := s.locals.upd d (i32 (Square.col to))} := by
  apply call_pure rfl rfl rfl rfl (col_of_refines to)
  exact EvArgs.cons (EvE.var h2) EvArgs.nil

theorem evCastI32 {s e a} (ha : Sm a) (h : EvE Gen.prog s e (i32 a)) : EvE Gen.prog s (.cast ⟨32, true⟩ e) (i32 a) :=
  EvE.cast h (cast_i32 a (by unfold Sm at ha; omega) (by unfold Sm at ha; omega))

theorem sm_sqrow (to : Square) : Sm (Square.row to : Int) := by
  unfold Sm; have ht := to.isLt; simp [Square.row]; omega
theorem sm_sqcol (to : Square) : Sm (Square.col to : Int) := by
  unfold Sm; have ht := to.isLt; simp [Square.col]; omega

theorem ray_walk_loop (p : Position) (m : Mem) (hm : m posBlock = some (encode p))
    (rs cs : Int) (to : Square) (hstep : rs ≠ 0 ∨ cs ≠ 0)
    (hrs : -1 ≤ rs ∧ rs ≤ 1) (hcs : -1 ≤ cs ∧ cs ≤ 1) :
  ∀ (d : Nat) (row col : Int) (s : State),
    (Square.row to : Int) = row + (d : Int) * rs →
    (Square.col to : Int) = col + (d : Int) * cs →
    (∀ (i : Nat), i ≤ d → 0 ≤ row + (i : Int) * rs ∧ row + (i : Int) * rs < 9 ∧ 0 ≤ col + (i : Int) * cs ∧ col + (i : Int) * cs < 9) →
    s.locals 0 = some (posPtr' posBlock) →
    s.locals 2 = some (u8 to.val) →
    s.locals 17 = some (i32 rs) →
    s.locals 18 = some (i32 cs) →
    s.locals 19 = some (i32 row) →
    s.locals 21 = some (i32 col) →
    s.mem = m →
    if walkErr p rs cs to d row col then
      ∃ s', ExS Gen.prog s Gen.shogi_piece_attacks_square_loop0 (.ret (some false8)) s'
    else
      ∃ s', ExS Gen.prog s Gen.shogi_piece_attacks_square_loop0 .normal s' ∧
        s'.mem = m ∧ s'.locals 19 = some (i32 (Square.row to : Int)) ∧
        s'.locals 21 = some (i32 (Square.col to : Int)) := by
  intro d
  induction d with
  | zero =>
    intro row col s hrow hcol hbnd h0 h2 h17 h18 h19 h21 hmem
    simp [walkErr]
    have hb0 := hbnd 0 (by omega)
    have hb0' : 0 ≤ row ∧ row < 9 ∧ 0 ≤ col ∧ col < 9 := by simpa using hb0
    have hroweq : row = (Square.row to : Int) := by omega
    have hcoleq : col = (Square.col to : Int) := by omega
    let s23 : State := {s with locals := s.locals.upd 23 (i32 (Square.row to))}
    have hcall23 : ExS Gen.prog s (.call (some 23) 7 [(.var 2)]) .normal s23 :=
      call_row_of_gen to h2 23
    have hne23' := evI_ne (EvE.var (s := s23) (i := 19) (v := i32 row) (by simpa [s23, Locals.upd] using h19))
      (EvE.var (s := s23) (i := 23) (v := i32 (Square.row to)) (by simp [s23, Locals.upd]))
      (by unfold Sm; omega) (sm_sqrow to)
    have hne23 : EvE Gen.prog s23 (.bin .ne (some ⟨32, true⟩) (.var 19) (.var 23)) (boolVal false) := by
      simpa [hroweq] using hne23'
    let s24 : State := {s23 with locals := s23.locals.upd 24 (i32 (Square.col to))}
    let s25 : State := {s24 with locals := s24.locals.upd 25 (boolVal false)}
    have hite1 : ExS Gen.prog s23
        (.ite (.bin .ne (some ⟨32, true⟩) (.var 19) (.var 23)) (.set 25 (.const (.int ⟨32, true⟩ 1)))
          (.seq (.call (some 24) 8 [(.var 2)])
            (.set 25 (.lor (.const (.int ⟨32, true⟩ 0)) (.bin .ne (some ⟨32, true⟩) (.var 21) (.var 24))))))
        .normal s25 := by
      refine ExS.ite (bc := false) hne23 (by simp [truthy_boolVal]) ?_
      have hcall24 : ExS Gen.prog s23 (.call (some 24) 8 [(.var 2)]) .normal s24 :=
        call_col_of_gen to (by simpa [s23, Locals.upd] using h2) 24
      refine ExS.seq hcall24 ?_
      have hne24' := evI_ne (EvE.var (s := s24) (i := 21) (v := i32 col) (by simpa [s24, s23, Locals.upd] using h21))
        (EvE.var (s := s24) (i := 24) (v := i32 (Square.col to)) (by simp [s24, Locals.upd]))
        (by unfold Sm; omega) (sm_sqcol to)
      have hne24 : EvE Gen.prog s24 (.bin .ne (some ⟨32, true⟩) (.var 21) (.var 24)) (boolVal false) := by
        simpa [hcoleq] using hne24'
      simpa [s25, Locals.upd] using ExS.set (evLor0 hne24)
    have hvar25 : EvE Gen.prog s25 (.var 25) (boolVal false) := EvE.var (s := s25) (i := 25) (v := boolVal false) (by simp [s25, Locals.upd])
    have hite2 : ExS Gen.prog s25
        (.ite (.var 25)
          (.seq (.ite (.bin .ne (some ⟨32, true⟩) (.cast ⟨32, true⟩
              (.load (.int ⟨8, false⟩) (.index (.field (.var 0) 0)
                (.bin .add (some ⟨32, true⟩) (.bin .mul (some ⟨32, true⟩) (.var 19) (.const (.int ⟨32, true⟩ 9))) (.var 21)) 1)))
              (.const (.int ⟨32, true⟩ 0)))
              (.ret (some (.cast ⟨8, false⟩ (.bin .ne (some ⟨32, true⟩) (.const (.int ⟨32, true⟩ 0)) (.const (.int ⟨32, true⟩ 0)))))) .skip)
            (.seq (.set 19 (.cast ⟨32, true⟩ (.bin .add (some ⟨32, true⟩) (.cast ⟨32, true⟩ (.var 19)) (.cast ⟨32, true⟩ (.var 17)))))
              (.set 21 (.cast ⟨32, true⟩ (.bin .add (some ⟨32, true⟩) (.cast ⟨32, true⟩ (.var 21)) (.cast ⟨32, true⟩ (.var 18)))))))
          .brk) .brk s25 := by
      refine ExS.ite (bc := false) hvar25 (by simp [truthy_boolVal]) ?_
      simpa using (ExS.brk : ExS Gen.prog s25 .brk .brk s25)
    refine ⟨s25, ?_, ?_, ?_, ?_⟩
    · exact ExS.loop_brk (ExS.seq hcall23 (ExS.seq hite1 hite2))
    · simp [s25, s24, s23, hmem]
    · simp [s25, s24, s23, Locals.upd, h19, hroweq]
    · simp [s25, s24, s23, Locals.upd, h21, hcoleq]
  | succ d ih =>
    intro row col s hrow hcol hbnd h0 h2 h17 h18 h19 h21 hmem
    have hne_cursor : ¬(row = (Square.row to : Int) ∧ col = (Square.col to : Int)) := by
      rintro ⟨h1, h2'⟩
      have hrs' : rs = -1 ∨ rs = 0 ∨ rs = 1 := by omega
      have hcs' : cs = -1 ∨ cs = 0 ∨ cs = 1 := by omega
      rcases hrs' with rfl | rfl | rfl <;> rcases hcs' with rfl | rfl | rfl <;> omega
    have hb0 := hbnd 0 (by omega)
    have hb0' : 0 ≤ row ∧ row < 9 ∧ 0 ≤ col ∧ col < 9 := by simpa using hb0
    let sq : Square := ⟨row.toNat * 9 + col.toNat, by
      have hrn : row.toNat < 9 := by omega
      have hcn : col.toNat < 9 := by omega
      omega⟩
    have hrowb : 0 ≤ row ∧ row < 9 := ⟨hb0'.1, hb0'.2.1⟩
    have hcolb : 0 ≤ col ∧ col < 9 := ⟨hb0'.2.2.1, hb0'.2.2.2⟩
    have hbnd' : ∀ i, i ≤ d → 0 ≤ (row + rs) + i * rs ∧ (row + rs) + i * rs < 9 ∧
        0 ≤ (col + cs) + i * cs ∧ (col + cs) + i * cs < 9 := by
      intro i hi
      have hb := hbnd (i + 1) (by omega)
      have heq1 : (row + rs) + i * rs = row + (i + 1) * rs := by rw [Int.add_mul]; simp; omega
      have heq2 : (col + cs) + i * cs = col + (i + 1) * cs := by rw [Int.add_mul]; simp; omega
      simpa [heq1, heq2] using hb
    have hrow' : (Square.row to : Int) = (row + rs) + d * rs := by
      rw [show (row + rs) + d * rs = row + ((d + 1 : Nat) : Int) * rs by
        simp; rw [Int.add_mul]; simp; omega]
      exact hrow
    have hcol' : (Square.col to : Int) = (col + cs) + d * cs := by
      rw [show (col + cs) + d * cs = col + ((d + 1 : Nat) : Int) * cs by
        simp; rw [Int.add_mul]; simp; omega]
      exact hcol
    by_cases hrowEq : row = (Square.row to : Int)
    · have hcolNe : col ≠ (Square.col to : Int) := by
        intro hc; exact hne_cursor ⟨hrowEq, hc⟩
      -- first ite: row == row23, so else branch; col != col24
      let s23 : State := {s with locals := s.locals.upd 23 (i32 (Square.row to))}
      have hcall23 : ExS Gen.prog s (.call (some 23) 7 [(.var 2)]) .normal s23 := call_row_of_gen to h2 23
      have hne23' := evI_ne (EvE.var (s := s23) (i := 19) (v := i32 row) (by simpa [s23, Locals.upd] using h19))
        (EvE.var (s := s23) (i := 23) (v := i32 (Square.row to)) (by simp [s23, Locals.upd]))
        (by unfold Sm; omega) (sm_sqrow to)
      have hne23 : EvE Gen.prog s23 (.bin .ne (some ⟨32, true⟩) (.var 19) (.var 23)) (boolVal false) := by
        simpa [hrowEq] using hne23'
      let s24 : State := {s23 with locals := s23.locals.upd 24 (i32 (Square.col to))}
      let s25 : State := {s24 with locals := s24.locals.upd 25 (boolVal true)}
      have hite1 : ExS Gen.prog s23
          (.ite (.bin .ne (some ⟨32, true⟩) (.var 19) (.var 23)) (.set 25 (.const (.int ⟨32, true⟩ 1)))
            (.seq (.call (some 24) 8 [(.var 2)])
              (.set 25 (.lor (.const (.int ⟨32, true⟩ 0)) (.bin .ne (some ⟨32, true⟩) (.var 21) (.var 24))))))
          .normal s25 := by
        refine ExS.ite (bc := false) hne23 (by simp [truthy_boolVal]) ?_
        have hcall24 : ExS Gen.prog s23 (.call (some 24) 8 [(.var 2)]) .normal s24 :=
          call_col_of_gen to (by simpa [s23, Locals.upd] using h2) 24
        refine ExS.seq hcall24 ?_
        have hne24' := evI_ne (EvE.var (s := s24) (i := 21) (v := i32 col) (by simpa [s24, s23, Locals.upd] using h21))
          (EvE.var (s := s24) (i := 24) (v := i32 (Square.col to)) (by simp [s24, Locals.upd]))
          (by unfold Sm; omega) (sm_sqcol to)
        have hne24 : EvE Gen.prog s24 (.bin .ne (some ⟨32, true⟩) (.var 21) (.var 24)) (boolVal true) := by
          simpa [hcolNe] using hne24'
        simpa [s25, Locals.upd, boolVal] using ExS.set (evLor0 hne24)
      -- now handle occupied / empty
      have hload := load_piece p m hm to rs cs row col hrowb hcolb
        (s := s25)
        (by simpa [s25, s24, s23, Locals.upd] using h0)
        (by simp [s25, s24, s23, Locals.upd, h19])
        (by simp [s25, s24, s23, Locals.upd, h21])
        (by simp [s25, s24, s23, hmem])
      have hb_sq : (pieceByte (p.pieceAt sq)).toNat < 256 := UInt8.toNat_lt _
      have hcond_ev : EvE Gen.prog s25 (.bin .ne (some ⟨32, true⟩) (.cast ⟨32, true⟩
          (.load (.int ⟨8, false⟩) (.index (.field (.var 0) 0)
            (.bin .add (some ⟨32, true⟩) (.bin .mul (some ⟨32, true⟩) (.var 19) (.const (.int ⟨32, true⟩ 9))) (.var 21)) 1)))
          (.const (.int ⟨32, true⟩ 0))) (boolVal (decide ((pieceByte (p.pieceAt sq)).toNat ≠ 0))) := by
        have hl : EvE Gen.prog s25
            (.load (.int ⟨8, false⟩) (.index (.field (.var 0) 0)
              (.bin .add (some ⟨32, true⟩) (.bin .mul (some ⟨32, true⟩) (.var 19) (.const (.int ⟨32, true⟩ 9))) (.var 21)) 1))
            (u8 (pieceByte (p.pieceAt sq)).toNat) := by
          simpa [s25, s24, s23, Locals.upd] using hload
        exact ev_ne0e2 hb_sq hl
      by_cases hempty : p.isEmpty sq = true
      · have hb0sq : (pieceByte (p.pieceAt sq)).toNat = 0 := by
          rw [isEmpty_bb p sq] at hempty
          simp [bb, sq.isLt] at hempty
          exact hempty
        -- walkErr reduces to recursive call
        have hsq_some : Square.mk? row col = some sq := by
          simp [sq, Square.mk?, hrowb, hcolb]
          omega
        simp [walkErr, hne_cursor, hsq_some, hempty]
        -- empty: skip, then advance cursor
        have hcond_ev0 : EvE Gen.prog s25 (.bin .ne (some ⟨32, true⟩) (.cast ⟨32, true⟩
            (.load (.int ⟨8, false⟩) (.index (.field (.var 0) 0)
              (.bin .add (some ⟨32, true⟩) (.bin .mul (some ⟨32, true⟩) (.var 19) (.const (.int ⟨32, true⟩ 9))) (.var 21)) 1)))
            (.const (.int ⟨32, true⟩ 0))) (boolVal false) := by
          simpa [hb0sq] using hcond_ev
        let s19 : State := {s25 with locals := s25.locals.upd 19 (i32 (row + rs))}
        let s21 : State := {s19 with locals := s19.locals.upd 21 (i32 (col + cs))}
        have hbody : ExS Gen.prog s25
            (.ite (.var 25)
              (.seq (.ite (.bin .ne (some ⟨32, true⟩) (.cast ⟨32, true⟩
                  (.load (.int ⟨8, false⟩) (.index (.field (.var 0) 0)
                    (.bin .add (some ⟨32, true⟩) (.bin .mul (some ⟨32, true⟩) (.var 19) (.const (.int ⟨32, true⟩ 9))) (.var 21)) 1)))
                  (.const (.int ⟨32, true⟩ 0)))
                  (.ret (some (.cast ⟨8, false⟩ (.bin .ne (some ⟨32, true⟩) (.const (.int ⟨32, true⟩ 0)) (.const (.int ⟨32, true⟩ 0)))))) .skip)
                (.seq (.set 19 (.cast ⟨32, true⟩ (.bin .add (some ⟨32, true⟩) (.cast ⟨32, true⟩ (.var 19)) (.cast ⟨32, true⟩ (.var 17)))))
                  (.set 21 (.cast ⟨32, true⟩ (.bin .add (some ⟨32, true⟩) (.cast ⟨32, true⟩ (.var 21)) (.cast ⟨32, true⟩ (.var 18)))))))
              .brk) .normal s21 := by
          refine ExS.ite (bc := true) (EvE.var (s := s25) (i := 25) (v := boolVal true) (by simp [s25, Locals.upd, boolVal, IntTy.i32])) (by simp [truthy_boolVal]) ?_
          refine ExS.seq (ExS.ite (bc := false) hcond_ev0 (by simp [truthy_boolVal]) ExS.skip) ?_
          refine ExS.seq (s1 := s19) (s2 := s21) ?_ ?_
          · apply ExS.set; apply evCastI32 (by unfold Sm; omega)
            exact evI_add
              (evCastI32 (by unfold Sm; omega) (EvE.var (s := s25) (i := 19) (v := i32 row)
                (by simpa [s25, s24, s23, Locals.upd] using h19)))
              (evCastI32 (by unfold Sm; omega) (EvE.var (s := s25) (i := 17) (v := i32 rs)
                (by simpa [s25, s24, s23, Locals.upd] using h17)))
              (by unfold Sm; omega) (by unfold Sm; omega)
          · apply ExS.set; apply evCastI32 (by unfold Sm; omega)
            exact evI_add
              (evCastI32 (by unfold Sm; omega) (EvE.var (s := s19) (i := 21) (v := i32 col)
                (by simpa [s19, s25, s24, s23, Locals.upd] using h21)))
              (evCastI32 (by unfold Sm; omega) (EvE.var (s := s19) (i := 18) (v := i32 cs)
                (by simpa [s19, s25, s24, s23, Locals.upd] using h18)))
              (by unfold Sm; omega) (by unfold Sm; omega)
        have ihres := ih (row + rs) (col + cs) s21 hrow' hcol' hbnd'
            (by simpa [s21, s19, s25, s24, s23, Locals.upd] using h0)
            (by simpa [s21, s19, s25, s24, s23, Locals.upd] using h2)
            (by simpa [s21, s19, s25, s24, s23, Locals.upd] using h17)
            (by simpa [s21, s19, s25, s24, s23, Locals.upd] using h18)
            (by simp [s21, s19, Locals.upd])
            (by simp [s21, Locals.upd])
            (by simp [s21, s19, s25, s24, s23, hmem])
        split at ihres
        · rename_i hh
          rw [if_pos hh]
          obtain ⟨s', hs'⟩ := ihres
          refine ⟨s', ?_⟩
          exact ExS.loop_next (ExS.seq hcall23 (ExS.seq hite1 hbody)) (Or.inl rfl) ExS.skip hs'
        · rename_i hh
          rw [if_neg hh]
          obtain ⟨s', hs', hm', h19', h21'⟩ := ihres
          refine ⟨s', ?_, hm', h19', h21'⟩
          exact ExS.loop_next (ExS.seq hcall23 (ExS.seq hite1 hbody)) (Or.inl rfl) ExS.skip hs'
      · have hb0sq : (pieceByte (p.pieceAt sq)).toNat ≠ 0 := by
          intro hz
          have : p.isEmpty sq = true := by
            rw [isEmpty_bb p sq]
            simp [bb, sq.isLt, hz]
          exact hempty this
        have hsq_some : Square.mk? row col = some sq := by
          simp [sq, Square.mk?, hrowb, hcolb]
          omega
        simp [walkErr, hne_cursor, hsq_some, hempty]
        -- occupied: return false
        let sret := s25
        have hbody : ExS Gen.prog s25
            (.ite (.var 25)
              (.seq (.ite (.bin .ne (some ⟨32, true⟩) (.cast ⟨32, true⟩
                  (.load (.int ⟨8, false⟩) (.index (.field (.var 0) 0)
                    (.bin .add (some ⟨32, true⟩) (.bin .mul (some ⟨32, true⟩) (.var 19) (.const (.int ⟨32, true⟩ 9))) (.var 21)) 1)))
                  (.const (.int ⟨32, true⟩ 0)))
                  (.ret (some (.cast ⟨8, false⟩ (.bin .ne (some ⟨32, true⟩) (.const (.int ⟨32, true⟩ 0)) (.const (.int ⟨32, true⟩ 0)))))) .skip)
                (.seq (.set 19 (.cast ⟨32, true⟩ (.bin .add (some ⟨32, true⟩) (.cast ⟨32, true⟩ (.var 19)) (.cast ⟨32, true⟩ (.var 17)))))
                  (.set 21 (.cast ⟨32, true⟩ (.bin .add (some ⟨32, true⟩) (.cast ⟨32, true⟩ (.var 21)) (.cast ⟨32, true⟩ (.var 18)))))))
              .brk) (.ret (some false8)) sret := by
          refine ExS.ite (bc := true) (EvE.var (s := s25) (i := 25) (v := boolVal true) (by simp [s25, Locals.upd, boolVal, IntTy.i32])) (by simp [truthy_boolVal]) ?_
          refine ExS.seq_ret ?_
          refine ExS.ite (bc := true) hcond_ev (by simp [truthy_boolVal, hb0sq]) ?_
          refine ExS.ret ?_
          exact EvE_of_eval (n := 3) (by simp [evalExpr, evalBin, isPtr, evalBinInt, binInt, intOf, evalCast, false8, boolVal, IntTy.i32, IntTy.u8, IntTy.toInt, IntTy.wrap, IntTy.modulus, Res.bind])
        refine ⟨sret, ?_⟩
        exact ExS.loop_ret (ExS.seq hcall23 (ExS.seq hite1 hbody))
    · have hrowNe : row ≠ (Square.row to : Int) := hrowEq
      -- first ite: row != row23 (true), set 25 = 1
      let s23 : State := {s with locals := s.locals.upd 23 (i32 (Square.row to))}
      have hcall23 : ExS Gen.prog s (.call (some 23) 7 [(.var 2)]) .normal s23 := call_row_of_gen to h2 23
      have hne23' := evI_ne (EvE.var (s := s23) (i := 19) (v := i32 row) (by simpa [s23, Locals.upd] using h19))
        (EvE.var (s := s23) (i := 23) (v := i32 (Square.row to)) (by simp [s23, Locals.upd]))
        (by unfold Sm; omega) (sm_sqrow to)
      have hne23 : EvE Gen.prog s23 (.bin .ne (some ⟨32, true⟩) (.var 19) (.var 23)) (boolVal true) := by
        simpa [hrowNe] using hne23'
      let s25 : State := {s23 with locals := s23.locals.upd 25 (.int ⟨32, true⟩ 1)}
      have hite1 : ExS Gen.prog s23
          (.ite (.bin .ne (some ⟨32, true⟩) (.var 19) (.var 23)) (.set 25 (.const (.int ⟨32, true⟩ 1)))
            (.seq (.call (some 24) 8 [(.var 2)])
              (.set 25 (.lor (.const (.int ⟨32, true⟩ 0)) (.bin .ne (some ⟨32, true⟩) (.var 21) (.var 24))))))
          .normal s25 := by
        refine ExS.ite (bc := true) hne23 (by simp [truthy_boolVal]) ?_
        simpa [s25, Locals.upd] using ExS.set (EvE.const (.int ⟨32, true⟩ 1))
      have hload := load_piece p m hm to rs cs row col hrowb hcolb
        (s := s25)
        (by simpa [s25, s23, Locals.upd] using h0)
        (by simp [s25, s23, Locals.upd, h19])
        (by simp [s25, s23, Locals.upd, h21])
        (by simp [s25, s23, hmem])
      have hb_sq : (pieceByte (p.pieceAt sq)).toNat < 256 := UInt8.toNat_lt _
      have hcond_ev : EvE Gen.prog s25 (.bin .ne (some ⟨32, true⟩) (.cast ⟨32, true⟩
          (.load (.int ⟨8, false⟩) (.index (.field (.var 0) 0)
            (.bin .add (some ⟨32, true⟩) (.bin .mul (some ⟨32, true⟩) (.var 19) (.const (.int ⟨32, true⟩ 9))) (.var 21)) 1)))
          (.const (.int ⟨32, true⟩ 0))) (boolVal (decide ((pieceByte (p.pieceAt sq)).toNat ≠ 0))) := by
        have hl : EvE Gen.prog s25
            (.load (.int ⟨8, false⟩) (.index (.field (.var 0) 0)
              (.bin .add (some ⟨32, true⟩) (.bin .mul (some ⟨32, true⟩) (.var 19) (.const (.int ⟨32, true⟩ 9))) (.var 21)) 1))
            (u8 (pieceByte (p.pieceAt sq)).toNat) := by
          simpa [s25, s23, Locals.upd] using hload
        exact ev_ne0e2 hb_sq hl
      by_cases hempty : p.isEmpty sq = true
      · have hb0sq : (pieceByte (p.pieceAt sq)).toNat = 0 := by
          rw [isEmpty_bb p sq] at hempty
          simp [bb, sq.isLt] at hempty
          exact hempty
        have hsq_some : Square.mk? row col = some sq := by simp [sq, Square.mk?, hrowb, hcolb]; omega
        simp [walkErr, hne_cursor, hsq_some, hempty]
        have hcond_ev0 : EvE Gen.prog s25 (.bin .ne (some ⟨32, true⟩) (.cast ⟨32, true⟩
            (.load (.int ⟨8, false⟩) (.index (.field (.var 0) 0)
              (.bin .add (some ⟨32, true⟩) (.bin .mul (some ⟨32, true⟩) (.var 19) (.const (.int ⟨32, true⟩ 9))) (.var 21)) 1)))
            (.const (.int ⟨32, true⟩ 0))) (boolVal false) := by simpa [hb0sq] using hcond_ev
        let s19 : State := {s25 with locals := s25.locals.upd 19 (i32 (row + rs))}
        let s21 : State := {s19 with locals := s19.locals.upd 21 (i32 (col + cs))}
        have hbody : ExS Gen.prog s25
            (.ite (.var 25)
              (.seq (.ite (.bin .ne (some ⟨32, true⟩) (.cast ⟨32, true⟩
                  (.load (.int ⟨8, false⟩) (.index (.field (.var 0) 0)
                    (.bin .add (some ⟨32, true⟩) (.bin .mul (some ⟨32, true⟩) (.var 19) (.const (.int ⟨32, true⟩ 9))) (.var 21)) 1)))
                  (.const (.int ⟨32, true⟩ 0)))
                  (.ret (some (.cast ⟨8, false⟩ (.bin .ne (some ⟨32, true⟩) (.const (.int ⟨32, true⟩ 0)) (.const (.int ⟨32, true⟩ 0)))))) .skip)
                (.seq (.set 19 (.cast ⟨32, true⟩ (.bin .add (some ⟨32, true⟩) (.cast ⟨32, true⟩ (.var 19)) (.cast ⟨32, true⟩ (.var 17)))))
                  (.set 21 (.cast ⟨32, true⟩ (.bin .add (some ⟨32, true⟩) (.cast ⟨32, true⟩ (.var 21)) (.cast ⟨32, true⟩ (.var 18)))))))
              .brk) .normal s21 := by
          refine ExS.ite (bc := true) (EvE.var (s := s25) (i := 25) (v := boolVal true) (by simp [s25, Locals.upd, boolVal, IntTy.i32])) (by simp [truthy_boolVal]) ?_
          refine ExS.seq (ExS.ite (bc := false) hcond_ev0 (by simp [truthy_boolVal]) ExS.skip) ?_
          refine ExS.seq (s1 := s19) (s2 := s21) ?_ ?_
          · apply ExS.set; apply evCastI32 (by unfold Sm; omega)
            exact evI_add
              (evCastI32 (by unfold Sm; omega) (EvE.var (s := s25) (i := 19) (v := i32 row)
                (by simpa [s25, s23, Locals.upd] using h19)))
              (evCastI32 (by unfold Sm; omega) (EvE.var (s := s25) (i := 17) (v := i32 rs)
                (by simpa [s25, s23, Locals.upd] using h17)))
              (by unfold Sm; omega) (by unfold Sm; omega)
          · apply ExS.set; apply evCastI32 (by unfold Sm; omega)
            exact evI_add
              (evCastI32 (by unfold Sm; omega) (EvE.var (s := s19) (i := 21) (v := i32 col)
                (by simpa [s19, s25, s23, Locals.upd] using h21)))
              (evCastI32 (by unfold Sm; omega) (EvE.var (s := s19) (i := 18) (v := i32 cs)
                (by simpa [s19, s25, s23, Locals.upd] using h18)))
              (by unfold Sm; omega) (by unfold Sm; omega)
        have ihres := ih (row + rs) (col + cs) s21 hrow' hcol' hbnd'
            (by simpa [s21, s19, s25, s23, Locals.upd] using h0)
            (by simpa [s21, s19, s25, s23, Locals.upd] using h2)
            (by simpa [s21, s19, s25, s23, Locals.upd] using h17)
            (by simpa [s21, s19, s25, s23, Locals.upd] using h18)
            (by simp [s21, s19, Locals.upd])
            (by simp [s21, Locals.upd])
            (by simp [s21, s19, s25, s23, hmem])
        split at ihres
        · rename_i hh; rw [if_pos hh]; obtain ⟨s', hs'⟩ := ihres
          refine ⟨s', ?_⟩
          exact ExS.loop_next (ExS.seq hcall23 (ExS.seq hite1 hbody)) (Or.inl rfl) ExS.skip hs'
        · rename_i hh; rw [if_neg hh]; obtain ⟨s', hs', hm', h19', h21'⟩ := ihres
          refine ⟨s', ?_, hm', h19', h21'⟩
          exact ExS.loop_next (ExS.seq hcall23 (ExS.seq hite1 hbody)) (Or.inl rfl) ExS.skip hs'
      · have hb0sq : (pieceByte (p.pieceAt sq)).toNat ≠ 0 := by
          intro hz
          have : p.isEmpty sq = true := by
            rw [isEmpty_bb p sq]
            simp [bb, sq.isLt, hz]
          exact hempty this
        have hsq_some : Square.mk? row col = some sq := by simp [sq, Square.mk?, hrowb, hcolb]; omega
        simp [walkErr, hne_cursor, hsq_some, hempty]
        let sret := s25
        have hbody : ExS Gen.prog s25
            (.ite (.var 25)
              (.seq (.ite (.bin .ne (some ⟨32, true⟩) (.cast ⟨32, true⟩
                  (.load (.int ⟨8, false⟩) (.index (.field (.var 0) 0)
                    (.bin .add (some ⟨32, true⟩) (.bin .mul (some ⟨32, true⟩) (.var 19) (.const (.int ⟨32, true⟩ 9))) (.var 21)) 1)))
                  (.const (.int ⟨32, true⟩ 0)))
                  (.ret (some (.cast ⟨8, false⟩ (.bin .ne (some ⟨32, true⟩) (.const (.int ⟨32, true⟩ 0)) (.const (.int ⟨32, true⟩ 0)))))) .skip)
                (.seq (.set 19 (.cast ⟨32, true⟩ (.bin .add (some ⟨32, true⟩) (.cast ⟨32, true⟩ (.var 19)) (.cast ⟨32, true⟩ (.var 17)))))
                  (.set 21 (.cast ⟨32, true⟩ (.bin .add (some ⟨32, true⟩) (.cast ⟨32, true⟩ (.var 21)) (.cast ⟨32, true⟩ (.var 18)))))))
              .brk) (.ret (some false8)) sret := by
          refine ExS.ite (bc := true) (EvE.var (s := s25) (i := 25) (v := boolVal true) (by simp [s25, Locals.upd, boolVal, IntTy.i32])) (by simp [truthy_boolVal]) ?_
          refine ExS.seq_ret ?_
          refine ExS.ite (bc := true) hcond_ev (by simp [truthy_boolVal, hb0sq]) ?_
          refine ExS.ret ?_
          exact EvE_of_eval (n := 3) (by simp [evalExpr, evalBin, isPtr, evalBinInt, binInt, intOf, evalCast, false8, boolVal, IntTy.i32, IntTy.u8, IntTy.toInt, IntTy.wrap, IntTy.modulus, Res.bind])
        refine ⟨sret, ?_⟩
        exact ExS.loop_ret (ExS.seq hcall23 (ExS.seq hite1 hbody))

end Shogi.C.Proofs
