/-
  T8: `make_legal_probe`, part 4 — access helpers for the probe's three blocks.
-/
import Shogi.C.Proofs.Probe3

namespace Shogi.C.Proofs
variable {posBlock : Nat}
open MiniC Shogi Shogi.C

section access
variable {s : State} {P : List UInt8} (hP : P.length = 114) (hl0 : s.locals 0 = some (posPtr' posBlock))
  (hmp : s.mem posBlock = some P)

include hP hl0 hmp in
/-- `position->…[x]` at byte `base + x` of the position (index of unsigned type). -/
theorem ev_pos_u {e : Expr} {base x : Nat} {t : IntTy} (ht : t.signed = false)
    (he : EvE Gen.prog s e (.int t x)) (hx : base + x < 114) :
    EvE Gen.prog s (.load (.int ⟨8, false⟩) (.index (.field (.var 0) base) e 1))
      (.int IntTy.u8 (P.getD (base + x) 0).toNat) := by
  refine load_u8_at (o := 0 + base + x * 1) (EvE.index (pb := .ptr posBlock (0 + base))
    (EvE.field (off := base) (EvE.var hl0) (by simp [ptrAddN, posPtr', hmp, hP]; omega)) (elem := 1) he
    (by simp [ht, ptrAddN, hmp, hP]; omega)) hmp (by rw [hP]; omega) |> fun h => by
      simpa using h

include hP hl0 hmp in
theorem st_pos_u {e ev : Expr} {base x v : Nat} {t : IntTy} (ht : t.signed = false)
    (he : EvE Gen.prog s e (.int t x)) (hx : base + x < 114) (hv : EvE Gen.prog s ev (.int IntTy.u8 v))
    (hro : s.ro = false) :
    ExS Gen.prog s (.store (.int ⟨8, false⟩) (.index (.field (.var 0) base) e 1) ev) .normal
      { s with mem := s.mem.write posBlock (base + x) (encodeLE 1 v) } := by
  have := ExS.store (p := Gen.prog) (s := s) (ty := .int ⟨8, false⟩) (pa := .ptr posBlock (0 + base + x * 1))
    (EvE.index (pb := .ptr posBlock (0 + base))
      (EvE.field (off := base) (EvE.var hl0) (by simp [ptrAddN, posPtr', hmp, hP]; omega)) (elem := 1) he
      (by simp [ht, ptrAddN, hmp, hP]; omega)) hv hro
    (by simp only [store, ite_true, show IntTy.u8 = (⟨8, false⟩ : IntTy) from rfl, IntTy.bytes]
        exact writeBytes_ok hmp (by simp [encodeLE_length, hP]; omega))
  simpa [IntTy.bytes] using this

end access

theorem ev_blk_u8 {s : State} {j b k : Nat} {B : List UInt8} (hl : s.locals j = some (.ptr b 0))
    (hm : s.mem b = some B) (hk : k < B.length) :
    EvE Gen.prog s (.load (.int ⟨8, false⟩) (.field (.var j) k)) (.int IntTy.u8 (B.getD k 0).toNat) := by
  have := load_u8_at (o := 0 + k) (EvE.field (off := k) (EvE.var hl) (by simp [ptrAddN, hm]; omega)) hm (by omega)
  simpa using this

theorem callS {s : State} {d f : Nat} {fn : Func} {args : List Expr} {vs : List Val} {v : Val}
    (hf : Gen.prog f = some fn) (hp : pureS fn.body = true)
    (hlen : fn.params.length = vs.length) (hrun : run f vs = some (some v))
    (hargs : EvArgs Gen.prog s args vs) :
    ExS Gen.prog s (.call (some d) f args) .normal { s with locals := s.locals.upd d v } :=
  ExS.call_dst (s' := ⟨frameLocals fn.params vs, s.mem, s.ro⟩) hargs hf hlen
    (pure_callS hf hp hlen hrun s.mem s.ro)

theorem run_type (q : Piece) : run Gen.fid_shogi_piece_type [u8 q.code] = some (some (u32 q.type.code)) := by
  obtain ⟨c, t⟩ := q; cases c <;> cases t <;> decide +kernel
theorem run_unpromote (t : PieceType) :
    run Gen.fid_shogi_unpromoted_type [u32 t.code] = some (some (u32 t.unpromote.code)) := by
  cases t <;> decide +kernel
theorem run_promote (t : PieceType) : run Gen.fid_promoted_type [u32 t.code] = some (some (u32 t.promote.code)) := by
  cases t <;> decide +kernel
theorem run_hand_index (t : PieceType) :
    run Gen.fid_hand_index [u32 t.code] =
      some (some (i32 (match t.handIndex with | some i => (i.val : Int) | none => -1))) := by
  cases t <;> decide +kernel
theorem run_piece (c : Color) (t : PieceType) :
    run Gen.fid_shogi_piece [u32 c.idx, u32 t.code] = some (some (u8 (Piece.code ⟨c, t⟩))) := by
  cases c <;> cases t <;> decide +kernel

theorem pureS_unpromote : pureS Gen.shogi_unpromoted_type.body = true := by decide
theorem pureS_promote : pureS Gen.promoted_type.body = true := by decide
theorem pureS_hand_index : pureS Gen.hand_index.body = true := by decide
theorem pureS_type : pureS Gen.shogi_piece_type.body = true := by decide
theorem pureS_piece : pureS Gen.shogi_piece.body = true := by decide

section hand
variable {s : State} {P : List UInt8} (hP : P.length = 114) (hl0 : s.locals 0 = some (posPtr' posBlock))
  (hmp : s.mem posBlock = some P) {c : Color} (hl4 : s.locals 4 = some (.int IntTy.u32 c.idx))
  {j : Nat} {i : Nat} (hi : i < 7) (hlj : s.locals j = some (i32 (i : Int)))

include hP hl0 hmp hl4 hi hlj in
theorem hand_ptr (hc : c.idx < 2) :
    EvE Gen.prog s (.index (.index (.field (.var 0) 81) (.var 4) 7) (.var j) 1)
      (.ptr posBlock (81 + 7 * c.idx + i)) := by
  refine EvE.index (pb := .ptr posBlock (0 + 81 + c.idx * 7))
    (EvE.index (pb := .ptr posBlock (0 + 81)) (EvE.field (EvE.var hl0) (by simp [ptrAddN, posPtr', hmp, hP]))
      (EvE.var hl4) (by simp [IntTy.u32, ptrAddN, hmp, hP]; omega)) (EvE.var hlj) ?_
  have hw : IntTy.i32.wrap (i : Int) = i := wrap_nat32 i (by omega)
  rw [hw]
  simp [IntTy.i32, IntTy.toInt, ptrAdd, hmp, hP, show ¬ (2147483648 ≤ i) by omega]
  rw [if_pos (by omega)]; congr 2; omega

include hP hl0 hmp hl4 hi hlj in
theorem ev_hand_slot :
    EvE Gen.prog s (.load (.int ⟨8, false⟩) (.index (.index (.field (.var 0) 81) (.var 4) 7) (.var j) 1))
      (.int IntTy.u8 (P.getD (81 + 7 * c.idx + i) 0).toNat) :=
  load_u8_at (hand_ptr hP hl0 hmp hl4 hi hlj (by cases c <;> decide)) hmp
    (by rw [hP]; have : c.idx < 2 := by cases c <;> decide
        omega)

include hP hl0 hmp hl4 hi hlj in
theorem st_hand_slot {ev : Expr} {v : Nat} (hv : EvE Gen.prog s ev (.int IntTy.u8 v)) (hro : s.ro = false) :
    ExS Gen.prog s (.store (.int ⟨8, false⟩) (.index (.index (.field (.var 0) 81) (.var 4) 7) (.var j) 1) ev) .normal
      { s with mem := s.mem.write posBlock (81 + 7 * c.idx + i) (encodeLE 1 v) } := by
  have hc : c.idx < 2 := by cases c <;> decide
  have := ExS.store (p := Gen.prog) (s := s) (ty := .int ⟨8, false⟩) (hand_ptr hP hl0 hmp hl4 hi hlj hc) hv hro
    (by simp only [store, ite_true, show IntTy.u8 = (⟨8, false⟩ : IntTy) from rfl, IntTy.bytes]
        exact writeBytes_ok hmp (by simp [encodeLE_length, hP]; omega))
  simpa [IntTy.bytes] using this

end hand

section handu
variable {s : State} {P : List UInt8} (hP : P.length = 114) (hl0 : s.locals 0 = some (posPtr' posBlock))
  (hmp : s.mem posBlock = some P) {c : Color} (hl4 : s.locals 4 = some (.int IntTy.u32 c.idx))
  {j : Nat} {i : Nat} (hi : i < 7) (hlj : s.locals j = some (.int IntTy.u32 i))

include hP hl0 hmp hl4 hi hlj in
theorem hand_ptr_u (hc : c.idx < 2) :
    EvE Gen.prog s (.index (.index (.field (.var 0) 81) (.var 4) 7) (.var j) 1)
      (.ptr posBlock (81 + 7 * c.idx + i)) := by
  refine EvE.index (pb := .ptr posBlock (0 + 81 + c.idx * 7))
    (EvE.index (pb := .ptr posBlock (0 + 81)) (EvE.field (EvE.var hl0) (by simp [ptrAddN, posPtr', hmp, hP]))
      (EvE.var hl4) (by simp [IntTy.u32, ptrAddN, hmp, hP]; omega)) (EvE.var hlj) ?_
  simp [IntTy.u32, ptrAddN, hmp, hP]
  rw [if_pos (by omega)]; congr 2; omega

include hP hl0 hmp hl4 hi hlj in
theorem ev_hand_slot_u :
    EvE Gen.prog s (.load (.int ⟨8, false⟩) (.index (.index (.field (.var 0) 81) (.var 4) 7) (.var j) 1))
      (.int IntTy.u8 (P.getD (81 + 7 * c.idx + i) 0).toNat) :=
  load_u8_at (hand_ptr_u hP hl0 hmp hl4 hi hlj (by cases c <;> decide)) hmp
    (by rw [hP]; have : c.idx < 2 := by cases c <;> decide
        omega)

include hP hl0 hmp hl4 hi hlj in
theorem st_hand_slot_u {ev : Expr} {v : Nat} (hv : EvE Gen.prog s ev (.int IntTy.u8 v)) (hro : s.ro = false) :
    ExS Gen.prog s (.store (.int ⟨8, false⟩) (.index (.index (.field (.var 0) 81) (.var 4) 7) (.var j) 1) ev) .normal
      { s with mem := s.mem.write posBlock (81 + 7 * c.idx + i) (encodeLE 1 v) } := by
  have hc : c.idx < 2 := by cases c <;> decide
  have := ExS.store (p := Gen.prog) (s := s) (ty := .int ⟨8, false⟩) (hand_ptr_u hP hl0 hmp hl4 hi hlj hc) hv hro
    (by simp only [store, ite_true, show IntTy.u8 = (⟨8, false⟩ : IntTy) from rfl, IntTy.bytes]
        exact writeBytes_ok hmp (by simp [encodeLE_length, hP]; omega))
  simpa [IntTy.bytes] using this

end handu

end Shogi.C.Proofs
