/-
  R3: `validate_material` (fid 48) refines the spec's `Position.materialOk`.
  The C fills a 7-entry maximum array, counts each unpromoted family on the
  board into a total array, adds both hands, and rejects if any total exceeds
  the maximum. The proof keeps the two arrays as symbolic functions of the
  loop index.
-/
import Shogi.C.Proofs.Pseudo4
import Shogi.C.Proofs.EntryPoints

set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

namespace Shogi.C.Proofs
variable {posBlock : Nat}
open MiniC Shogi Shogi.C

/-- The C maximum array (handMax) at each slot. -/
def maxArr (i : Fin 7) : Nat := PieceType.handMax i

/-- The family index of a piece byte, or 7 if it has no hand slot. -/
def famOfByte (b : UInt8) : Nat :=
  match PieceType.ofCode (b.toNat % 16) with
  | none => 7
  | some t =>
    match t.unpromote.handIndex with
    | some i => i.val
    | none => 7

/-- Board-family count among the first `k` squares. -/
def famAt (p : Position) (s : Nat) : Nat :=
  if h : s < 81 then famOfByte (pieceByte (p.pieceAt ⟨s, h⟩)) else 7

def boardFamCount (p : Position) (k : Nat) (i : Fin 7) : Nat :=
  (List.range k).countP (fun s => famAt p s = i.val)

@[simp] theorem code_mod_16 (t : PieceType) : t.code % 16 = t.code :=
  Nat.mod_eq_of_lt (by cases t <;> decide)

theorem famOfByte_eq (o : Option Piece) (i : Fin 7) :
    (famOfByte (pieceByte o) = i.val) ↔
      (match o with | some pc => pc.type.unpromote.handIndex == some i | none => false) := by
  cases o with
  | none => simp [pieceByte, famOfByte, PieceType.ofCode]; omega
  | some pc =>
      obtain ⟨c, t⟩ := pc
      cases c <;> cases t <;>
        simp [pieceByte, famOfByte, Piece.code, PieceType.ofCode_code,
          PieceType.unpromote, PieceType.handIndex, Fin.ext_iff, code_mod_16] <;> omega

theorem boardFamCount_take (p : Position) (hs : p.board.length = 81) (k : Nat) (i : Fin 7) :
    boardFamCount p k i =
      (p.board.take k).countP (fun o => famOfByte (pieceByte o) = i.val) := by
  induction k with
  | zero => simp [boardFamCount]
  | succ k ih =>
      rw [show boardFamCount p (k + 1) i =
          boardFamCount p k i + (if famAt p k = i.val then 1 else 0) by
        unfold boardFamCount
        rw [List.range_succ, List.countP_append]
        simp]
      rw [ih]
      by_cases hk81 : k < p.board.length
      · have ht : p.board.take (k + 1) = p.board.take k ++ [p.board[k]] := by
          rw [List.take_succ]
          simp [List.getElem?_eq_getElem hk81]
        rw [ht, List.countP_append]
        congr 1
        have hget : pieceByte p.board[k] = pieceByte (p.pieceAt ⟨k, by omega⟩) := by
          simp [Position.pieceAt, List.getD_eq_getElem?_getD, hk81]
        have hfameq : famAt p k = famOfByte (pieceByte p.board[k]) := by
          unfold famAt
          rw [dif_pos (show k < 81 by omega)]
          rw [hget]
        rw [hfameq]
        simp
      · have hlen : p.board.length ≤ k := by omega
        have ht : p.board.take (k + 1) = p.board.take k := by
          rw [List.take_of_length_le (show p.board.length ≤ k + 1 by omega),
            List.take_of_length_le (show p.board.length ≤ k by omega)]
        rw [ht]
        have hb : p.board[k]? = none := List.getElem?_eq_none hlen
        simp [famAt, show ¬ k < 81 by omega, hb]
        omega

theorem boardFamCount_81 (p : Position) (hs : p.board.length = 81) (i : Fin 7) :
    boardFamCount p 81 i + p.hand .black i + p.hand .white i = p.familyCount i := by
  rw [boardFamCount_take p hs, List.take_of_length_le (by omega)]
  unfold Position.familyCount
  apply congrArg (fun t => t + p.hand Color.black i + p.hand Color.white i)
  apply List.countP_congr
  intro o ho
  simp [famOfByte_eq]
  cases o <;> simp


/-- The unpromoted type code after `shogi_piece_type` + `shogi_unpromoted_type`. -/
def unpromotedCode (c : Nat) : Nat :=
  match PieceType.ofCode c with
  | none => 0
  | some t => t.unpromote.code

/-- The hand slot of a piece byte after unpromotion, or -1. -/
def byteFam (b : UInt8) : Int :=
  match PieceType.ofCode (unpromotedCode (b.toNat % 16)) with
  | none => -1
  | some t => match t.handIndex with
    | some i => (i.val : Int)
    | none => -1

theorem hand_index_compose (b : Fin 256) (h15 : b.val % 16 ≠ 15) :
    run Gen.fid_hand_index [u32 (unpromotedCode (b.val % 16))] =
      some (some (i32 (byteFam ⟨b.val, b.isLt⟩))) := by
  cases hb : PieceType.ofCode (b.val % 16) with
  | none =>
      have hc : b.val % 16 < 16 := Nat.mod_lt _ (by decide)
      have hall : ∀ c : Fin 16, c.val ≠ 0 → c.val ≠ 15 → PieceType.ofCode c.val ≠ none := by decide +kernel
      have h0 : b.val % 16 = 0 := by
        by_cases h : b.val % 16 = 0
        · exact h
        · exact False.elim (hall ⟨b.val % 16, hc⟩ h h15 hb)
      simp [unpromotedCode, byteFam, hb, h0]
      decide +kernel
  | some t =>
      simp [unpromotedCode, byteFam, hb, PieceType.ofCode_code]
      cases htu : t.unpromote <;> decide +kernel


/-- Store a u32 at `blk[4*i .. 4*i+4)`. -/
theorem array_store {s : State} {j b i v : Nat} {blk : Block} (hv : v < 2 ^ 31)
    (hj : s.locals j = some (.ptr b 0)) (hb : s.mem b = some blk) (hlen : 4 * i + 4 ≤ blk.length)
    (hro : s.ro = false) :
    ExS Gen.prog s
      (.store (.int ⟨32, false⟩) (.index (.var j) (.const (.int ⟨64, false⟩ i)) 4)
        (.cast ⟨32, false⟩ (.const (.int ⟨32, true⟩ v)))) .normal
      { s with mem := s.mem.write b (4 * i) (encodeLE 4 v) } := by
    refine ExS.store (pa := .ptr b (4 * i)) (v := .int ⟨32, false⟩ v)
      (EvE.index (EvE.var hj) (EvE.const (v := .int IntTy.u64 i))
        (by simp [IntTy.u64, ptrAddN, hb, show i * 4 = 4 * i by omega, show 4 * i ≤ blk.length by omega]))
      (EvE_of_eval (n := 3) (by
        have h1 : IntTy.toInt IntTy.i32 v = (v : Int) := by simp [IntTy.toInt, IntTy.i32, IntTy.modulus]; omega
        have h2 : ((v : Int) % (4294967296 : Int)).toNat = v := by
          rw [Int.emod_eq_of_lt (by omega) (by omega)]
          simp
        simp [evalExpr, evalCast, IntTy.wrap, IntTy.modulus, h1, h2,
          Nat.mod_eq_of_lt (show v < 4294967296 by omega)]
        have h3 : ({ width := 32, signed := true } : IntTy).toInt v = (v : Int) := by
          simp [IntTy.toInt]; omega
        rw [h3]
        rw [Int.emod_eq_of_lt (by omega) (by omega)]
        simp)) hro ?_
    simp only [store, Ty.size, IntTy.bytes, ite_true]
    exact writeBytes_ok hb (by simpa [encodeLE_length] using hlen)

/-- Load the u32 at `blk[4*i .. 4*i+4)`. -/
theorem array_load {s : State} {j b i : Nat} {blk : Block}
    (hj : s.locals j = some (.ptr b 0)) (hb : s.mem b = some blk) (hlen : 4 * i + 4 ≤ blk.length) :
    EvE Gen.prog s
      (.load (.int ⟨32, false⟩) (.index (.var j) (.const (.int ⟨64, false⟩ i)) 4))
      (.int ⟨32, false⟩ (decodeLE ((blk.drop (4 * i)).take 4))) := by
    refine EvE.load (pa := .ptr b (4 * i))
      (EvE.index (EvE.var hj) (EvE.const (v := .int IntTy.u64 i))
        (by simp [IntTy.u64, ptrAddN, hb, show i * 4 = 4 * i by omega, show 4 * i ≤ blk.length by omega])) ?_
    simp only [load, readBytes, hb, Ty.size, IntTy.bytes, show 4*i + 4 ≤ blk.length by omega, ite_true]
    rfl


/-- Lift a kernel-checked `run` result to an `ExS` call in arbitrary memory. -/
theorem call_run {s : State} {d f : Nat} {fn : Func} {args : List Expr} {vs : List Val} {v : Val}
    (hf : Gen.prog f = some fn) (hp : pureS fn.body = true)
    (hlen : fn.params.length = vs.length) (hrun : run f vs = some (some v))
    (hargs : EvArgs Gen.prog s args vs) :
    ExS Gen.prog s (.call (some d) f args) .normal { s with locals := s.locals.upd d v } := by
  refine ExS.call_dst (s' := ⟨frameLocals fn.params vs, s.mem, s.ro⟩) hargs hf hlen ?_
  exact pure_callS hf hp hlen hrun s.mem s.ro

example : pureS Gen.shogi_piece_type.body = true := by decide
example : pureS Gen.shogi_unpromoted_type.body = true := by decide
example : pureS Gen.hand_index.body = true := by decide




theorem unpromoted_run_all : ∀ c : Fin 16, c.val ≠ 15 →
    run Gen.fid_shogi_unpromoted_type [u32 c.val] = some (some (u32 (unpromotedCode c.val))) := by
  decide +kernel

theorem piece_type_run_all : ∀ b : Fin 256,
    run Gen.fid_shogi_piece_type [u8 b.val] = some (some (u32 (b.val % 16))) := by
  decide +kernel



/-- A board byte never has nibble 15. -/
theorem board_nibble (p : Position) (hs : p.board.length = 81) (k : Nat) (hk : k < 81) :
    (pieceByte (p.pieceAt ⟨k, by omega⟩)).toNat % 16 ≠ 15 := by
  cases hp : p.pieceAt ⟨k, by omega⟩ with
  | none => simp [pieceByte]
  | some pc =>
      obtain ⟨c, t⟩ := pc
      simp [pieceByte, Piece.code]
      have ht : t.code ≤ 14 := by cases t <;> decide
      omega

/-- The three helper calls on the board byte at square `k` return the spec
    hand slot (or -1) in local 8, leaving memory and locals 0..3 unchanged. -/
theorem board_helper_calls (s : State) (p : Position) (hs : p.board.length = 81)
    (k : Nat) (hk : k < 81) (hm : s.mem posBlock = some (encode p))
    (h0 : s.locals 0 = some (posPtr' posBlock)) (h3 : s.locals 3 = some (u8 k)) :
    ∃ s', ExS Gen.prog s
      (.seq (.call (some 5) 2 [(.load (.int ⟨8, false⟩) (.index (.field (.var 0) 0) (.var 3) 1))])
        (.seq (.call (some 6) 4 [(.var 5)])
          (.seq (.set 4 (.var 6)) (.call (some 8) 13 [(.var 4)])))) .normal s' ∧
      s'.locals 8 = some (i32 (byteFam (pieceByte (p.pieceAt ⟨k, by omega⟩)))) ∧
      s'.mem = s.mem ∧ (∀ x, x ≠ 5 → x ≠ 6 → x ≠ 4 → x ≠ 8 → s'.locals x = s.locals x) := by
  let b := pieceByte (p.pieceAt ⟨k, by omega⟩)
  have hb15 : b.toNat % 16 ≠ 15 := board_nibble p hs k hk
  -- load the board byte
  have hbload : EvE Gen.prog s (.load (.int ⟨8, false⟩) (.index (.field (.var 0) 0) (.var 3) 1)) (u8 b.toNat) := by
    refine EvE.load (pa := .ptr posBlock k)
      (EvE.index (EvE.field (pb := .ptr posBlock 0) (EvE.var h0) (by
          show ptrAddN s.mem (.ptr posBlock 0) 0 = .ok (.ptr posBlock 0)
          simp [ptrAddN, hm]))
        (EvE.var h3) (by
        have hlen : (encode p).length = 114 := encode_length p
        simp [IntTy.u8, ptrAddN, posPtr', hm, hlen, show k ≤ 114 by omega])) ?_
    have hread := readBoard hm k hk
    simp [load, hread, Ty.size, IntTy.bytes, decodeLE, b]
    rfl
  have e1 : ExS Gen.prog s
      (.call (some 5) 2 [(.load (.int ⟨8, false⟩) (.index (.field (.var 0) 0) (.var 3) 1))]) .normal
      { s with locals := s.locals.upd 5 (u32 (b.toNat % 16)) } := by
    apply call_run (f := Gen.fid_shogi_piece_type) (fn := Gen.shogi_piece_type)
      (vs := [u8 b.toNat]) (v := u32 (b.toNat % 16))
    · rfl
    · decide
    · rfl
    · exact piece_type_run_all ⟨b.toNat, UInt8.toNat_lt b⟩
    · exact EvArgs.cons hbload EvArgs.nil
  let s5 : State := { s with locals := s.locals.upd 5 (u32 (b.toNat % 16)) }
  have e2 : ExS Gen.prog s5 (.call (some 6) 4 [(.var 5)]) .normal
      { s5 with locals := s5.locals.upd 6 (u32 (unpromotedCode (b.toNat % 16))) } := by
    apply call_run (f := Gen.fid_shogi_unpromoted_type) (fn := Gen.shogi_unpromoted_type)
      (vs := [u32 (b.toNat % 16)]) (v := u32 (unpromotedCode (b.toNat % 16)))
    · rfl
    · decide
    · rfl
    · exact unpromoted_run_all ⟨b.toNat % 16, Nat.mod_lt _ (by decide)⟩ hb15
    · exact EvArgs.cons (EvE.var (by simp [s5, Locals.upd])) EvArgs.nil
  have e3 : ExS Gen.prog { s5 with locals := s5.locals.upd 6 (u32 (unpromotedCode (b.toNat % 16))) }
      (.set 4 (.var 6)) .normal
      { s5 with locals := (s5.locals.upd 6 (u32 (unpromotedCode (b.toNat % 16)))).upd 4 (u32 (unpromotedCode (b.toNat % 16))) } := ExS.set (EvE.var (by simp [Locals.upd]))
  let s7 : State := { s5 with locals := (s5.locals.upd 6 (u32 (unpromotedCode (b.toNat % 16)))).upd 4 (u32 (unpromotedCode (b.toNat % 16))) }
  have e4 : ExS Gen.prog s7 (.call (some 8) 13 [(.var 4)]) .normal
      { s7 with locals := s7.locals.upd 8 (i32 (byteFam b)) } := by
    apply call_run (f := Gen.fid_hand_index) (fn := Gen.hand_index)
      (vs := [u32 (unpromotedCode (b.toNat % 16))]) (v := i32 (byteFam b))
    · rfl
    · decide
    · rfl
    · exact hand_index_compose ⟨b.toNat, UInt8.toNat_lt b⟩ hb15
    · exact EvArgs.cons (EvE.var (by simp [s7, Locals.upd])) EvArgs.nil
  refine ⟨{ s7 with locals := s7.locals.upd 8 (i32 (byteFam b)) }, ?_, ?_, ?_, ?_⟩
  · exact ExS.seq e1 (ExS.seq e2 (ExS.seq e3 e4))
  · simp [s7, Locals.upd, b]
  · rfl
  · intro x hx5 hx6 hx4 hx8
    simp [s5, s7, Locals.upd, hx5, hx6, hx4, hx8]



/-- A 7-entry u32 array in memory. -/
def ArrEq (blk : Block) (f : Fin 7 → Nat) : Prop :=
  ∀ i : Fin 7, decodeLE ((blk.drop (4 * i.val)).take 4) = f i

theorem famOfByte_of_byteFam (b : UInt8) (hb15 : b.toNat % 16 ≠ 15) :
    famOfByte b = if byteFam b < 0 then 7 else (byteFam b).toNat := by
  cases hc : PieceType.ofCode (b.toNat % 16) with
  | none =>
      have hc0 : b.toNat % 16 = 0 := by
        have hlt : b.toNat % 16 < 16 := Nat.mod_lt _ (by decide)
        have hall : ∀ c : Fin 16, c.val ≠ 0 → c.val ≠ 15 → PieceType.ofCode c.val ≠ none := by decide +kernel
        by_cases h : b.toNat % 16 = 0
        · exact h
        · exact False.elim (hall ⟨b.toNat % 16, hlt⟩ h hb15 hc)
      simp [famOfByte, byteFam, unpromotedCode, hc, hc0, PieceType.ofCode]
  | some t =>
      cases ht : t.unpromote.handIndex with
      | none =>
          simp [famOfByte, byteFam, unpromotedCode, hc, ht, PieceType.ofCode_code]
      | some i =>
          simp [famOfByte, byteFam, unpromotedCode, hc, ht, PieceType.ofCode_code]
          omega


theorem boardFamCount_succ (p : Position) (k : Nat) (i : Fin 7) :
    boardFamCount p (k + 1) i = boardFamCount p k i + (if famAt p k = i.val then 1 else 0) := by
  unfold boardFamCount
  rw [List.range_succ, List.countP_append]
  simp


theorem byteFam_bound (b : UInt8) : byteFam b = -1 ∨ (byteFam b).toNat < 7 := by
  cases hc : PieceType.ofCode (unpromotedCode (b.toNat % 16)) with
  | none => left; simp [byteFam, hc]
  | some t =>
      cases ht : t.handIndex with
      | none => left; simp [byteFam, hc, ht]
      | some i => right; simp [byteFam, hc, ht]


/-- The C `.index (var 2) (var 7) 4` addressing for a slot `j < 7`. -/
theorem slot_index {s : State} {tb : Nat} {T : Block} (j : Fin 7)
    (h2 : s.locals 2 = some (.ptr tb 0))
    (h7 : s.locals 7 = some (i32 (j.val : Int)))
    (htb : s.mem tb = some T) (hlen : T.length = 28) :
    EvE Gen.prog s (.index (.var 2) (.var 7) 4) (.ptr tb (4 * j.val)) := by
  refine EvE.index (EvE.var h2) (EvE.var h7) ?_
  have hn : IntTy.wrap IntTy.i32 (j.val : Int) = j.val := by
    have hmod : (↑j.val % 4294967296 : Int) = j.val := Int.emod_eq_of_lt (by omega) (by omega)
    simp [IntTy.wrap, IntTy.modulus, IntTy.i32, hmod]
  have hdelta : IntTy.i32.toInt (IntTy.wrap IntTy.i32 (j.val : Int)) = j.val := by
    rw [hn]
    simp [IntTy.toInt, IntTy.i32, IntTy.modulus]
    omega
  rw [hdelta]
  unfold ptrAdd
  simp only [htb]
  have hnonneg : 0 ≤ (j.val : Int) * 4 := by omega
  have hle : (j.val : Int) * 4 ≤ (T.length : Int) := by rw [hlen]; omega
  simp [IntTy.i32, hnonneg, hle]
  omega

end Shogi.C.Proofs
