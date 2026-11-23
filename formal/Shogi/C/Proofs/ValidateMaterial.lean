/-
  R3: `validate_material` (fid 48) refines the spec's `Position.materialOk`.
  The C fills a 7-entry maximum array, counts each unpromoted family on the
  board into a total array, adds both hands, and rejects if any total exceeds
  the maximum. The proof keeps the two arrays as symbolic functions of the
  loop index.
-/
import Shogi.C.Proofs.Pseudo4
import Shogi.C.Proofs.EntryPoints
import Shogi.SfenTheorems

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
    ∃ s4 s5,
      ExS Gen.prog s
        (.seq (.call (some 5) 2 [(.load (.int ⟨8, false⟩) (.index (.field (.var 0) 0) (.var 3) 1))])
          (.seq (.call (some 6) 4 [(.var 5)]) (.set 4 (.var 6)))) .normal s4 ∧
      ExS Gen.prog s4 (.call (some 8) 13 [(.var 4)]) .normal s5 ∧
      s5.locals 8 = some (i32 (byteFam (pieceByte (p.pieceAt ⟨k, by omega⟩)))) ∧
      s5.mem = s.mem ∧ s5.ro = s.ro ∧
      (∀ x, x ≠ 5 → x ≠ 6 → x ≠ 4 → x ≠ 8 → s5.locals x = s.locals x) := by
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
  refine ⟨s7, { s7 with locals := s7.locals.upd 8 (i32 (byteFam b)) }, ?_, e4, ?_, ?_, rfl, ?_⟩
  · exact ExS.seq e1 (ExS.seq e2 e3)
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


/-- Load the u32 total at slot `j` of the array block `tb`. -/
theorem slot_load {s : State} {tb : Nat} {T : Block} (j : Fin 7) (val : Nat)
    (h2 : s.locals 2 = some (.ptr tb 0))
    (h7 : s.locals 7 = some (i32 (j.val : Int)))
    (htb : s.mem tb = some T) (hlen : T.length = 28)
    (hT : decodeLE ((T.drop (4*j.val)).take 4) = val) :
    EvE Gen.prog s (.load (.int ⟨32, false⟩) (.index (.var 2) (.var 7) 4))
      (.int ⟨32, false⟩ val) := by
  refine EvE.load (slot_index (s := s) j h2 h7 htb hlen) ?_
  simp only [load, readBytes, Ty.size, IntTy.bytes]
  rw [htb]
  simp [show 4 * j.val + 4 ≤ T.length by omega, hT]

theorem array_write_other (T : Block) (hlen : T.length = 28) (i j : Fin 7) (hij : i ≠ j) (v : Nat) :
    let T' := T.take (4*j.val) ++ encodeLE 4 v ++ T.drop (4*j.val + 4)
    decodeLE ((T'.drop (4*i.val)).take 4) = decodeLE ((T.drop (4*i.val)).take 4) := by
  intro T'
  have hijlt : i.val < j.val ∨ j.val < i.val := by omega
  rcases hijlt with hlt | hgt
  · -- i < j: the write is after the read window
    have h1 : 4 * i.val ≤ (T.take (4*j.val)).length := by simp [hlen]; omega
    rw [show T'.drop (4*i.val) = (T.take (4*j.val)).drop (4*i.val) ++
        (encodeLE 4 v ++ T.drop (4*j.val + 4)) by
      simp [T', List.drop_append_of_le_length h1]]
    rw [List.take_append_of_le_length (show 4 ≤ ((T.take (4*j.val)).drop (4*i.val)).length by simp [hlen]; omega)]
    -- (take 4j T).drop 4i = take (4j - 4i) (T.drop 4i)
    rw [show (T.take (4*j.val)).drop (4*i.val) = (T.drop (4*i.val)).take (4*j.val - 4*i.val) by
      rw [List.drop_take]]
    rw [List.take_take]
    simp [Nat.min_eq_left (show 4 ≤ 4*j.val - 4*i.val by omega)]
  · -- j < i: the write is before the read window
    have hA : (T.take (4*j.val)).length = 4*j.val := by
      simp [hlen, Nat.min_eq_left (show 4*j.val ≤ 28 by omega)]
    have hdropA : (T.take (4*j.val)).drop (4*i.val) = [] := by
      apply List.drop_eq_nil_of_le
      rw [hA]; omega
    have hdrop_part : T'.drop (4*i.val) = (encodeLE 4 v ++ T.drop (4*j.val+4)).drop (4*i.val - 4*j.val) := by
      dsimp [T']
      rw [List.drop_append]
      rw [List.drop_append]
      rw [hdropA]
      simp [hA, encodeLE_length]
      rw [List.drop_append]
      simp [encodeLE_length]
      exact congrArg (fun x => min (4 * (j : Nat) + 4 + x) (List.length T))
        (show 4 * (i : Nat) - (4 * (j : Nat) + 4) = 4 * (i : Nat) - 4 * (j : Nat) - 4 by omega)
    rw [hdrop_part]
    simp only [List.drop_append]
    have hk : 4 ≤ 4 * i.val - 4 * j.val := by omega
    have hdropenc : (encodeLE 4 v).drop (4*i.val - 4*j.val) = [] := by
      apply List.drop_eq_nil_of_le
      simp [encodeLE_length]; omega
    rw [hdropenc, List.nil_append]
    rw [← List.drop_drop]
    rw [List.drop_drop]
    rw [List.drop_drop]
    apply congrArg (fun x => decodeLE (List.take 4 (List.drop x T)))
    simp [encodeLE_length]
    omega


theorem byteFam_neg (b : UInt8) (h : byteFam b < 0) : byteFam b = -1 := by
  cases hc : PieceType.ofCode (unpromotedCode (b.toNat % 16)) with
  | none => simp [byteFam, hc]
  | some t =>
      cases ht : t.handIndex with
      | none => simp [byteFam, hc, ht]
      | some i => simp [byteFam, hc, ht] at h; omega

def Inv0T (p : Position) (m : Mem) (mb tb : Nat) (k : Nat) (s : State) : Prop :=
  ∃ MB T,
    s.locals 0 = some (posPtr' posBlock) ∧ s.locals 1 = some (.ptr mb 0) ∧
    s.locals 2 = some (.ptr tb 0) ∧ s.locals 3 = some (u8 k) ∧
    s.mem mb = some MB ∧ MB.length = 28 ∧ ArrEq MB maxArr ∧
    s.mem tb = some T ∧ T.length = 28 ∧
    (∀ i : Fin 7, decodeLE ((T.drop (4*i.val)).take 4) = boardFamCount p k i) ∧
    s.mem posBlock = some (encode p) ∧
    mb ≠ tb ∧ mb ≠ 0 ∧ tb ≠ 0 ∧ posBlock ≠ mb ∧ posBlock ≠ tb ∧
    (∀ b, b ≠ 0 → b ≠ mb → b ≠ tb → s.mem b = m b) ∧ s.ro = false

def loop0BodyStmt : Stmt :=
  .ite (.bin .lt (some ⟨32, true⟩) (.cast ⟨32, true⟩ (.var 3)) (.const (.int ⟨32, true⟩ 81)))
    (.seq (.seq (.call (some 5) 2 [(.load (.int ⟨8, false⟩) (.index (.field (.var 0) 0) (.var 3) 1))])
      (.seq (.call (some 6) 4 [(.var 5)]) (.set 4 (.var 6))))
      (.seq (.seq (.call (some 8) 13 [(.var 4)]) (.set 7 (.var 8)))
        (.ite (.bin .ge (some ⟨32, true⟩) (.var 7) (.const (.int ⟨32, true⟩ 0)))
          (.store (.int ⟨32, false⟩) (.index (.var 2) (.var 7) 4) (.cast ⟨32, false⟩
            (.bin .add (some ⟨32, false⟩) (.cast ⟨32, false⟩
              (.load (.int ⟨32, false⟩) (.index (.var 2) (.var 7) 4))) (.const (.int ⟨32, false⟩ 1))))) .skip)))
    .brk

structure BodyResult (p : Position) (m : Mem) (mb tb : Nat) (k : Nat) (s s1 : State) (T : Block) : Prop where
  exs : ExS Gen.prog s loop0BodyStmt .normal s1
  hmem_tb : s1.mem tb = some T
  hlenT : T.length = 28
  hTot : ∀ i : Fin 7, decodeLE ((T.drop (4*i.val)).take 4) = boardFamCount p (k+1) i
  hloc0 : s1.locals 0 = s.locals 0
  hloc1 : s1.locals 1 = s.locals 1
  hloc2 : s1.locals 2 = s.locals 2
  hloc3 : s1.locals 3 = s.locals 3
  hro : s1.ro = s.ro
  hmem_mb : s1.mem mb = s.mem mb
  hmem_pos : s1.mem posBlock = s.mem posBlock
  hframe : ∀ b, b ≠ 0 → b ≠ mb → b ≠ tb → s1.mem b = s.mem b

-- one body iteration: condition true, helper calls, increment or skip, outcome normal
theorem loop0_body (p : Position) (m : Mem) (mb tb : Nat) (s : State) (k : Nat)
    (hs : p.board.length = 81) (hk : k < 81)
    (hInv : Inv0T (posBlock := posBlock) p m mb tb k s) :
    ∃ s1 T, BodyResult (posBlock := posBlock) p m mb tb k s s1 T := by
  rcases hInv with ⟨MB, T, h0, h1, h2, h3, hmb, hlenmb, hArrMB, htb, hlentb, hTot, hpos, hmbtb, hmb0, htb0, hpm, hpt, hframe, hro⟩
  let b := pieceByte (p.pieceAt ⟨k, by omega⟩)
  have hb15 : b.toNat % 16 ≠ 15 := board_nibble p hs k hk
  have hcond : EvE Gen.prog s (.bin .lt (some ⟨32, true⟩) (.cast ⟨32, true⟩ (.var 3)) (.const (.int ⟨32, true⟩ 81)))
      (boolVal true) := by
    refine EvE.bin (va := i32 (k : Int)) (EvE.cast (v := i32 (k : Int)) (EvE.var h3) ?_) (EvE.const _) ?_
    · simp [u8, i32, IntTy.u8, IntTy.i32, evalCast, IntTy.wrap, IntTy.modulus, IntTy.toInt,
        Nat.mod_eq_of_lt (show k < 4294967296 by omega)]
      rw [Int.emod_eq_of_lt (by omega) (by omega)]; simp
    · simp [i32, IntTy.i32, evalBin, evalBinInt, binInt, intOf, isPtr, IntTy.toInt, IntTy.wrap,
        IntTy.modulus, boolVal, hk, Nat.mod_eq_of_lt (show k < 4294967296 by omega)]
      rw [Int.emod_eq_of_lt (by omega) (by omega)]; simp; omega
  obtain ⟨s4, s5, eA, e13, hl8, hmem5, hro5, hl5⟩ := board_helper_calls s p hs k hk hpos h0 h3
  let s7 : State := { s5 with locals := s5.locals.upd 7 (i32 (byteFam b)) }
  have h7 : s7.locals 7 = some (i32 (byteFam b)) := by simp [s7, Locals.upd]
  have e7 : ExS Gen.prog s5 (.set 7 (.var 8)) .normal s7 := ExS.set (EvE.var hl8)
  by_cases hneg : byteFam b < 0
  · -- skip
    have hbf : byteFam b = -1 := byteFam_neg b hneg
    have hcondge : EvE Gen.prog s7 (.bin .ge (some ⟨32, true⟩) (.var 7) (.const (.int ⟨32, true⟩ 0)))
        (boolVal false) := by
      refine EvE_of_eval (n := 10) ?_
      simp [evalExpr, evalBin, evalBinInt, binInt, intOf, isPtr, IntTy.toInt, IntTy.wrap,
        IntTy.modulus, boolVal, i32, IntTy.i32, h7, hbf]
    have eskip : ExS Gen.prog s7 (.ite (.bin .ge (some ⟨32, true⟩) (.var 7) (.const (.int ⟨32, true⟩ 0))) (.store (.int ⟨32, false⟩) (.index (.var 2) (.var 7) 4) (.cast ⟨32, false⟩ (.bin .add (some ⟨32, false⟩) (.cast ⟨32, false⟩ (.load (.int ⟨32, false⟩) (.index (.var 2) (.var 7) 4))) (.const (.int ⟨32, false⟩ 1))))) .skip) .normal s7 := ExS.ite hcondge rfl ExS.skip
    have hactions : ExS Gen.prog s
        (.seq (.seq (.call (some 5) 2 [(.load (.int ⟨8, false⟩) (.index (.field (.var 0) 0) (.var 3) 1))])
          (.seq (.call (some 6) 4 [(.var 5)]) (.set 4 (.var 6))))
          (.seq (.seq (.call (some 8) 13 [(.var 4)]) (.set 7 (.var 8)))
            (.ite (.bin .ge (some ⟨32, true⟩) (.var 7) (.const (.int ⟨32, true⟩ 0)))
              (.store (.int ⟨32, false⟩) (.index (.var 2) (.var 7) 4) (.cast ⟨32, false⟩
                (.bin .add (some ⟨32, false⟩) (.cast ⟨32, false⟩
                  (.load (.int ⟨32, false⟩) (.index (.var 2) (.var 7) 4))) (.const (.int ⟨32, false⟩ 1))))) .skip)))
        .normal s7 := ExS.seq eA (ExS.seq (ExS.seq e13 e7) eskip)
    refine ⟨s7, T, { exs := ExS.ite hcond rfl hactions, hmem_tb := ?_, hlenT := hlentb, hTot := ?_, hloc0 := ?_, hloc1 := ?_, hloc2 := ?_, hloc3 := ?_, hro := ?_, hmem_mb := ?_, hmem_pos := ?_, hframe := ?_ }⟩
    · rw [show s7.mem = s5.mem by rfl, hmem5]; exact htb
    · intro i
      rw [boardFamCount_succ]
      have hf := famOfByte_of_byteFam b hb15
      rw [hbf] at hf
      have hfam : famAt p k = 7 := by simpa [famAt, hk, b] using hf
      rw [hfam]
      simp [show 7 ≠ i.val by omega]
      exact hTot i
    · simpa [show s7.locals 0 = s5.locals 0 by simp [s7, Locals.upd],
        hl5 0 (by omega) (by omega) (by omega) (by omega)] using h0
    · simpa [show s7.locals 1 = s5.locals 1 by simp [s7, Locals.upd],
        hl5 1 (by omega) (by omega) (by omega) (by omega)] using h1
    · simpa [show s7.locals 2 = s5.locals 2 by simp [s7, Locals.upd],
        hl5 2 (by omega) (by omega) (by omega) (by omega)] using h2
    · simpa [show s7.locals 3 = s5.locals 3 by simp [s7, Locals.upd],
        hl5 3 (by omega) (by omega) (by omega) (by omega)] using h3
    · simpa [show s7.ro = s5.ro by rfl, hro5] using hro
    · simpa [show s7.mem mb = s5.mem mb by rfl, hmem5] using hmb
    · simpa [show s7.mem posBlock = s5.mem posBlock by rfl, hmem5] using hpos
    · exact fun b hb0 hmbx htb => by
        simpa [show s7.mem b = s5.mem b by rfl, hmem5] using hframe b hb0 hmbx htb
  · -- increment
    have hbf_nonneg : 0 ≤ byteFam b := by omega
    have hjlt : (byteFam b).toNat < 7 := by
      rcases byteFam_bound b with h | h
      · omega
      · exact h
    let j : Fin 7 := ⟨(byteFam b).toNat, hjlt⟩
    have hbfj : byteFam b = (j.val : Int) := by simp [j, Int.toNat_of_nonneg hbf_nonneg]
    have h2s7 : s7.locals 2 = some (.ptr tb 0) := by
      rw [show s7.locals 2 = s5.locals 2 by simp [s7, Locals.upd],
        hl5 2 (by omega) (by omega) (by omega) (by omega)]
      exact h2
    have h7j : s7.locals 7 = some (i32 (j.val : Int)) := by rw [h7, hbfj]
    have hs7tb : s7.mem tb = some T := by rw [show s7.mem = s5.mem by rfl, hmem5, htb]
    have hidx := slot_index (s := s7) j h2s7 h7j hs7tb hlentb
    have hold := hTot j
    have hload : EvE Gen.prog s7 (.load (.int ⟨32, false⟩) (.index (.var 2) (.var 7) 4))
        (.int ⟨32, false⟩ (boardFamCount p k j)) := slot_load j _ h2s7 h7j hs7tb hlentb hold
    have hbnd : boardFamCount p k j ≤ 81 := by
      unfold boardFamCount
      have := List.countP_le_length (p := fun s => famAt p s = j.val) (l := List.range k)
      simp at this; omega
    have hadd : EvE Gen.prog s7
        (.bin .add (some ⟨32, false⟩) (.cast ⟨32, false⟩
          (.load (.int ⟨32, false⟩) (.index (.var 2) (.var 7) 4))) (.const (.int ⟨32, false⟩ 1)))
        (.int ⟨32, false⟩ (boardFamCount p k j + 1)) := by
      refine EvE.bin (va := .int ⟨32, false⟩ (boardFamCount p k j))
        (EvE.cast hload (by simp [evalCast, IntTy.wrap, IntTy.modulus,
          Nat.mod_eq_of_lt (show boardFamCount p k j < 4294967296 by omega)])) (EvE.const _) ?_
      simp [evalBin, evalBinInt, binInt, intOf, isPtr, IntTy.toInt, IntTy.wrap, IntTy.modulus,
        arith, IntTy.inRange, IntTy.u32, Nat.mod_eq_of_lt (show boardFamCount p k j + 1 < 4294967296 by omega)]
    have hadd_cast : EvE Gen.prog s7 (.cast ⟨32, false⟩
        (.bin .add (some ⟨32, false⟩) (.cast ⟨32, false⟩
          (.load (.int ⟨32, false⟩) (.index (.var 2) (.var 7) 4))) (.const (.int ⟨32, false⟩ 1))))
        (.int ⟨32, false⟩ (boardFamCount p k j + 1)) := by
      apply EvE.cast hadd
      have hlt : boardFamCount p k j + 1 < 4294967296 := by omega
      simp [evalCast, IntTy.wrap, IntTy.modulus, Nat.mod_eq_of_lt hlt]
    have hstore : store s7.mem (Ty.int ⟨32, false⟩) (.ptr tb (4*j.val))
        (.int ⟨32, false⟩ (boardFamCount p k j + 1)) =
        .ok (s7.mem.upd tb (T.take (4*j.val) ++ encodeLE 4 (boardFamCount p k j + 1) ++ T.drop (4*j.val+4))) := by
      simp [store, writeBytes, hs7tb, Ty.size, IntTy.bytes, encodeLE_length,
        show 4*j.val + 4 ≤ T.length by omega]
    let T' := T.take (4*j.val) ++ encodeLE 4 (boardFamCount p k j + 1) ++ T.drop (4*j.val+4)
    let s8 : State := { s7 with mem := s7.mem.upd tb T' }
    have estore : ExS Gen.prog s7
        (.store (.int ⟨32, false⟩) (.index (.var 2) (.var 7) 4) (.cast ⟨32, false⟩
          (.bin .add (some ⟨32, false⟩) (.cast ⟨32, false⟩
            (.load (.int ⟨32, false⟩) (.index (.var 2) (.var 7) 4))) (.const (.int ⟨32, false⟩ 1)))))
        .normal s8 := ExS.store hidx hadd_cast (by simpa [show s7.ro = s5.ro by rfl, hro5] using hro) hstore
    have hcondge : EvE Gen.prog s7 (.bin .ge (some ⟨32, true⟩) (.var 7) (.const (.int ⟨32, true⟩ 0)))
        (boolVal true) := by
      refine EvE_of_eval (n := 10) ?_
      simp [evalExpr, evalBin, evalBinInt, binInt, intOf, isPtr, IntTy.toInt, IntTy.wrap,
        IntTy.modulus, boolVal, i32, IntTy.i32, h7j, hbf_nonneg]
      omega
    have estore_branch : ExS Gen.prog s7 (.ite (.bin .ge (some ⟨32, true⟩) (.var 7) (.const (.int ⟨32, true⟩ 0)))
        (.store (.int ⟨32, false⟩) (.index (.var 2) (.var 7) 4) (.cast ⟨32, false⟩
          (.bin .add (some ⟨32, false⟩) (.cast ⟨32, false⟩
            (.load (.int ⟨32, false⟩) (.index (.var 2) (.var 7) 4))) (.const (.int ⟨32, false⟩ 1))))) .skip)
        .normal s8 := ExS.ite hcondge rfl estore
    have hactions : ExS Gen.prog s
        (.seq (.seq (.call (some 5) 2 [(.load (.int ⟨8, false⟩) (.index (.field (.var 0) 0) (.var 3) 1))])
          (.seq (.call (some 6) 4 [(.var 5)]) (.set 4 (.var 6))))
          (.seq (.seq (.call (some 8) 13 [(.var 4)]) (.set 7 (.var 8)))
            (.ite (.bin .ge (some ⟨32, true⟩) (.var 7) (.const (.int ⟨32, true⟩ 0)))
              (.store (.int ⟨32, false⟩) (.index (.var 2) (.var 7) 4) (.cast ⟨32, false⟩
                (.bin .add (some ⟨32, false⟩) (.cast ⟨32, false⟩
                  (.load (.int ⟨32, false⟩) (.index (.var 2) (.var 7) 4))) (.const (.int ⟨32, false⟩ 1))))) .skip)))
        .normal s8 := ExS.seq eA (ExS.seq (ExS.seq e13 e7) estore_branch)
    refine ⟨s8, T', { exs := ExS.ite hcond rfl hactions, hmem_tb := ?_, hlenT := ?_, hTot := ?_, hloc0 := ?_, hloc1 := ?_, hloc2 := ?_, hloc3 := ?_, hro := ?_, hmem_mb := ?_, hmem_pos := ?_, hframe := ?_ }⟩
    · simp [s8, Mem.upd_eq]
    · simp [T', hlentb, Nat.min_eq_left (show 4*j.val ≤ 28 by omega), encodeLE_length]; omega
    · intro i
      rw [boardFamCount_succ]
      have hfam : famAt p k = j.val := by
        have hf := famOfByte_of_byteFam b hb15
        simpa [famAt, hk, b, j, Int.toNat_of_nonneg hbf_nonneg, hbf_nonneg, show ¬ byteFam b < 0 by omega] using hf
      rw [hfam]
      by_cases hij : i = j
      · have hijv : j.val = i.val := by rw [hij]
        rw [if_pos hijv]
        subst hij
        have hnew : decodeLE ((T'.drop (4*j.val)).take 4) = boardFamCount p k j + 1 := by
          unfold T'
          simp [T', hlentb, Nat.min_eq_left (show 4*j.val ≤ 28 by omega), encodeLE_length,
            encodeLE, decodeLE, Nat.mod_eq_of_lt (show boardFamCount p k j + 1 < 4294967296 by omega)]
          omega
        exact hnew
      · have hijv : (j : Nat) ≠ i.val := by
          intro h; apply hij; apply Fin.ext; exact h.symm
        rw [if_neg hijv]
        simpa [T', hTot i] using array_write_other T hlentb i j hij (boardFamCount p k j + 1)
    · simpa [show s8.locals 0 = s7.locals 0 by simp [s8],
        show s7.locals 0 = s5.locals 0 by simp [s7, Locals.upd],
        hl5 0 (by omega) (by omega) (by omega) (by omega)] using h0
    · simpa [show s8.locals 1 = s7.locals 1 by simp [s8],
        show s7.locals 1 = s5.locals 1 by simp [s7, Locals.upd],
        hl5 1 (by omega) (by omega) (by omega) (by omega)] using h1
    · simpa [show s8.locals 2 = s7.locals 2 by simp [s8],
        show s7.locals 2 = s5.locals 2 by simp [s7, Locals.upd],
        hl5 2 (by omega) (by omega) (by omega) (by omega)] using h2
    · simpa [show s8.locals 3 = s7.locals 3 by simp [s8],
        show s7.locals 3 = s5.locals 3 by simp [s7, Locals.upd],
        hl5 3 (by omega) (by omega) (by omega) (by omega)] using h3
    · simpa [show s8.ro = s7.ro by simp [s8], show s7.ro = s5.ro by rfl, hro5] using hro
    · simpa [show s8.mem mb = s7.mem mb by simp [s8, Mem.upd_ne hmbtb],
        show s7.mem mb = s5.mem mb by rfl, hmem5] using hmb
    · simpa [show s8.mem posBlock = s7.mem posBlock by simp [s8, Mem.upd_ne hpt],
        show s7.mem posBlock = s5.mem posBlock by rfl, hmem5] using hpos
    · exact fun b hb0 hmbx htb => by
        simpa [show s8.mem b = s7.mem b by simp [s8, Mem.upd_ne htb],
          show s7.mem b = s5.mem b by rfl, hmem5] using hframe b hb0 hmbx htb

theorem loop0_runs (p : Position) (m : Mem) (mb tb : Nat) (s0 : State)
    (hs : p.board.length = 81) (hInv0 : Inv0T (posBlock := posBlock) p m mb tb 0 s0) :
    ∃ s', ExS Gen.prog s0 Gen.validate_material_loop0 .normal s' ∧
      Inv0T (posBlock := posBlock) p m mb tb 81 s' := by
  let P : Nat → Prop := fun d => d ≤ 81 → ∀ (s : State),
    Inv0T (posBlock := posBlock) p m mb tb (81 - d) s →
      ∃ s', ExS Gen.prog s Gen.validate_material_loop0 .normal s' ∧
        Inv0T (posBlock := posBlock) p m mb tb 81 s'
  have hP : ∀ d, P d := by
    intro d
    induction d with
    | zero =>
        intro hd s hInv
        refine ⟨s, ?_, ?_⟩
        · unfold Gen.validate_material_loop0
          apply ExS.loop_brk
          obtain ⟨MB, T, h0, h1, h2, h3, hmb, hlenmb, hArrMB, htb, hlentb, hTot, hpos,
            hmbtb, hmb0, htb0, hpm, hpt, hframe, hro⟩ := hInv
          have hcond : EvE Gen.prog s (.bin .lt (some ⟨32, true⟩) (.cast ⟨32, true⟩ (.var 3)) (.const (.int ⟨32, true⟩ 81)))
              (boolVal false) := by
            refine EvE.bin (va := i32 81) (EvE.cast (v := i32 81) (EvE.var h3) ?_) (EvE.const _) ?_
            · simp [u8, i32, IntTy.u8, IntTy.i32, evalCast, IntTy.wrap, IntTy.modulus, IntTy.toInt]
            · simp [i32, IntTy.i32, evalBin, evalBinInt, binInt, intOf, isPtr, IntTy.toInt, IntTy.wrap,
                IntTy.modulus, boolVal]
          exact ExS.ite (bc := false) hcond rfl ExS.brk
        · exact hInv
    | succ d ih =>
        intro hd s hInv
        have hInv_copy := hInv
        obtain ⟨MB0, T0, h0, h1, h2, h3, hmb, hlenmb, hArrMB, htb, hlentb, hTot, hpos,
          hmbtb, hmb0, htb0, hpm, hpt, hframe, hro⟩ := hInv
        let k := 81 - (d + 1)
        have hk : k < 81 := by change 81 - (d + 1) < 81; exact Nat.sub_lt (by decide) (Nat.succ_pos d)
        have hd_le : d ≤ 81 := by omega
        have hk_eq : k + 1 = 81 - d := by dsimp [k]; omega
        obtain ⟨s1, T1, hres⟩ := loop0_body p m mb tb s k hs hk hInv_copy
        let s2 : State := { s1 with locals := s1.locals.upd 3 (u8 (k+1)) }
        have hstep : ExS Gen.prog s1 (.set 3 (.cast ⟨8, false⟩
            (.bin .add (some ⟨32, true⟩) (.cast ⟨32, true⟩ (.var 3)) (.const (.int ⟨32, true⟩ 1))))) .normal s2 := by
          have h3s1 : s1.locals 3 = some (.int IntTy.u8 k) := by rw [hres.hloc3]; exact h3
          have hev : evalExpr Gen.prog 5 s1 (.cast ⟨8, false⟩
              (.bin .add (some ⟨32, true⟩) (.cast ⟨32, true⟩ (.var 3)) (.const (.int ⟨32, true⟩ 1))))
              = .ok (u8 (k+1)) := ev_succ (v := 3) s1 k hk h3s1
          exact ExS.set (EvE_of_eval hev)
        have hInv2 : Inv0T (posBlock := posBlock) p m mb tb (k+1) s2 := by
          refine ⟨MB0, T1, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
          · rw [show s2.locals 0 = s1.locals 0 by simp [s2, Locals.upd], hres.hloc0]; exact h0
          · rw [show s2.locals 1 = s1.locals 1 by simp [s2, Locals.upd], hres.hloc1]; exact h1
          · rw [show s2.locals 2 = s1.locals 2 by simp [s2, Locals.upd], hres.hloc2]; exact h2
          · simp [s2, Locals.upd]
          · rw [show s2.mem mb = s1.mem mb by simp [s2], hres.hmem_mb]; exact hmb
          · exact hlenmb
          · exact hArrMB
          · rw [show s2.mem tb = s1.mem tb by simp [s2]]; exact hres.hmem_tb
          · exact hres.hlenT
          · exact hres.hTot
          · rw [show s2.mem posBlock = s1.mem posBlock by simp [s2], hres.hmem_pos]; exact hpos
          · exact hmbtb
          · exact hmb0
          · exact htb0
          · exact hpm
          · exact hpt
          · intro b hb0 hmbx htb
            rw [show s2.mem b = s1.mem b by simp [s2], hres.hframe b hb0 hmbx htb]
            exact hframe b hb0 hmbx htb
          · rw [show s2.ro = s1.ro by simp [s2], hres.hro]; exact hro
        obtain ⟨sf, hloopf, hInvf⟩ := ih hd_le s2 (by simpa [hk_eq] using hInv2)
        refine ⟨sf, ?_, hInvf⟩
        unfold Gen.validate_material_loop0
        exact ExS.loop_next hres.exs (Or.inl rfl) hstep hloopf
  exact hP 81 (by omega) s0 (by simpa using hInv0)


-- hand byte at slot i of colour c in the encoded position
theorem hand_byte_val (p : Position) (hs : p.Shaped) (c : Color) (i : Fin 7) :
    (encode p).getD (81 + 7 * c.idx + i.val) 0 = (p.hand c i).toUInt8 := by
  rw [encode_enc]
  exact enc_getD_hand (pa := p.pieceAt) (h := p.hand) (sd := p.side)
    (kb := kingByte p .black) (kw := kingByte p .white) c i

-- full hand-byte load via the address lemma
theorem ev_hand_byte0 (p : Position) (s : State) (i : Fin 7)
    (hm : s.mem posBlock = some (encode p))
    (h0 : s.locals 0 = some (posPtr' posBlock))
    (h9 : s.locals 9 = some (u32 i.val)) :
    EvE Gen.prog s (.load (.int ⟨8, false⟩)
      (.index (.index (.field (.var 0) 81) (.const (.int ⟨32, true⟩ 0)) 7) (.var 9) 1))
      (.int IntTy.u8 ((encode p).getD (81 + i.val) 0).toNat) := by
  -- first the address (copy the proven proof)
  have haddr : evalExpr Gen.prog 10 s (.index (.index (.field (.var 0) 81) (.const (.int ⟨32, true⟩ 0)) 7) (.var 9) 1)
      = .ok (.ptr posBlock (81 + i.val)) := by
    have hlen : (encode p).length = 114 := encode_length p
    simp [evalExpr, evalCast, evalUn, intOf, IntTy.toInt, IntTy.wrap, IntTy.modulus,
      ptrAdd, ptrAddN, u32, i32, posPtr', h0, h9, hm, hlen, IntTy.i32, IntTy.u32,
      wrap_nat32 i.val (by omega), show ¬ (2147483648 : Int) ≤ i.val by omega]
    omega
  refine EvE.load (EvE_of_eval haddr) ?_
  simp only [load, readBytes, hm, Ty.size, IntTy.bytes]
  have hlen : (encode p).length = 114 := encode_length p
  simp [show 81 + i.val + 1 ≤ (encode p).length by omega,
    List.take_one, List.head?_drop, List.getD, decodeLE]
  cases he : (encode p)[81 + i.val]? <;> simp [he, decodeLE, IntTy.u8]

theorem ev_hand_byte1 (p : Position) (s : State) (i : Fin 7)
    (hm : s.mem posBlock = some (encode p))
    (h0 : s.locals 0 = some (posPtr' posBlock))
    (h9 : s.locals 9 = some (u32 i.val)) :
    EvE Gen.prog s (.load (.int ⟨8, false⟩)
      (.index (.index (.field (.var 0) 81) (.const (.int ⟨32, true⟩ 1)) 7) (.var 9) 1))
      (.int IntTy.u8 ((encode p).getD (81 + 7 + i.val) 0).toNat) := by
  have haddr : evalExpr Gen.prog 10 s (.index (.index (.field (.var 0) 81) (.const (.int ⟨32, true⟩ 1)) 7) (.var 9) 1)
      = .ok (.ptr posBlock (81 + 7 + i.val)) := by
    have hlen : (encode p).length = 114 := encode_length p
    simp [evalExpr, evalCast, evalUn, intOf, IntTy.toInt, IntTy.wrap, IntTy.modulus,
      ptrAdd, ptrAddN, u32, i32, posPtr', h0, h9, hm, hlen, IntTy.i32, IntTy.u32,
      wrap_nat32 i.val (by omega), show ¬ (2147483648 : Int) ≤ i.val by omega]
    omega
  refine EvE.load (EvE_of_eval haddr) ?_
  simp only [load, readBytes, hm, Ty.size, IntTy.bytes]
  have hlen : (encode p).length = 114 := encode_length p
  simp [show 81 + 7 + i.val + 1 ≤ (encode p).length by omega,
    List.take_one, List.head?_drop, List.getD, decodeLE]
  cases he : (encode p)[81 + 7 + i.val]? <;> simp [he, decodeLE, IntTy.u8]

-- u32-indexed array address: ptr b (4*i)
theorem slot_index_u {s : State} {b : Nat} {T : Block} (i : Fin 7)
    (hbase : s.locals 2 = some (.ptr b 0)) (hidx : s.locals 9 = some (u32 i.val))
    (hb : s.mem b = some T) (hlen : T.length = 28) :
    EvE Gen.prog s (.index (.var 2) (.var 9) 4) (.ptr b (4 * i.val)) := by
  have haddr : evalExpr Gen.prog 10 s (.index (.var 2) (.var 9) 4) = .ok (.ptr b (4 * i.val)) := by
    simp [evalExpr, evalCast, evalUn, intOf, IntTy.toInt, IntTy.wrap, IntTy.modulus,
      ptrAdd, ptrAddN, u32, i32, hbase, hidx, hb, hlen, IntTy.i32, IntTy.u32,
      show 4 * i.val ≤ T.length by omega]
    rw [if_pos (show i.val * 4 ≤ 28 by omega)]
    congr 2 <;> omega
  exact EvE_of_eval haddr

-- u32-indexed array load
theorem slot_load_u {s : State} {b : Nat} {T : Block} (i : Fin 7) (val : Nat)
    (hbase : s.locals 2 = some (.ptr b 0)) (hidx : s.locals 9 = some (u32 i.val))
    (hb : s.mem b = some T) (hlen : T.length = 28)
    (hval : decodeLE ((T.drop (4*i.val)).take 4) = val) :
    EvE Gen.prog s (.load (.int ⟨32, false⟩) (.index (.var 2) (.var 9) 4))
      (.int ⟨32, false⟩ val) := by
  refine EvE.load (slot_index_u i hbase hidx hb hlen) ?_
  simp only [load, readBytes, hb, Ty.size, IntTy.bytes]
  simp [show 4 * i.val + 4 ≤ T.length by omega, hval]

-- helpers
theorem slot_index_u_at {s : State} {b : Nat} {T : Block} (base : Nat) (i : Fin 7)
    (hbase : s.locals base = some (.ptr b 0)) (hidx : s.locals 9 = some (u32 i.val))
    (hb : s.mem b = some T) (hlen : T.length = 28) :
    EvE Gen.prog s (.index (.var base) (.var 9) 4) (.ptr b (4 * i.val)) := by
  have haddr : evalExpr Gen.prog 10 s (.index (.var base) (.var 9) 4) = .ok (.ptr b (4 * i.val)) := by
    simp [evalExpr, evalCast, evalUn, intOf, IntTy.toInt, IntTy.wrap, IntTy.modulus,
      ptrAdd, ptrAddN, u32, i32, hbase, hidx, hb, hlen, IntTy.i32, IntTy.u32,
      show 4 * i.val ≤ T.length by omega]
    rw [if_pos (show i.val * 4 ≤ 28 by omega)]
    congr 2 <;> omega
  exact EvE_of_eval haddr
theorem slot_load_u_at {s : State} {b : Nat} {T : Block} (base : Nat) (i : Fin 7) (val : Nat)
    (hbase : s.locals base = some (.ptr b 0)) (hidx : s.locals 9 = some (u32 i.val))
    (hb : s.mem b = some T) (hlen : T.length = 28)
    (hval : decodeLE ((T.drop (4*i.val)).take 4) = val) :
    EvE Gen.prog s (.load (.int ⟨32, false⟩) (.index (.var base) (.var 9) 4))
      (.int ⟨32, false⟩ val) := by
  refine EvE.load (slot_index_u_at base i hbase hidx hb hlen) ?_
  simp only [load, readBytes, hb, Ty.size, IntTy.bytes]
  simp [show 4 * i.val + 4 ≤ T.length by omega, hval]
theorem ev_hand_count (p : Position) (hs : p.Shaped) (s : State) (c : Color) (i : Fin 7) (hsmall : p.hand c i < 256)
    (hm : s.mem posBlock = some (encode p)) (h0 : s.locals 0 = some (posPtr' posBlock))
    (h9 : s.locals 9 = some (u32 i.val)) :
    EvE Gen.prog s (.load (.int ⟨8, false⟩)
      (.index (.index (.field (.var 0) 81) (.const (.int ⟨32, true⟩ c.idx)) 7) (.var 9) 1))
      (.int IntTy.u8 (p.hand c i)) := by
  have hraw : EvE Gen.prog s (.load (.int ⟨8, false⟩)
      (.index (.index (.field (.var 0) 81) (.const (.int ⟨32, true⟩ c.idx)) 7) (.var 9) 1))
      (.int IntTy.u8 ((encode p).getD (81 + 7*c.idx + i.val) 0).toNat) := by
    cases c with
    | black => simpa [Color.idx] using ev_hand_byte0 p s i hm h0 h9
    | white => simpa [Color.idx] using ev_hand_byte1 p s i hm h0 h9
  have hval : (encode p).getD (81 + 7*c.idx + i.val) 0 = (p.hand c i).toUInt8 := hand_byte_val p hs c i
  obtain ⟨K, hK⟩ := hraw
  refine ⟨K, ?_⟩
  intro n hn
  rw [hK n hn]
  exact congrArg (fun v => Res.ok (Val.int IntTy.u8 v)) (by rw [hval]; simp [Nat.mod_eq_of_lt hsmall])

theorem evalCast_u32_of_u32 (n : Nat) (hn : n < 2^31) :
    evalCast ⟨32, false⟩ (.int ⟨32, false⟩ n) = .ok (.int ⟨32, false⟩ n) := by
  simp [evalCast, IntTy.modulus] <;> omega

theorem evalCast_i32_of_u8 (n : Nat) (hn : n < 256) :
    evalCast ⟨32, true⟩ (.int ⟨8, false⟩ n) = .ok (.int ⟨32, true⟩ n) := by
  simp [evalCast, IntTy.modulus, IntTy.u8, IntTy.i32] <;> omega

theorem evalCast_u32_of_i32 (n : Nat) (hn : n < 2^30) :
    evalCast ⟨32, false⟩ (.int ⟨32, true⟩ n) = .ok (.int ⟨32, false⟩ n) := by
  simp [evalCast, IntTy.wrap, IntTy.modulus, IntTy.toInt, IntTy.i32, IntTy.u32,
    IntTy.minVal, IntTy.maxVal] <;> omega

theorem evalBin_add_i32_nat (a b : Nat) (ha : a < 2^30) (hb : b < 2^30) :
    evalBin .add (some ⟨32, true⟩) (.int ⟨32, true⟩ a) (.int ⟨32, true⟩ b) =
      .ok (.int ⟨32, true⟩ (a+b)) := by
  simp [evalBin, evalBinInt, binInt, intOf, isPtr, IntTy.toInt, IntTy.wrap, IntTy.modulus,
    IntTy.i32, arith, IntTy.inRange, IntTy.minVal, IntTy.maxVal,
    show ¬ (2147483648 : Nat) ≤ a by omega, show ¬ (2147483648 : Nat) ≤ b by omega,
    show -2147483648 ≤ (a : Int) + b ∧ (a : Int) + b ≤ 2147483647 by omega]
  have hs : (a : Int) + b = (a + b : Nat) := by omega
  rw [hs]
  rw [Int.emod_eq_of_lt (by omega) (by omega)]
  omega

theorem evalBin_add_u32_nat (a b : Nat) (ha : a < 2^30) (hb : b < 2^30) :
    evalBin .add (some ⟨32, false⟩) (.int ⟨32, false⟩ a) (.int ⟨32, false⟩ b) =
      .ok (.int ⟨32, false⟩ (a+b)) := by
  simp [evalBin, evalBinInt, binInt, intOf, isPtr, IntTy.toInt, IntTy.wrap, IntTy.modulus,
    IntTy.u32, arith, IntTy.inRange, IntTy.minVal, IntTy.maxVal,
    show ¬ (2147483648 : Nat) ≤ a by omega, show ¬ (2147483648 : Nat) ≤ b by omega,
    show -2147483648 ≤ (a : Int) + b ∧ (a : Int) + b ≤ 2147483647 by omega]
  omega

theorem evalBin_gt_u32_le (a b : Nat) (ha : a < 2^30) (hb : b < 2^30) (hle : a ≤ b) :
    evalBin .gt (some ⟨32, false⟩) (.int ⟨32, false⟩ a) (.int ⟨32, false⟩ b) =
      .ok (boolVal false) := by
  simp [evalBin, evalBinInt, binInt, intOf, isPtr, IntTy.toInt, IntTy.wrap, IntTy.modulus,
    IntTy.u32, arith, IntTy.inRange, IntTy.minVal, IntTy.maxVal, boolVal] <;> omega


def Loop1Inv (p : Position) (m : Mem) (mb tb : Nat) (j : Nat) (s : State) : Prop :=
  ∃ MB T,
    s.locals 0 = some (posPtr' posBlock) ∧ s.locals 1 = some (.ptr mb 0) ∧
    s.locals 2 = some (.ptr tb 0) ∧
    s.mem mb = some MB ∧ MB.length = 28 ∧ ArrEq MB maxArr ∧
    s.mem tb = some T ∧ T.length = 28 ∧
    (∀ i : Fin 7, decodeLE ((T.drop (4*i.val)).take 4) =
        if i.val < j then p.familyCount i else boardFamCount p 81 i) ∧
    s.mem posBlock = some (encode p) ∧
    mb ≠ tb ∧ mb ≠ 0 ∧ tb ≠ 0 ∧ posBlock ≠ mb ∧ posBlock ≠ tb ∧
    (∀ b, b ≠ 0 → b ≠ mb → b ≠ tb → s.mem b = m b) ∧ s.ro = false

-- named sub-expressions of the loop-1 body
def l1Cond (j : Nat) : Expr :=
  .bin .lt (some ⟨32, false⟩) (.var 9) (.cast ⟨32, false⟩ (.const (.int ⟨32, true⟩ 7)))
def l1Val : Expr :=
  .cast ⟨32, false⟩
    (.bin .add (some ⟨32, false⟩)
      (.cast ⟨32, false⟩ (.load (.int ⟨32, false⟩) (.index (.var 2) (.var 9) 4)))
      (.cast ⟨32, false⟩ (.cast ⟨32, false⟩
        (.bin .add (some ⟨32, true⟩)
          (.cast ⟨32, true⟩ (.load (.int ⟨8, false⟩) (.index (.index (.field (.var 0) 81) (.const (.int ⟨32, true⟩ 0)) 7) (.var 9) 1)))
          (.cast ⟨32, true⟩ (.load (.int ⟨8, false⟩) (.index (.index (.field (.var 0) 81) (.const (.int ⟨32, true⟩ 1)) 7) (.var 9) 1)))))))
def l1OverCond : Expr :=
  .bin .gt (some ⟨32, false⟩)
    (.load (.int ⟨32, false⟩) (.index (.var 2) (.var 9) 4))
    (.load (.int ⟨32, false⟩) (.index (.var 1) (.var 9) 4))
def l1Store : Stmt := .store (.int ⟨32, false⟩) (.index (.var 2) (.var 9) 4) l1Val
def l1Ret : Stmt := .ret (some (.cast ⟨8, false⟩ (.bin .ne (some ⟨32, true⟩)
  (.const (.int ⟨32, true⟩ 0)) (.const (.int ⟨32, true⟩ 0)))))
def loop1BodyStmt : Stmt := .ite (l1Cond 0) (.seq l1Store (.ite l1OverCond l1Ret .skip)) .brk

theorem loop1_body (p : Position) (hs : p.Shaped) (hmat : p.materialOk = true)
    (m : Mem) (mb tb : Nat) (s : State) (j : Nat) (hj : j < 7)
    (h9 : s.locals 9 = some (u32 j))
    (hInv : Loop1Inv (posBlock := posBlock) p m mb tb j s) :
    ∃ s1, ExS Gen.prog s (loop1BodyStmt) .normal s1 ∧
      Loop1Inv (posBlock := posBlock) p m mb tb (j+1) s1 ∧
      s1.locals 9 = s.locals 9 := by
  rcases hInv with ⟨MB, T, h0, h1, h2, hmb, hlenmb, hArrMB, htb, hlentb, hTot, hpos,
    hmbtb, hmb0, htb0, hpm, hpt, hframe, hro⟩
  let jf : Fin 7 := ⟨j, hj⟩
  have hall : ∀ i, i ∈ List.finRange 7 → p.familyCount i ≤ PieceType.handMax i := by
    simpa [Shogi.Position.materialOk, List.all_eq_true] using hmat
  have hhand_le (c : Color) (i : Fin 7) : p.hand c i ≤ 18 := Shogi.Sfen.hand_le_18 hmat c i
  have hsmallB : p.hand .black jf < 256 := by have h := hhand_le .black jf; omega
  have hsmallW : p.hand .white jf < 256 := by have h := hhand_le .white jf; omega
  have hfits : p.familyCount jf ≤ maxArr jf := by
    simpa [maxArr] using hall jf (List.mem_finRange jf)
  let t := boardFamCount p 81 jf
  let b := p.hand .black jf
  let w := p.hand .white jf
  let f := p.familyCount jf
  have ht_le : t ≤ 81 := by
    unfold t boardFamCount
    have hc := List.countP_le_length (p := fun s => famAt p s = jf.val) (l := List.range 81)
    simp at hc; omega
  have hb_le : b ≤ 18 := by simpa [b] using hhand_le .black jf
  have hw_le : w ≤ 18 := by simpa [w] using hhand_le .white jf
  have hf_le : f ≤ 18 := by
    have hm : maxArr jf ≤ 18 := (by decide : ∀ i : Fin 7, PieceType.handMax i ≤ 18) jf
    simpa [f, maxArr] using (Nat.le_trans hfits hm)
  have htbf : t + b + w = f := by
    simpa [t, b, w, f] using boardFamCount_81 p hs.1 jf
  -- condition
  have hcond : EvE Gen.prog s (l1Cond j) (boolVal true) := by
    refine EvE_of_eval (n := 10) ?_
    simp [l1Cond, evalExpr, evalCast, evalUn, intOf, isPtr, IntTy.toInt, IntTy.wrap, IntTy.modulus,
      evalBin, evalBinInt, binInt, u32, i32, h9, IntTy.u32, IntTy.i32, boolVal] <;> omega
  -- loads
  have hTotJ : decodeLE ((T.drop (4*jf.val)).take 4) = t := by simpa [jf, t] using hTot jf
  have hloadT : EvE Gen.prog s (.load (.int ⟨32, false⟩) (.index (.var 2) (.var 9) 4))
      (.int ⟨32, false⟩ t) := slot_load_u jf t h2 h9 htb hlentb hTotJ
  have hloadB : EvE Gen.prog s (.load (.int ⟨8, false⟩)
      (.index (.index (.field (.var 0) 81) (.const (.int ⟨32, true⟩ 0)) 7) (.var 9) 1))
      (.int IntTy.u8 b) := by simpa [b, Color.idx] using ev_hand_count p hs s .black jf hsmallB hpos h0 h9
  have hloadW : EvE Gen.prog s (.load (.int ⟨8, false⟩)
      (.index (.index (.field (.var 0) 81) (.const (.int ⟨32, true⟩ 1)) 7) (.var 9) 1))
      (.int IntTy.u8 w) := by simpa [w, Color.idx] using ev_hand_count p hs s .white jf hsmallW hpos h0 h9
  -- casts/adds (sub-expressions named via let)
  let eT := (.cast ⟨32, false⟩ (.load (.int ⟨32, false⟩) (.index (.var 2) (.var 9) 4)) : Expr)
  let eB := (.cast ⟨32, true⟩ (.load (.int ⟨8, false⟩)
      (.index (.index (.field (.var 0) 81) (.const (.int ⟨32, true⟩ 0)) 7) (.var 9) 1)) : Expr)
  let eW := (.cast ⟨32, true⟩ (.load (.int ⟨8, false⟩)
      (.index (.index (.field (.var 0) 81) (.const (.int ⟨32, true⟩ 1)) 7) (.var 9) 1)) : Expr)
  have hcastT : EvE Gen.prog s eT (.int ⟨32, false⟩ t) := by
    dsimp [eT]; exact EvE.cast hloadT (evalCast_u32_of_u32 t (by omega))
  have hcastB : EvE Gen.prog s eB (.int ⟨32, true⟩ b) := by
    dsimp [eB]; exact EvE.cast hloadB (evalCast_i32_of_u8 b (by omega))
  have hcastW : EvE Gen.prog s eW (.int ⟨32, true⟩ w) := by
    dsimp [eW]; exact EvE.cast hloadW (evalCast_i32_of_u8 w (by omega))
  let eAddI := (.bin .add (some ⟨32, true⟩) eB eW : Expr)
  have haddI : EvE Gen.prog s eAddI (.int ⟨32, true⟩ (b+w)) := by
    dsimp [eAddI]; exact EvE.bin hcastB hcastW (evalBin_add_i32_nat b w (by omega) (by omega))
  let eC1 := (.cast ⟨32, false⟩ eAddI : Expr)
  have hcastI1 : EvE Gen.prog s eC1 (.int ⟨32, false⟩ (b+w)) := by
    dsimp [eC1]; exact EvE.cast haddI (evalCast_u32_of_i32 (b+w) (by omega))
  let eC2 := (.cast ⟨32, false⟩ eC1 : Expr)
  have hcastI2 : EvE Gen.prog s eC2 (.int ⟨32, false⟩ (b+w)) := by
    dsimp [eC2]; exact EvE.cast hcastI1 (evalCast_u32_of_u32 (b+w) (by omega))
  let eAddU := (.bin .add (some ⟨32, false⟩) eT eC2 : Expr)
  have haddU : EvE Gen.prog s eAddU (.int ⟨32, false⟩ (t+(b+w))) := by
    dsimp [eAddU]; exact EvE.bin hcastT hcastI2 (evalBin_add_u32_nat t (b+w) (by omega) (by omega))
  have hvalue : EvE Gen.prog s l1Val (.int ⟨32, false⟩ f) := by
    have hc : EvE Gen.prog s (.cast ⟨32, false⟩ eAddU) (.int ⟨32, false⟩ (t+(b+w))) := by
      exact EvE.cast haddU (evalCast_u32_of_u32 (t+(b+w)) (by omega))
    have hval : t + (b+w) = f := by omega
    simpa [hval, l1Val, eAddU, eC2, eC1, eAddI, eT, eB, eW] using hc
  -- store
  have hidx := slot_index_u jf h2 h9 htb hlentb
  have hstore_eq : store s.mem (Ty.int ⟨32, false⟩) (.ptr tb (4*jf.val)) (.int ⟨32, false⟩ f) =
      .ok (s.mem.upd tb (T.take (4*jf.val) ++ encodeLE 4 f ++ T.drop (4*jf.val+4))) := by
    simp [store, writeBytes, htb, Ty.size, IntTy.bytes, encodeLE_length,
      show 4*jf.val + 4 ≤ T.length by omega]
  let T' := T.take (4*jf.val) ++ encodeLE 4 f ++ T.drop (4*jf.val+4)
  let s1 : State := { s with mem := s.mem.upd tb T' }
  have estore : ExS Gen.prog s l1Store .normal s1 := by
    dsimp [l1Store]; exact ExS.store hidx hvalue hro hstore_eq
  -- overflow check false
  have hlenT' : T'.length = 28 := by simp [T', hlentb, encodeLE_length]; omega
  have hTot1 : ∀ i : Fin 7, decodeLE ((T'.drop (4*i.val)).take 4) =
      if i.val < j+1 then p.familyCount i else boardFamCount p 81 i := by
    intro i
    by_cases hij : i = jf
    · subst hij; rw [if_pos (by simp [jf])]
      simp [T', hlentb, Nat.min_eq_left (show 4*jf.val ≤ 28 by omega), encodeLE_length,
        encodeLE, decodeLE] <;> omega
    · have hiv_ne : i.val ≠ j := by
        intro heq; apply hij; apply Fin.ext; simpa [jf] using heq
      by_cases hlt : i.val < j
      · rw [if_pos (by omega)]
        simpa [T', hTot i, hlt] using array_write_other T hlentb i jf hij f
      · rw [if_neg (by omega)]
        simpa [T', hTot i, hlt] using array_write_other T hlentb i jf hij f
  have hloadT1 : EvE Gen.prog s1 (.load (.int ⟨32, false⟩) (.index (.var 2) (.var 9) 4))
      (.int ⟨32, false⟩ f) := by
    have h2s1 : s1.locals 2 = some (.ptr tb 0) := by simp [s1, h2]
    have h9s1 : s1.locals 9 = some (u32 jf.val) := by simp [s1, h9, jf]
    have htbs1 : s1.mem tb = some T' := by simp [s1, Mem.upd_eq]
    have hv : decodeLE ((T'.drop (4*jf.val)).take 4) = f := by simpa [jf] using hTot1 jf
    exact slot_load_u jf f h2s1 h9s1 htbs1 hlenT' hv
  have hloadM : EvE Gen.prog s1 (.load (.int ⟨32, false⟩) (.index (.var 1) (.var 9) 4))
      (.int ⟨32, false⟩ (maxArr jf)) := by
    have h1s1 : s1.locals 1 = some (.ptr mb 0) := by simp [s1, h1]
    have h9s1 : s1.locals 9 = some (u32 jf.val) := by simp [s1, h9, jf]
    have hmbs1 : s1.mem mb = some MB := by simp [s1, T', Mem.upd_ne hmbtb, hmb]
    exact slot_load_u_at 1 jf (maxArr jf) h1s1 h9s1 hmbs1 hlenmb (hArrMB jf)
  have hcondgt : EvE Gen.prog s1 l1OverCond (boolVal false) := by
    dsimp [l1OverCond]
    exact EvE.bin hloadT1 hloadM (evalBin_gt_u32_le f (maxArr jf) (by omega) (by
      have hm : maxArr jf ≤ 18 := (by decide : ∀ i : Fin 7, PieceType.handMax i ≤ 18) jf
      omega) hfits)
  have eskip : ExS Gen.prog s1 (.ite l1OverCond l1Ret .skip) .normal s1 :=
    ExS.ite hcondgt rfl ExS.skip
  have hactions : ExS Gen.prog s (.seq l1Store (.ite l1OverCond l1Ret .skip)) .normal s1 :=
    ExS.seq estore eskip
  have hbody : ExS Gen.prog s (loop1BodyStmt) .normal s1 := by
    dsimp [loop1BodyStmt]; exact ExS.ite hcond rfl hactions
  refine ⟨s1, hbody, ?_⟩
  constructor
  · refine ⟨MB, T', ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simpa [s1, h0]
    · simpa [s1, h1]
    · simpa [s1, h2]
    · simpa [s1, T', Mem.upd_ne hmbtb, hmb]
    · exact hlenmb
    · exact hArrMB
    · simp [s1, Mem.upd_eq]
    · exact hlenT'
    · exact hTot1
    · simpa [s1, T', Mem.upd_ne hpt, hpos]
    · exact hmbtb
    · exact hmb0
    · exact htb0
    · exact hpm
    · exact hpt
    · intro bb hb0 hmbx htb_x
      simpa [s1, T', Mem.upd_ne htb_x] using hframe bb hb0 hmbx htb_x
    · simpa [s1] using hro
  · simp [s1]

def loop1StepStmt : Stmt :=
  .set 9 (.cast ⟨32, false⟩ (.bin .add (some ⟨32, false⟩)
    (.cast ⟨32, false⟩ (.var 9)) (.const (.int ⟨32, false⟩ 1))))

theorem loop1_runs (p : Position) (hs : p.Shaped) (hmat : p.materialOk = true)
    (m : Mem) (mb tb : Nat) (s0 : State) (h9zero : s0.locals 9 = some (u32 0))
    (hInv0 : Loop1Inv (posBlock := posBlock) p m mb tb 0 s0) :
    ∃ s', ExS Gen.prog s0 Gen.validate_material_loop1 .normal s' ∧
      Loop1Inv (posBlock := posBlock) p m mb tb 7 s' ∧ s'.locals 9 = some (u32 7) := by
  let P : Nat → Prop := fun d => d ≤ 7 → ∀ (s : State),
    s.locals 9 = some (u32 (7 - d)) →
    Loop1Inv (posBlock := posBlock) p m mb tb (7 - d) s →
      ∃ s', ExS Gen.prog s Gen.validate_material_loop1 .normal s' ∧
        Loop1Inv (posBlock := posBlock) p m mb tb 7 s' ∧ s'.locals 9 = some (u32 7)
  have hP : ∀ d, P d := by
    intro d
    induction d with
    | zero =>
        intro hd s h9 hInv
        refine ⟨s, ?_, ?_, h9⟩
        · unfold Gen.validate_material_loop1
          apply ExS.loop_brk
          have hcond : EvE Gen.prog s (l1Cond 7) (boolVal false) := by
            refine EvE_of_eval (n := 10) ?_
            simp [l1Cond, evalExpr, evalCast, intOf, isPtr, IntTy.toInt, IntTy.wrap, IntTy.modulus,
              evalBin, evalBinInt, binInt, u32, i32, h9, IntTy.u32, IntTy.i32, boolVal]
          exact ExS.ite hcond rfl ExS.brk
        · simpa using hInv
    | succ d ih =>
        intro hd s h9 hInv
        have hInv_copy := hInv
        let j := 7 - (d + 1)
        have hj : j < 7 := by dsimp [j]; omega
        have hd_le : d ≤ 7 := by omega
        have hjeq : j + 1 = 7 - d := by dsimp [j]; omega
        obtain ⟨s1, hbody, hInv1, hl9⟩ := loop1_body p hs hmat m mb tb s j hj h9 hInv_copy
        let s2 : State := { s1 with locals := s1.locals.upd 9 (u32 (j+1)) }
        have hstep : ExS Gen.prog s1 loop1StepStmt .normal s2 := by
          have h9s1 : s1.locals 9 = some (u32 j) := by rw [hl9]; exact h9
          have hev : evalExpr Gen.prog 10 s1 (.cast ⟨32, false⟩
              (.bin .add (some ⟨32, false⟩) (.cast ⟨32, false⟩ (.var 9)) (.const (.int ⟨32, false⟩ 1))))
              = .ok (u32 (j+1)) := by
            simp [evalExpr, evalCast, evalBin, evalBinInt, binInt, intOf, isPtr,
              IntTy.toInt, IntTy.wrap, IntTy.modulus, u32, i32, h9s1, IntTy.u32] <;> omega
          exact ExS.set (EvE_of_eval hev)
        have hInv2 : Loop1Inv (posBlock := posBlock) p m mb tb (j+1) s2 := by
          simpa [s2, Locals.upd, Loop1Inv] using hInv1
        have h9s2 : s2.locals 9 = some (u32 (j+1)) := by simp [s2, Locals.upd]
        obtain ⟨sf, hloopf, hInvf, h9f⟩ := ih hd_le s2 (by simpa [hjeq] using h9s2) (by simpa [hjeq] using hInv2)
        refine ⟨sf, ?_, hInvf, h9f⟩
        unfold Gen.validate_material_loop1
        exact ExS.loop_next hbody (Or.inl rfl) hstep hloopf
  exact hP 7 (by omega) s0 h9zero hInv0

def maxBlock : Block :=
  encodeLE 4 18 ++ encodeLE 4 4 ++ encodeLE 4 4 ++ encodeLE 4 4 ++
  encodeLE 4 4 ++ encodeLE 4 2 ++ encodeLE 4 2

def setSlot (blk : Block) (i v : Nat) : Block :=
  blk.take (4*i) ++ encodeLE 4 v ++ blk.drop (4*i+4)

theorem maxBlock_ArrEq : ArrEq maxBlock maxArr := by
  intro i
  have hv : i.val = 0 ∨ i.val = 1 ∨ i.val = 2 ∨ i.val = 3 ∨ i.val = 4 ∨ i.val = 5 ∨ i.val = 6 := by omega
  rcases hv with h|h|h|h|h|h|h
  · have : i = ⟨0, by omega⟩ := Fin.ext h; rw [this]; simp [maxBlock, maxArr, ArrEq, encodeLE, decodeLE, PieceType.handMax]
  · have : i = ⟨1, by omega⟩ := Fin.ext h; rw [this]; simp [maxBlock, maxArr, ArrEq, encodeLE, decodeLE, PieceType.handMax]
  · have : i = ⟨2, by omega⟩ := Fin.ext h; rw [this]; simp [maxBlock, maxArr, ArrEq, encodeLE, decodeLE, PieceType.handMax]
  · have : i = ⟨3, by omega⟩ := Fin.ext h; rw [this]; simp [maxBlock, maxArr, ArrEq, encodeLE, decodeLE, PieceType.handMax]
  · have : i = ⟨4, by omega⟩ := Fin.ext h; rw [this]; simp [maxBlock, maxArr, ArrEq, encodeLE, decodeLE, PieceType.handMax]
  · have : i = ⟨5, by omega⟩ := Fin.ext h; rw [this]; simp [maxBlock, maxArr, ArrEq, encodeLE, decodeLE, PieceType.handMax]
  · have : i = ⟨6, by omega⟩ := Fin.ext h; rw [this]; simp [maxBlock, maxArr, ArrEq, encodeLE, decodeLE, PieceType.handMax]

theorem decodeLE_replicate_zero : ∀ k, decodeLE (List.replicate k (0:UInt8)) = (0:Nat) := by
  intro k
  induction k with
  | zero => simp [decodeLE]
  | succ k ih =>
      change decodeLE ((0 : UInt8) :: List.replicate k 0) = 0
      simp [decodeLE, ih]

theorem max_index {s : State} {mb i : Nat} {MB : Block} (hi : i < 7)
    (h1 : s.locals 1 = some (.ptr mb 0)) (hmb : s.mem mb = some MB) (hlen : MB.length = 28) :
    EvE Gen.prog s (.index (.var 1) (.const (.int ⟨64, false⟩ i)) 4) (.ptr mb (4*i)) := by
  have haddr : evalExpr Gen.prog 10 s (.index (.var 1) (.const (.int ⟨64, false⟩ i)) 4) = .ok (.ptr mb (4*i)) := by
    simp [evalExpr, evalUn, intOf, IntTy.toInt, IntTy.u64, ptrAddN, h1, hmb, hlen]
    rw [if_pos (show i * 4 ≤ 28 by omega)]
    congr 2 <;> omega
  exact EvE_of_eval haddr

theorem store_max_slot {s : State} {mb i v : Nat} {MB : Block} (hi : i < 7) (hv : v < 2^30)
    (h1 : s.locals 1 = some (.ptr mb 0)) (hmb : s.mem mb = some MB) (hlen : MB.length = 28)
    (hro : s.ro = false) :
    ExS Gen.prog s (.store (.int ⟨32, false⟩) (.index (.var 1) (.const (.int ⟨64, false⟩ i)) 4)
      (.cast ⟨32, false⟩ (.const (.int ⟨32, true⟩ v)))) .normal
      { s with mem := s.mem.upd mb (setSlot MB i v) } := by
  have hev : EvE Gen.prog s (.cast ⟨32, false⟩ (.const (.int ⟨32, true⟩ v)))
      (.int ⟨32, false⟩ v) := by
    exact EvE.cast (EvE.const (v := .int ⟨32, true⟩ v)) (evalCast_u32_of_i32 v (by omega))
  have hstore : store s.mem (Ty.int ⟨32, false⟩) (.ptr mb (4*i)) (.int ⟨32, false⟩ v) =
      .ok (s.mem.upd mb (setSlot MB i v)) := by
    simp [store, writeBytes, hmb, Ty.size, IntTy.bytes, setSlot, encodeLE_length,
      show 4*i + 4 ≤ MB.length by omega]
  exact ExS.store (max_index hi h1 hmb hlen) hev hro hstore

-- applying stores 0..6 to a zero block yields maxBlock
theorem init_stores_result :
    setSlot (setSlot (setSlot (setSlot (setSlot (setSlot (setSlot (List.replicate 28 0) 0 18) 1 4) 2 4) 3 4) 4 4) 5 2) 6 2 = maxBlock := by
  decide +kernel

theorem validate_material_spec {p : Position} (hs : p.Shaped) (hmat : p.materialOk = true)
    {m : Mem} {n : Nat} (hm : m posBlock = some (encode p)) (hf : Fresh m n) (hn64 : n + 2 < 2^64) (hpm0 : posBlock ≠ 0) :
    ∃ sf, ExS Gen.prog ⟨frameLocals Gen.validate_material.params [posPtr' posBlock], m, false⟩
      Gen.validate_material.body (.ret (some (.int ⟨8, false⟩ 1))) sf ∧
      sf.mem posBlock = some (encode p) ∧
      (∀ b, b ≠ 0 → b ≠ n → b ≠ n + 1 → sf.mem b = m b) := by
  let s0 : State := ⟨frameLocals Gen.validate_material.params [posPtr' posBlock], m, false⟩
  have hn0 : n ≠ 0 := hf.2.1
  have hn1 : n + 1 ≠ 0 := by omega
  have hposn : posBlock < n := posBlock_lt_of_fresh (m := m) (p := p) hf hm
  have hpmn : posBlock ≠ n := by omega
  have hpmn1 : posBlock ≠ n + 1 := by omega
  have hp0 : posBlock ≠ 0 := hpm0
  -- alloc maximum
  have e1 : ExS Gen.prog s0 (.alloc 1 28) .normal
      { s0 with mem := (s0.mem.upd 0 (encodeLE 8 (n+1))).upd n (List.replicate 28 0),
                locals := s0.locals.upd 1 (.ptr n 0) } :=
    exec_alloc (hf.allocAt (by omega)) 1 28
  let s1 : State := { s0 with mem := (s0.mem.upd 0 (encodeLE 8 (n+1))).upd n (List.replicate 28 0), locals := s0.locals.upd 1 (.ptr n 0) }
  have hs1_1 : s1.locals 1 = some (.ptr n 0) := by simp [s1, s0, frameLocals, Locals.upd]
  have hs1_mb : s1.mem n = some (List.replicate 28 0) := by simp [s1, Mem.upd]
  have hs1_ro : s1.ro = false := by simp [s1, s0]
  -- 7 stores (named blocks keep the state facts simple)
  let B0 : Block := List.replicate 28 0
  let B1 := setSlot B0 0 18
  let B2 := setSlot B1 1 4
  let B3 := setSlot B2 2 4
  let B4 := setSlot B3 3 4
  let B5 := setSlot B4 4 4
  let B6 := setSlot B5 5 2
  let B7 := setSlot B6 6 2
  let s2a : State := { s1 with mem := s1.mem.upd n B1 }
  have e2a : ExS Gen.prog s1 (.store (.int ⟨32, false⟩) (.index (.var 1) (.const (.int ⟨64, false⟩ 0)) 4)
      (.cast ⟨32, false⟩ (.const (.int ⟨32, true⟩ 18)))) .normal s2a := by
    dsimp [s2a]; exact store_max_slot (s := s1) (mb := n) (i := 0) (v := 18) (MB := B0)
      (by omega) (by omega) hs1_1 (by simp [s1, B0, Mem.upd]) (by simp [B0]) hs1_ro
  let s2b : State := { s2a with mem := s2a.mem.upd n B2 }
  have e2b : ExS Gen.prog s2a (.store (.int ⟨32, false⟩) (.index (.var 1) (.const (.int ⟨64, false⟩ 1)) 4)
      (.cast ⟨32, false⟩ (.const (.int ⟨32, true⟩ 4)))) .normal s2b := by
    dsimp [s2b]; exact store_max_slot (s := s2a) (mb := n) (i := 1) (v := 4) (MB := B1)
      (by omega) (by omega) (by simp [s2a, hs1_1]) (by simp [s2a, Mem.upd]) (by simp [B1, setSlot, encodeLE_length, B0] <;> omega) (by simp [s2a, hs1_ro])
  let s2c : State := { s2b with mem := s2b.mem.upd n B3 }
  have e2c : ExS Gen.prog s2b (.store (.int ⟨32, false⟩) (.index (.var 1) (.const (.int ⟨64, false⟩ 2)) 4)
      (.cast ⟨32, false⟩ (.const (.int ⟨32, true⟩ 4)))) .normal s2c := by
    dsimp [s2c]; exact store_max_slot (s := s2b) (mb := n) (i := 2) (v := 4) (MB := B2)
      (by omega) (by omega) (by simp [s2b, s2a, hs1_1]) (by simp [s2b, Mem.upd]) (by simp [B2, B1, setSlot, encodeLE_length, B0] <;> omega) (by simp [s2b, s2a, hs1_ro])
  let s2d : State := { s2c with mem := s2c.mem.upd n B4 }
  have e2d : ExS Gen.prog s2c (.store (.int ⟨32, false⟩) (.index (.var 1) (.const (.int ⟨64, false⟩ 3)) 4)
      (.cast ⟨32, false⟩ (.const (.int ⟨32, true⟩ 4)))) .normal s2d := by
    dsimp [s2d]; exact store_max_slot (s := s2c) (mb := n) (i := 3) (v := 4) (MB := B3)
      (by omega) (by omega) (by simp [s2c, s2b, s2a, hs1_1]) (by simp [s2c, Mem.upd]) (by simp [B3, B2, B1, setSlot, encodeLE_length, B0] <;> omega) (by simp [s2c, s2b, s2a, hs1_ro])
  let s2e : State := { s2d with mem := s2d.mem.upd n B5 }
  have e2e : ExS Gen.prog s2d (.store (.int ⟨32, false⟩) (.index (.var 1) (.const (.int ⟨64, false⟩ 4)) 4)
      (.cast ⟨32, false⟩ (.const (.int ⟨32, true⟩ 4)))) .normal s2e := by
    dsimp [s2e]; exact store_max_slot (s := s2d) (mb := n) (i := 4) (v := 4) (MB := B4)
      (by omega) (by omega) (by simp [s2d, s2c, s2b, s2a, hs1_1]) (by simp [s2d, Mem.upd]) (by simp [B4, B3, B2, B1, setSlot, encodeLE_length, B0] <;> omega) (by simp [s2d, s2c, s2b, s2a, hs1_ro])
  let s2f : State := { s2e with mem := s2e.mem.upd n B6 }
  have e2f : ExS Gen.prog s2e (.store (.int ⟨32, false⟩) (.index (.var 1) (.const (.int ⟨64, false⟩ 5)) 4)
      (.cast ⟨32, false⟩ (.const (.int ⟨32, true⟩ 2)))) .normal s2f := by
    dsimp [s2f]; exact store_max_slot (s := s2e) (mb := n) (i := 5) (v := 2) (MB := B5)
      (by omega) (by omega) (by simp [s2e, s2d, s2c, s2b, s2a, hs1_1]) (by simp [s2e, Mem.upd]) (by simp [B5, B4, B3, B2, B1, setSlot, encodeLE_length, B0] <;> omega) (by simp [s2e, s2d, s2c, s2b, s2a, hs1_ro])
  let s2 : State := { s2f with mem := s2f.mem.upd n B7 }
  have e2g : ExS Gen.prog s2f (.store (.int ⟨32, false⟩) (.index (.var 1) (.const (.int ⟨64, false⟩ 6)) 4)
      (.cast ⟨32, false⟩ (.const (.int ⟨32, true⟩ 2)))) .normal s2 := by
    dsimp [s2]; exact store_max_slot (s := s2f) (mb := n) (i := 6) (v := 2) (MB := B6)
      (by omega) (by omega) (by simp [s2f, s2e, s2d, s2c, s2b, s2a, hs1_1]) (by simp [s2f, Mem.upd]) (by simp [B6, B5, B4, B3, B2, B1, setSlot, encodeLE_length, B0] <;> omega) (by simp [s2f, s2e, s2d, s2c, s2b, s2a, hs1_ro])
  have hB7 : B7 = maxBlock := by rfl
  have hs2_mb : s2.mem n = some maxBlock := by simp [s2, Mem.upd, hB7]
  have hs2_1 : s2.locals 1 = some (.ptr n 0) := by simp [s2, s2f, s2e, s2d, s2c, s2b, s2a, hs1_1]
  -- alloc total
  have hf2 : Fresh s2.mem (n+1) := by
    refine ⟨?_, by omega, ?_⟩
    · simp [s2, s2f, s2e, s2d, s2c, s2b, s2a, s1, s0, Mem.upd, hf.1, hn0, show 0 ≠ n by omega]
    · intro x hx
      have hx0 : x ≠ 0 := by omega
      have hxn : x ≠ n := by omega
      have hsx : s2.mem x = m x := by
        simp [s2, s2f, s2e, s2d, s2c, s2b, s2a, s1, s0, Mem.upd, hx0, hxn]
      rw [hsx]
      exact hf.2.2 x (by omega)
  have e3 : ExS Gen.prog s2 (.alloc 2 28) .normal
      { s2 with mem := (s2.mem.upd 0 (encodeLE 8 (n+2))).upd (n+1) (List.replicate 28 0),
                locals := s2.locals.upd 2 (.ptr (n+1) 0) } :=
    exec_alloc (hf2.allocAt (by omega)) 2 28
  let s3 : State := { s2 with mem := (s2.mem.upd 0 (encodeLE 8 (n+2))).upd (n+1) (List.replicate 28 0), locals := s2.locals.upd 2 (.ptr (n+1) 0) }
  -- set 3 = u8 0
  have e4 : ExS Gen.prog s3 (.set 3 (.cast ⟨8, false⟩ (.const (.int ⟨32, true⟩ 0)))) .normal
      { s3 with locals := s3.locals.upd 3 (u8 0) } := by
    exact ExS.set (EvE_of_eval (n := 3) (by simp [evalExpr, evalCast, IntTy.wrap, IntTy.modulus, IntTy.toInt, IntTy.i32, IntTy.u8, u8, boolVal]))
  let s4 := { s3 with locals := s3.locals.upd 3 (u8 0) }
  -- loop0 invariant
  have hInv0 : Inv0T (posBlock := posBlock) p s4.mem n (n+1) 0 s4 := by
    refine ⟨maxBlock, List.replicate 28 0, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp [s4, s3, s2, s2f, s2e, s2d, s2c, s2b, s2a, s1, s0, frameLocals, Gen.validate_material, Locals.upd]
    · simp [s4, s3, s2, s2f, s2e, s2d, s2c, s2b, s2a, s1, s0, frameLocals, Gen.validate_material, Locals.upd]
    · simp [s4, s3, Locals.upd, hs2_1]
    · simp [s4, Locals.upd]
    · simpa [s4, s3, Mem.upd, hn0, show n ≠ n+1 by omega] using hs2_mb
    · simp [maxBlock, encodeLE_length]
    · exact maxBlock_ArrEq
    · simp [s4, s3, Mem.upd]
    · simp
    · intro i
      rw [boardFamCount]
      simp [famAt]
      change decodeLE (List.take 4 (List.drop (4 * i.val) (List.replicate 28 (0:UInt8)))) = 0
      rw [List.drop_replicate, List.take_replicate]
      exact decodeLE_replicate_zero _
    · simpa [s4, s3, s2, s2f, s2e, s2d, s2c, s2b, s2a, s1, s0, Mem.upd, hpmn,
        hpmn1, hp0, frameLocals] using hm
    · omega
    · exact hn0
    · exact Nat.succ_ne_zero n
    · exact hpmn
    · exact hpmn1
    · intro b hb0 hbn hbn1
      simp [s4, s3, s2, s2f, s2e, s2d, s2c, s2b, s2a, s1, s0, Mem.upd_ne hb0,
        Mem.upd_ne hbn, Mem.upd_ne hbn1]
    · rfl
  obtain ⟨s5, hloop0, hInv81⟩ := loop0_runs p s4.mem n (n+1) s4 hs.1 hInv0

  -- set 9 = u32 0
  have e5 : ExS Gen.prog s5 (.set 9 (.cast ⟨32, false⟩ (.const (.int ⟨32, true⟩ 0)))) .normal
      { s5 with locals := s5.locals.upd 9 (u32 0) } := by
    exact ExS.set (EvE_of_eval (n := 3) (by
      simp [evalExpr, evalCast, IntTy.wrap, IntTy.modulus, IntTy.toInt, IntTy.i32, IntTy.u32, u32]))
  let s6 : State := { s5 with locals := s5.locals.upd 9 (u32 0) }
  have h9zero : s6.locals 9 = some (u32 0) := by simp [s6, Locals.upd]
  obtain ⟨MB81, T81, i0, i1, i2, i3, iMB, ilenMB, iArrMB, iTB, ilenT, iTot, ipos,
    imbtb, imb0, itb0, ipm, ipt, iframe, iro⟩ := hInv81
  have hInv1 : Loop1Inv (posBlock := posBlock) p s6.mem n (n+1) 0 s6 := by
    refine ⟨MB81, T81, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simpa [s6, Locals.upd] using i0
    · simpa [s6, Locals.upd] using i1
    · simpa [s6, Locals.upd] using i2
    · simpa [s6, Locals.upd] using iMB
    · exact ilenMB
    · exact iArrMB
    · simpa [s6, Locals.upd] using iTB
    · exact ilenT
    · intro i; simpa using iTot i
    · simpa [s6, Locals.upd] using ipos
    · exact imbtb
    · exact imb0
    · exact itb0
    · exact ipm
    · exact ipt
    · intro b hb0 hbn hbn1; simpa [s6, Locals.upd] using iframe b hb0 hbn hbn1
    · simpa [s6, Locals.upd] using iro
  obtain ⟨s7, hloop1, hInv7, h97⟩ := loop1_runs p hs hmat s6.mem n (n+1) s6 h9zero hInv1
  -- final return (1 != 0) -> u8 1
  have hret : ExS Gen.prog s7 (.ret (some (.cast ⟨8, false⟩ (.bin .ne (some ⟨32, true⟩)
      (.const (.int ⟨32, true⟩ 1)) (.const (.int ⟨32, true⟩ 0)))))) (.ret (some (.int ⟨8, false⟩ 1))) s7 := by
    apply ExS.ret
    refine EvE_of_eval (n := 10) ?_
    simp [evalExpr, evalCast, evalBin, evalBinInt, binInt, intOf, isPtr, IntTy.wrap,
      IntTy.modulus, IntTy.toInt, IntTy.i32, IntTy.u8, u8, boolVal]
  refine ⟨s7, ?_, ?_, ?_⟩
  · unfold Gen.validate_material
    exact ExS.seq (ExS.seq e1 (ExS.seq e2a (ExS.seq e2b (ExS.seq e2c (ExS.seq e2d
      (ExS.seq e2e (ExS.seq e2f e2g)))))))
      (ExS.seq e3 (ExS.seq (ExS.seq e4 hloop0) (ExS.seq (ExS.seq e5 hloop1) hret)))
  · obtain ⟨_, _, _, _, _, _, _, _, _, _, _, mp7, _, _, _, _, _, _, _⟩ := hInv7
    simpa [s6, Locals.upd] using mp7
  · obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, f7, _⟩ := hInv7
    intro b hb0 hbn hbn1
    have h1 := f7 b hb0 hbn hbn1
    have h2 := iframe b hb0 hbn hbn1
    have h3 : s4.mem b = m b := by
      simpa [s4, s3, s2, s2f, s2e, s2d, s2c, s2b, s2a, s1, s0, Mem.upd, hb0, hbn, hbn1]
    rw [h1, h2, h3]

end Shogi.C.Proofs
