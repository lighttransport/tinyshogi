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

end Shogi.C.Proofs
