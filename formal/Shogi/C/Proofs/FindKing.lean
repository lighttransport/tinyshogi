/-
  T7 layer 2, first symbolic refinement: `find_king`, for every position.
  Method (reused by later proofs): expression judgements come from one
  symbolic `evalExpr` computation (`EvE_of_eval`, via fuel monotonicity);
  statements are composed with the `ExS` rules; loops by induction on the
  iterations left; board bytes are read through the abstraction `encode`.
-/
import Shogi.C.Model

namespace Shogi.C.Proofs
open MiniC Shogi Shogi.C

/-- `shogi_piece(c, KING)` in any memory. -/
theorem shogi_piece_king (c : Color) (m : Mem) (ro : Bool) :
    ExS Gen.prog ⟨frameLocals Gen.shogi_piece.params [.int IntTy.u32 c.idx, .int IntTy.u32 8], m, ro⟩
      Gen.shogi_piece.body (.ret (some (.int IntTy.u8 (8 + 16 * c.idx))))
      ⟨frameLocals Gen.shogi_piece.params [.int IntTy.u32 c.idx, .int IntTy.u32 8], m, ro⟩ :=
  ExS_of_execStmt Gen.prog (n := 10) (by cases c <;> rfl)

/-- Byte `k < 81` of the encoded board. -/
theorem encode_board (p : Position) (k : Nat) (hk : k < 81) :
    (encode p).getD k 0 = pieceByte (p.pieceAt ⟨k, hk⟩) := by
  simp only [encode]
  rw [List.getD_eq_getElem?_getD]
  simp [List.getElem?_append_left, hk]

theorem readBoard {m : Mem} {p : Position} (hm : m posBlock = some (encode p)) (k : Nat) (hk : k < 81) :
    readBytes m posBlock k 1 = .ok [pieceByte (p.pieceAt ⟨k, hk⟩)] := by
  have hlen : k + 1 ≤ (encode p).length := by
    simp [encode]; omega
  simp only [readBytes, hm, hlen, ite_true]
  rw [← encode_board p k hk]
  congr 1
  rw [List.take_one, List.head?_drop]
  simp [List.getD, show k < (encode p).length by omega]

/-- Board byte as a number (0 off the board). -/
def bb (p : Position) (j : Nat) : Nat :=
  if h : j < 81 then (pieceByte (p.pieceAt ⟨j, h⟩)).toNat else 0

theorem bb_lt (p : Position) (j : Nat) : bb p j < 256 := by
  unfold bb; split
  · exact UInt8.toNat_lt _
  · omega

/-- First square `j ≥ k` whose byte is `K`. -/
def firstFrom (p : Position) (K k : Nat) : Option Nat :=
  ((List.range 81).filter fun j => decide (k ≤ j) && decide (bb p j = K)).head?

macro "mc_eval" : tactic => `(tactic| simp [evalExpr, evalBin, evalCast, evalBinInt, binInt, isPtr,
  intOf, IntTy.toInt, IntTy.wrap, IntTy.modulus, boolVal, IntTy.u8, IntTy.i32, Res.bind,
  truthy, ptrAddN, load, Ty.size, IntTy.bytes])

section
variable (p : Position) (s : State) (k K : Nat)

theorem ev_lt81 {i : Nat} (hk : k < 256) (h8 : s.locals i = some (.int IntTy.u8 k)) :
    evalExpr Gen.prog 5 s (.bin .lt (some ⟨32, true⟩) (.cast ⟨32, true⟩ (.var i))
      (.const (.int ⟨32, true⟩ 81))) = .ok (boolVal (decide (k < 81))) := by
  simp [evalExpr, evalBin, evalCast, evalBinInt, binInt, isPtr, intOf, IntTy.toInt, IntTy.wrap,
    IntTy.modulus, boolVal, IntTy.u8, Res.bind, h8, Nat.mod_eq_of_lt (show k < 4294967296 by omega)]
  have : ¬ (2147483648 ≤ k) := by omega
  simp only [this, ite_false]
  by_cases h : k < 81
  · simp [h, show ((k : Int) < 81) by omega]
  · simp [h, show ¬ ((k : Int) < 81) by omega]

theorem ev_cmp {i j : Nat} (hk : k < 81) (hK : K < 256) (hm : s.mem posBlock = some (encode p))
    (h0 : s.locals 0 = some posPtr) (h6 : s.locals j = some (.int IntTy.u8 K))
    (h8 : s.locals i = some (.int IntTy.u8 k)) :
    evalExpr Gen.prog 6 s (.bin .eq (some ⟨32, true⟩) (.cast ⟨32, true⟩ (.load (.int ⟨8, false⟩)
      (.index (.field (.var 0) 0) (.var i) 1))) (.cast ⟨32, true⟩ (.var j)))
      = .ok (boolVal (decide (bb p k = K))) := by
  have hlen : (encode p).length = 114 := by simp [encode, Gen.off_side, Gen.off_king_square, le32]
  have hr := readBoard hm k hk
  have hbb : bb p k = (pieceByte (p.pieceAt ⟨k, hk⟩)).toNat := by simp [bb, hk]
  have hlt := bb_lt p k
  simp only [evalExpr, h0, h6, h8, posPtr, Res.bind_eq, Res.bind_ok, ptrAddN, hm, hlen]
  simp only [show 0 + 0 ≤ 114 by omega, ite_true, Res.bind, IntTy.u8, Bool.false_eq_true,
    ite_false, hm, hlen, Nat.zero_add, Nat.mul_one, show k ≤ 114 by omega, load, Ty.size,
    IntTy.bytes, show (8:Nat) / 8 = 1 by rfl, hr]
  simp [evalCast, evalBin, isPtr, evalBinInt, binInt, intOf, IntTy.toInt, IntTy.wrap,
    IntTy.modulus, boolVal, decodeLE, ← hbb]
  have a1 : ¬ (2147483648 ≤ bb p k) := by omega
  have a2 : ¬ (2147483648 ≤ K) := by omega
  rw [Nat.mod_eq_of_lt (show bb p k < 4294967296 by omega),
    Nat.mod_eq_of_lt (show K < 4294967296 by omega)]
  have e1 : ((bb p k : Int) % 4294967296) = bb p k := Int.emod_eq_of_lt (by omega) (by omega)
  have e2 : ((K : Int) % 4294967296) = K := Int.emod_eq_of_lt (by omega) (by omega)
  simp only [a1, a2, ite_false, e1, e2, Int.natCast_inj]

end

def true8 : Val := .int IntTy.u8 1

theorem ev_true8 (s : State) :
    evalExpr Gen.prog 5 s (.cast ⟨8, false⟩ (.bin .ne (some ⟨32, true⟩) (.const (.int ⟨32, true⟩ 1))
      (.const (.int ⟨32, true⟩ 0)))) = .ok true8 := by rfl

theorem ev_succ {v : Nat} (s : State) (k : Nat) (hk : k < 81) (h8 : s.locals v = some (.int IntTy.u8 k)) :
    evalExpr Gen.prog 5 s (.cast ⟨8, false⟩ (.bin .add (some ⟨32, true⟩) (.cast ⟨32, true⟩ (.var v))
      (.const (.int ⟨32, true⟩ 1)))) = .ok (.int IntTy.u8 (k + 1)) := by
  simp [evalExpr, evalBin, evalCast, evalBinInt, binInt, isPtr, intOf, IntTy.toInt, IntTy.wrap,
    IntTy.modulus, IntTy.u8, Res.bind, h8, arith, IntTy.inRange, IntTy.minVal, IntTy.maxVal,
    Nat.mod_eq_of_lt (show k < 4294967296 by omega)]
  have : ¬ (2147483648 ≤ k) := by omega
  simp only [this, ite_false]
  rw [if_pos (by omega)]
  have e : ((k : Int) + 1) % 4294967296 = (k : Int) + 1 := Int.emod_eq_of_lt (by omega) (by omega)
  simp only [e]
  have e2 : ((k : Int) + 1).toNat = k + 1 := by omega
  simp only [e2]
  have e3 : ((k : Int) + 1) % 256 = (k : Int) + 1 := Int.emod_eq_of_lt (by omega) (by omega)
  simp [e3]; omega

theorem firstFrom_81 (p : Position) (K : Nat) : firstFrom p K 81 = none := by
  unfold firstFrom
  rw [List.head?_eq_none_iff, List.filter_eq_nil_iff]
  intro j hj
  simp at hj ⊢; omega

theorem filter_range_from (f : Nat → Bool) (k n : Nat) (hk : k < n) :
    ((List.range n).filter fun j => decide (k ≤ j) && f j) =
      (if f k then [k] else []) ++ ((List.range n).filter fun j => decide (k + 1 ≤ j) && f j) := by
  induction n with
  | zero => omega
  | succ n ih =>
    rw [List.range_succ, List.filter_append, List.filter_append]
    by_cases hkn : k < n
    · rw [ih hkn]
      simp only [List.filter_cons, List.filter_nil, List.append_assoc]
      have : ¬ (n ≤ k) := by omega
      simp [show k + 1 ≤ n by omega, show k ≤ n by omega]
    · have hkn' : k = n := by omega
      subst hkn'
      have h1 : ((List.range k).filter fun j => decide (k ≤ j) && f j) = [] := by
        rw [List.filter_eq_nil_iff]; intro j hj; simp at hj ⊢; omega
      have h2 : ((List.range k).filter fun j => decide (k + 1 ≤ j) && f j) = [] := by
        rw [List.filter_eq_nil_iff]; intro j hj; simp at hj ⊢; omega
      rw [h1, h2]
      cases hf : f k <;> simp [hf]

theorem firstFrom_step (p : Position) (K k : Nat) (hk : k < 81) :
    firstFrom p K k = if bb p k = K then some k else firstFrom p K (k + 1) := by
  unfold firstFrom
  rw [filter_range_from (fun j => decide (bb p j = K)) k 81 hk]
  by_cases h : bb p k = K <;> simp [h]

/-- The search loop of `find_king`: starting at index `k`, it returns 1
    after storing the first square `j ≥ k` whose byte is `K`, or finishes
    normally if there is none. Memory is changed only by that store. -/
theorem store_u8_ok {m : Mem} {ob : Nat} {blk : Block} (hob : m ob = some blk)
    (hl : 1 ≤ blk.length) (v : Nat) :
    store m (.int IntTy.u8) (.ptr ob 0) (.int IntTy.u8 v) = .ok (m.upd ob (encodeLE 1 v ++ blk.drop 1)) := by
  simp [store, writeBytes, hob, IntTy.u8, IntTy.bytes, encodeLE, hl]

theorem find_king_loop (p : Position) (K ob : Nat) (hK : K < 256) :
    ∀ d k (s : State), k + d = 81 →
    s.locals 0 = some posPtr → s.locals 2 = some (.ptr ob 0) →
    s.locals 6 = some (.int IntTy.u8 K) → s.locals 8 = some (.int IntTy.u8 k) →
    s.mem posBlock = some (encode p) → s.ro = false →
    (∃ blk, s.mem ob = some blk ∧ 1 ≤ blk.length) →
    match firstFrom p K k with
    | some j => ∃ s', ExS Gen.prog s Gen.find_king_loop0 (.ret (some true8)) s' ∧
        store s.mem (.int IntTy.u8) (.ptr ob 0) (.int IntTy.u8 j) = .ok s'.mem
    | none => ∃ s', ExS Gen.prog s Gen.find_king_loop0 .normal s' ∧ s'.mem = s.mem := by
  intro d
  induction d with
  | zero =>
    intro k s hk h0 h2 h6 h8 hm hro _
    have : k = 81 := by omega
    subst this
    rw [firstFrom_81]
    refine ⟨s, ?_, rfl⟩
    unfold Gen.find_king_loop0
    apply ExS.loop_brk
    exact ExS.ite (EvE_of_eval (ev_lt81 s 81 (by decide) h8)) (by rfl) ExS.brk
  | succ d ih =>
    intro k s hk h0 h2 h6 h8 hm hro hob
    have hk81 : k < 81 := by omega
    have hcond := EvE_of_eval (ev_lt81 s k (by omega) h8)
    have hcmp := EvE_of_eval (ev_cmp p s k K hk81 hK hm h0 h6 h8)
    rw [firstFrom_step p K k hk81]
    by_cases hb : bb p k = K
    · simp only [hb, ite_true]
      -- the store, then return 1
      obtain ⟨blk, hob1, hl⟩ := hob
      have hst := store_u8_ok hob1 hl k
      refine ⟨{ s with mem := _ }, ?_, hst⟩
      unfold Gen.find_king_loop0
      apply ExS.loop_ret
      refine ExS.ite (bc := true) hcond (by simp [boolVal, truthy, hk81]) ?_
      simp only [ite_true]
      refine ExS.ite (bc := true) hcmp (by simp [boolVal, truthy, hb]) ?_
      simp only [ite_true]
      refine ExS.seq (ExS.store (EvE_of_eval (n := 2) (by simp [evalExpr, h2]))
        (EvE_of_eval (n := 2) (by simp [evalExpr, h8])) hro hst) ?_
      exact ExS.ret (EvE_of_eval (ev_true8 _))
    · simp only [hb, ite_false]
      let s2 : State := { s with locals := s.locals.upd 8 (.int IntTy.u8 (k + 1)) }
      have ihs := ih (k + 1) s2 (by omega) (by simp [s2, Locals.upd, h0]) (by simp [s2, Locals.upd, h2])
        (by simp [s2, Locals.upd, h6]) (by simp [s2, Locals.upd]) hm hro hob
      have hbody : ExS Gen.prog s (.ite (.bin .lt (some ⟨32, true⟩) (.cast ⟨32, true⟩ (.var 8))
          (.const (.int ⟨32, true⟩ 81))) (.ite (.bin .eq (some ⟨32, true⟩) (.cast ⟨32, true⟩
          (.load (.int ⟨8, false⟩) (.index (.field (.var 0) 0) (.var 8) 1))) (.cast ⟨32, true⟩ (.var 6)))
          (.seq (.store (.int ⟨8, false⟩) (.var 2) (.var 8)) (.ret (some (.cast ⟨8, false⟩ (.bin .ne
          (some ⟨32, true⟩) (.const (.int ⟨32, true⟩ 1)) (.const (.int ⟨32, true⟩ 0))))))) .skip) .brk)
          .normal s := by
        refine ExS.ite (bc := true) hcond (by simp [boolVal, truthy, hk81]) ?_
        simp only [ite_true]
        refine ExS.ite (bc := false) hcmp (by simp [boolVal, truthy, hb]) ?_
        exact ExS.skip
      have hstep : ExS Gen.prog s (.set 8 (.cast ⟨8, false⟩ (.bin .add (some ⟨32, true⟩)
          (.cast ⟨32, true⟩ (.var 8)) (.const (.int ⟨32, true⟩ 1))))) .normal s2 :=
        ExS.set (EvE_of_eval (ev_succ s k hk81 h8))
      revert ihs
      cases firstFrom p K (k + 1) with
      | some j =>
        intro ⟨s', hs', hst⟩
        exact ⟨s', ExS.loop_next hbody (Or.inl rfl) hstep hs', hst⟩
      | none =>
        intro ⟨s', hs', hmem⟩
        exact ⟨s', ExS.loop_next hbody (Or.inl rfl) hstep hs', hmem⟩

theorem encode_length (p : Position) : (encode p).length = 114 := by
  simp [encode, Gen.off_side, Gen.off_king_square, le32]

theorem encode_king (p : Position) (c : Color) :
    (encode p).getD (112 + c.idx) 0 = kingByte p c := by
  cases c <;> simp [encode, Gen.off_side, Gen.off_king_square, le32, List.getD, Color.idx,
    List.getElem?_append_right]

/-- The king byte. -/
def kb (c : Color) : Nat := 8 + 16 * c.idx

theorem pieceByte_king_iff (x : Option Piece) (c : Color) :
    (pieceByte x).toNat = kb c ↔ x = some ⟨c, .king⟩ := by
  rcases x with _ | ⟨c', t⟩
  · cases c <;> simp [pieceByte, kb, Color.idx]
  · cases c <;> cases c' <;> cases t <;> simp [pieceByte, kb, Color.idx, Piece.code, PieceType.code]

theorem map_val_finRange (n : Nat) : (List.finRange n).map (·.val) = List.range n := by
  apply List.ext_getElem <;> simp

theorem firstFrom_kingSquare (p : Position) (c : Color) :
    firstFrom p (kb c) 0 = (p.kingSquare c).map (·.val) := by
  unfold firstFrom Position.kingSquare
  rw [List.head?_filter, ← map_val_finRange, List.find?_map]
  congr 1
  congr 1
  funext x
  simp only [Function.comp, Nat.zero_le, decide_true, Bool.true_and, bb, x.isLt, dite_true]
  by_cases h : p.pieceAt x = some ⟨c, .king⟩
  · simp only [h, beq_self_eq_true, decide_eq_true_eq]
    exact (pieceByte_king_iff _ c).mpr rfl
  · have : ¬ (pieceByte (p.pieceAt x)).toNat = kb c := fun e => h ((pieceByte_king_iff _ c).mp e)
    simp [h, this]

def false8 : Val := .int IntTy.u8 0

theorem ev_cache (p : Position) (s : State) (c : Color) (hm : s.mem posBlock = some (encode p))
    (h0 : s.locals 0 = some posPtr) (h1 : s.locals 1 = some (.int IntTy.u32 c.idx)) :
    evalExpr Gen.prog 5 s (.load (.int ⟨8, false⟩) (.index (.field (.var 0) 112) (.var 1) 1))
      = .ok (.int IntTy.u8 (kingByte p c).toNat) := by
  have hl := encode_length p
  have hci : c.idx < 2 := by cases c <;> decide
  have hr : readBytes s.mem posBlock (112 + c.idx) 1 = .ok [kingByte p c] := by
    simp only [readBytes, hm, hl, show 112 + c.idx + 1 ≤ 114 by omega, ite_true]
    rw [← encode_king p c]
    congr 1
    rw [List.take_one, List.head?_drop]
    simp [List.getD, show 112 + c.idx < (encode p).length by omega]
  simp only [evalExpr, h0, h1, posPtr, Res.bind_eq, Res.bind_ok, ptrAddN, hm, hl,
    show 0 + 112 ≤ 114 by omega, ite_true, Res.bind, IntTy.u32, Bool.false_eq_true, ite_false,
    Nat.zero_add, Nat.mul_one, show 112 + c.idx ≤ 114 by omega, load, Ty.size, IntTy.bytes,
    show (8:Nat) / 8 = 1 by rfl, hr]
  simp [decodeLE, IntTy.u8]

theorem kingSquare_spec {p : Position} {c : Color} {sq : Square} (h : p.kingSquare c = some sq) :
    p.pieceAt sq = some ⟨c, .king⟩ := by
  unfold Position.kingSquare at h
  have := List.find?_some h
  simpa using this

theorem kingByte_some {p : Position} {c : Color} {sq : Square} (h : p.kingSquare c = some sq) :
    (kingByte p c).toNat = sq.val := by
  have := sq.isLt
  simp [kingByte, h, UInt8.toNat_ofNat]; omega

theorem kingByte_none {p : Position} {c : Color} (h : p.kingSquare c = none) :
    (kingByte p c).toNat = 255 := by
  simp [kingByte, h]

/-- **`find_king` refines `Position.kingSquare`.** For every position and
    colour: no UB, terminates; if the colour has a king, `*square` is set to
    its square and the result is 1, otherwise the result is 0 and memory is
    unchanged. (The cached `king_square` is the spec's king square, as
    `reset_history` and every make/unmake maintain.) -/
theorem find_king_refines (p : Position) (c : Color) (m : Mem) (ob : Nat) (blk : Block)
    (hm : m posBlock = some (encode p)) (hob : m ob = some blk) (hl : 1 ≤ blk.length) :
    match p.kingSquare c with
    | some sq => ∃ s', ExS Gen.prog ⟨frameLocals Gen.find_king.params
          [posPtr, .int IntTy.u32 c.idx, .ptr ob 0], m, false⟩ Gen.find_king.body
          (.ret (some true8)) s' ∧ store m (.int IntTy.u8) (.ptr ob 0) (.int IntTy.u8 sq.val) = .ok s'.mem
    | none => ∃ s', ExS Gen.prog ⟨frameLocals Gen.find_king.params
          [posPtr, .int IntTy.u32 c.idx, .ptr ob 0], m, false⟩ Gen.find_king.body
          (.ret (some false8)) s' ∧ s'.mem = m := by
  have hci : c.idx < 2 := by cases c <;> decide
  have hkb : kb c < 256 := by unfold kb; omega
  let L0 := frameLocals Gen.find_king.params [posPtr, .int IntTy.u32 c.idx, .ptr ob 0]
  have h0 : L0 0 = some posPtr := rfl
  have h1 : L0 1 = some (.int IntTy.u32 c.idx) := rfl
  have h2 : L0 2 = some (.ptr ob 0) := rfl
  let s0 : State := ⟨L0, m, false⟩
  let kc := (kingByte p c).toNat
  let s1 : State := { s0 with locals := s0.locals.upd 3 (.int IntTy.u8 kc) }
  have hset3 : ExS Gen.prog s0 (.set 3 (.load (.int ⟨8, false⟩) (.index (.field (.var 0) 112) (.var 1) 1)))
      .normal s1 := ExS.set (EvE_of_eval (ev_cache p s0 c hm (by simp [s0, h0]) (by simp [s0, h1])))
  have hkc : kc < 256 := UInt8.toNat_lt _
  have h13 : s1.locals 3 = some (.int IntTy.u8 kc) := by simp [s1, Locals.upd]
  -- the call shogi_piece(color, SHOGI_KING), result in local `d`
  have hcall : ∀ (st : State) (d : Nat), st.locals 1 = some (.int IntTy.u32 c.idx) →
      ExS Gen.prog st (.call (some d) 0 [(.var 1), (.cast ⟨32, false⟩ (.const (.int ⟨32, true⟩ 8)))])
        .normal { st with mem := st.mem, locals := st.locals.upd d (.int IntTy.u8 (kb c)) } := by
    intro st d hs1
    have hargs : evalArgs Gen.prog 6 st [(.var 1), (.cast ⟨32, false⟩ (.const (.int ⟨32, true⟩ 8)))]
        = .ok [.int IntTy.u32 c.idx, .int IntTy.u32 8] := by
      simp [evalArgs, evalExpr, hs1, evalCast, IntTy.wrap, IntTy.modulus, Res.bind]; decide
    have := ExS.call_dst (d := d) (f := 0) (s := st) (EvArgs_of_eval hargs)
      (rfl : Gen.prog 0 = some Gen.shogi_piece) rfl (shogi_piece_king c st.mem st.ro)
    simpa [kb] using this
  revert hset3
  cases hks : p.kingSquare c with
  | some sq =>
    intro hset3
    have hsq := kingSquare_spec hks
    have hkcq : kc = sq.val := kingByte_some hks
    have hbb : bb p sq.val = kb c := by
      simp [bb, sq.isLt, hsq, (pieceByte_king_iff _ c).mpr rfl]
    let s2 : State := { s1 with mem := s1.mem, locals := s1.locals.upd 4 (.int IntTy.u8 (kb c)) }
    have hc2 := hcall s1 4 (by simp [s1, s0, Locals.upd, h1])
    have hcmp := ev_cmp p s2 sq.val (kb c) (i := 3) (j := 4) sq.isLt hkb hm
      (by simp [s2, s1, s0, Locals.upd, h0]) (by simp [s2, Locals.upd])
      (by simp [s2, Locals.upd, h13, hkcq])
    have hland : EvE Gen.prog s2 (.land (.const (.int ⟨32, true⟩ 1)) (.bin .eq (some ⟨32, true⟩)
        (.cast ⟨32, true⟩ (.load (.int ⟨8, false⟩) (.index (.field (.var 0) 0) (.var 3) 1)))
        (.cast ⟨32, true⟩ (.var 4)))) (boolVal true) :=
      EvE.land_true (EvE.const _) rfl (EvE_of_eval hcmp) (by simp [hbb, boolVal, truthy])
    let s3 : State := { s2 with locals := s2.locals.upd 5 (boolVal true) }
    obtain hst := store_u8_ok hob hl sq.val
    refine ⟨{ s3 with mem := _ }, ?_, hst⟩
    unfold Gen.find_king
    simp only
    refine ExS.seq hset3 (ExS.seq_ret (ExS.seq (s1 := s3) ?_ ?_))
    · refine ExS.ite (bc := true) (EvE_of_eval (ev_lt81 s1 kc hkc h13))
        (by simp [boolVal, truthy, hkcq, sq.isLt]) ?_
      simp only [ite_true]
      exact ExS.seq hc2 (ExS.set hland)
    · refine ExS.ite (vc := boolVal true) (bc := true)
        (EvE_of_eval (n := 2) (by simp [evalExpr, s3, Locals.upd])) (by rfl) ?_
      simp only [ite_true]
      have hm3 : s3.mem = m := rfl
      refine ExS.seq (ExS.store (pa := .ptr ob 0) (v := .int IntTy.u8 sq.val)
        (EvE_of_eval (n := 2) (by simp [evalExpr, s3, s2, s1, s0, Locals.upd, h2]))
        (EvE_of_eval (n := 2) (by simp [evalExpr, s3, s2, Locals.upd, h13, hkcq])) rfl
        (by rw [hm3]; exact hst)) ?_
      exact ExS.ret (EvE_of_eval (ev_true8 _))
  | none =>
    intro hset3
    have hkc255 : kc = 255 := kingByte_none hks
    let sA : State := { s1 with locals := s1.locals.upd 5 (.int IntTy.i32 0) }
    have hite1 : ExS Gen.prog s1 (.ite (.bin .lt (some ⟨32, true⟩) (.cast ⟨32, true⟩ (.var 3))
        (.const (.int ⟨32, true⟩ 81))) (.seq (.call (some 4) 0 [(.var 1), (.cast ⟨32, false⟩
        (.const (.int ⟨32, true⟩ 8)))]) (.set 5 (.land (.const (.int ⟨32, true⟩ 1)) (.bin .eq
        (some ⟨32, true⟩) (.cast ⟨32, true⟩ (.load (.int ⟨8, false⟩) (.index (.field (.var 0) 0)
        (.var 3) 1))) (.cast ⟨32, true⟩ (.var 4)))))) (.set 5 (.const (.int ⟨32, true⟩ 0))))
        .normal sA := by
      refine ExS.ite (bc := false) (EvE_of_eval (ev_lt81 s1 kc hkc h13))
        (by simp [boolVal, truthy, hkc255]) ?_
      exact ExS.set (EvE.const _)
    have hite2 : ExS Gen.prog sA (.ite (.var 5) (.seq (.store (.int ⟨8, false⟩) (.var 2) (.var 3))
        (.ret (some (.cast ⟨8, false⟩ (.bin .ne (some ⟨32, true⟩) (.const (.int ⟨32, true⟩ 1))
        (.const (.int ⟨32, true⟩ 0))))))) .skip) .normal sA :=
      ExS.ite (vc := .int IntTy.i32 0) (bc := false)
        (EvE_of_eval (n := 2) (by simp [evalExpr, sA, Locals.upd])) (by rfl) ExS.skip
    have hc7 := hcall sA 7 (by simp [sA, s1, s0, Locals.upd, h1])
    let sB : State := { sA with mem := sA.mem, locals := sA.locals.upd 7 (.int IntTy.u8 (kb c)) }
    let sC : State := { sB with locals := sB.locals.upd 6 (.int IntTy.u8 (kb c)) }
    have hset6 : ExS Gen.prog sB (.set 6 (.var 7)) .normal sC :=
      ExS.set (EvE_of_eval (n := 2) (by simp [evalExpr, sB, Locals.upd]))
    let sD : State := { sC with locals := sC.locals.upd 8 (.int IntTy.u8 0) }
    have hset8 : ExS Gen.prog sC (.set 8 (.cast ⟨8, false⟩ (.const (.int ⟨32, true⟩ 0)))) .normal sD :=
      ExS.set (EvE_of_eval (n := 3) (by simp [evalExpr, evalCast, IntTy.wrap, IntTy.modulus, IntTy.toInt, Res.bind, IntTy.u8]))
    have hloop := find_king_loop p (kb c) ob hkb 81 0 sD (by omega)
      (by simp [sD, sC, sB, sA, s1, s0, Locals.upd, h0])
      (by simp [sD, sC, sB, sA, s1, s0, Locals.upd, h2])
      (by simp [sD, sC, Locals.upd]) (by simp [sD, Locals.upd]) hm rfl ⟨blk, hob, hl⟩
    rw [firstFrom_kingSquare, hks] at hloop
    obtain ⟨s', hs', hmem⟩ := hloop
    refine ⟨s', ?_, hmem⟩
    unfold Gen.find_king
    exact ExS.seq hset3 (ExS.seq (ExS.seq hite1 hite2) (ExS.seq (ExS.seq hc7 hset6)
      (ExS.seq (ExS.seq hset8 hs') (ExS.ret (EvE_of_eval (n := 5) rfl)))))
end Shogi.C.Proofs
