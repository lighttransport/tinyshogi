/-
  T1: SFEN round trip. `parse_print`: printing a well-formed position and
  parsing it back gives the same position; `parse_print_reachable` for every
  reachable position.
-/
import Shogi.Sfen
import Shogi.Theorems
namespace Shogi.Sfen

theorem digitChar_props : ∀ d : Fin 10,
    isDigit (digitChar d) = true ∧ digitVal (digitChar d) = d ∧ isSpace (digitChar d) = false ∧
    digitChar d ≠ '/' ∧ digitChar d ≠ '+' ∧ digitChar d ≠ '-' := by decide

theorem digitChar_isDigit {d : Nat} (h : d < 10) : isDigit (digitChar d) = true :=
  (digitChar_props ⟨d, h⟩).1
theorem digitChar_val {d : Nat} (h : d < 10) : digitVal (digitChar d) = d :=
  (digitChar_props ⟨d, h⟩).2.1
theorem digitChar_space {d : Nat} (h : d < 10) : isSpace (digitChar d) = false :=
  (digitChar_props ⟨d, h⟩).2.2.1

theorem digitsVal_append (xs : List Char) (c : Char) (acc : Nat) :
    digitsVal (xs ++ [c]) acc = digitsVal xs acc * 10 + digitVal c := by
  induction xs generalizing acc with
  | nil => rfl
  | cons x xs ih => exact ih _

theorem natDigits_spec : ∀ (f n : Nat), n < 10 ^ (f + 1) →
    natDigits (f + 1) n ≠ [] ∧ (natDigits (f + 1) n).all isDigit = true ∧
    digitsVal (natDigits (f + 1) n) 0 = n := by
  intro f
  induction f with
  | zero =>
    intro n h
    have h10 : n < 10 := by simpa using h
    simp [natDigits, h10, digitChar_isDigit h10, digitsVal, digitChar_val h10]
  | succ f ih =>
    intro n h
    unfold natDigits
    split
    · rename_i h10
      simp [digitChar_isDigit h10, digitsVal, digitChar_val h10]
    · rename_i h10
      have hlt : n / 10 < 10 ^ (f + 1) := by
        rw [Nat.pow_succ] at h; omega
      obtain ⟨_, hd, hv⟩ := ih (n / 10) hlt
      have hm : n % 10 < 10 := Nat.mod_lt _ (by decide)
      refine ⟨by simp, ?_, ?_⟩
      · simp [List.all_append, hd, digitChar_isDigit hm]
      · rw [digitsVal_append, hv, digitChar_val hm]; omega

theorem natDigits_length : ∀ (f k n : Nat), 0 < k → n < 10 ^ k → (natDigits f n).length ≤ k := by
  intro f
  induction f with
  | zero => intro k n _ _; simp [natDigits]
  | succ f ih =>
    intro k n hk h
    unfold natDigits
    split
    · simp; omega
    · rename_i h10
      obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
      have hk' : 0 < k' := by
        rcases Nat.eq_zero_or_pos k' with e | e
        · subst e; simp at h; omega
        · exact e
      have := ih k' (n / 10) hk' (by rw [Nat.pow_succ] at h; omega)
      simp; omega

theorem showNat_spec {n : Nat} (h : n ≤ ulongMax) :
    showNat n ≠ [] ∧ (showNat n).all isDigit = true ∧ digitsVal (showNat n) 0 = n :=
  natDigits_spec 19 n (by unfold ulongMax at h; omega)

theorem showNat_length {n : Nat} (h : n ≤ uintMax) : (showNat n).length ≤ 10 :=
  natDigits_length 20 10 n (by decide) (by unfold uintMax at h; omega)

theorem showNat_length18 {n : Nat} (h : n ≤ 18) : (showNat n).length ≤ 2 :=
  natDigits_length 20 2 n (by decide) (by omega)

theorem uintMax_le : uintMax ≤ ulongMax := by decide

theorem parseMoveNumber_showNat {n : Nat} (h1 : 1 ≤ n) (h2 : n ≤ uintMax) :
    parseMoveNumber (showNat n) = some n := by
  obtain ⟨hne, hd, hv⟩ := showNat_spec (Nat.le_trans h2 uintMax_le)
  have hhead : ∀ c r, showNat n = c :: r → c ≠ '+' ∧ c ≠ '-' := by
    intro c r e
    rw [e] at hd
    simp only [List.all_cons, Bool.and_eq_true] at hd
    constructor <;> (intro hc; subst hc; simp [isDigit] at hd)
  have hle : n ≤ ulongMax := Nat.le_trans h2 uintMax_le
  have key : strtoulField (showNat n) = some n := by
    have hs : signSplit (showNat n) = (false, showNat n) := by
      cases e : showNat n with
      | nil => exact absurd e hne
      | cons c r =>
        obtain ⟨hp, hm⟩ := hhead c r e
        unfold signSplit
        split
        · rename_i heq; simp at heq; exact absurd heq.1 hp
        · rename_i heq; simp at heq; exact absurd heq.1 hm
        · rfl
    unfold strtoulField
    rw [hs]
    have hne' : (showNat n).isEmpty = false := by simpa using hne
    simp only [hne', hd, hv, Bool.not_true, Bool.or_false, Bool.false_eq_true, ite_false]
    rw [if_neg (by omega)]
  unfold parseMoveNumber
  rw [key]
  simp only
  rw [if_neg (by simp; omega)]

/-! ## Tokenizing printed output -/

theorem tokens_noSpace (xs r cur : List Char) (h : xs.all (fun c => !isSpace c) = true) :
    tokens (xs ++ r) cur = tokens r (xs.reverse ++ cur) := by
  induction xs generalizing cur with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.all_cons, Bool.and_eq_true, Bool.not_eq_true'] at h
    simp only [List.cons_append, tokens, h.1, if_false, Bool.false_eq_true]
    rw [ih _ h.2]
    simp

theorem tokens_field (xs r : List Char) (h : xs.all (fun c => !isSpace c) = true)
    (hne : xs ≠ []) : tokens (xs ++ ' ' :: r) [] = xs :: tokens r [] := by
  rw [tokens_noSpace xs _ [] h]
  simp only [tokens, isSpace, beq_self_eq_true, Bool.true_or, if_true, List.append_nil]
  have : xs.reverse.isEmpty = false := by simpa using hne
  simp [this]

theorem tokens_last (xs : List Char) (h : xs.all (fun c => !isSpace c) = true)
    (hne : xs ≠ []) : tokens xs [] = [xs] := by
  have := tokens_noSpace xs [] [] h
  simp only [List.append_nil] at this
  rw [this]
  simp [tokens, hne]

/-! ## Pieces and board rows -/

def caseLetter (pc : Piece) : Char :=
  if pc.color == .black then toUpper pc.type.letter else pc.type.letter

theorem pieceChars_eq (pc : Piece) :
    pieceChars pc = (if pc.type.isPromoted then ['+'] else []) ++ [caseLetter pc] := rfl

/-- Facts about the letter of every piece, by finite case analysis. -/
theorem letter_facts (c : Color) (t : PieceType) :
    let l := caseLetter ⟨c, t⟩
    (if isUpper l then Color.black else Color.white) = c ∧
    PieceType.ofLetter (toLower l) = some t.unpromote ∧
    (t.isPromoted = true → t.unpromote.canPromote = true ∧ t.unpromote.promote = t) ∧
    (t.isPromoted = false → t.unpromote = t) ∧
    l ≠ '/' ∧ l ≠ '+' ∧ isDigit l = false ∧ isSpace l = false := by
  cases c <;> cases t <;> decide

/-- Squares `k, k+1, …` set to the pieces of `xs` (empty entries leave the board). -/
def fillRow : List (Option Piece) → Nat → List (Option Piece) → List (Option Piece)
  | b, _, [] => b
  | b, k, none :: r => fillRow b (k + 1) r
  | b, k, some pc :: r => fillRow (b.set k (some pc)) (k + 1) r

theorem parseBoard_append_digit (e : Nat) (rest : List Char) (st : BoardSt)
    (he1 : 1 ≤ e) (he9 : e ≤ 9) (hp : st.promoted = false) (hc : st.col + e ≤ 9) :
    parseBoard (digitChar e :: rest) st = parseBoard rest ⟨st.row, st.col + e, st.promoted, st.board⟩ := by
  have hd := digitChar_isDigit (show e < 10 by omega)
  have hv := digitChar_val (show e < 10 by omega)
  have h1 : (digitChar e == '/') = false := by
    have := (digitChar_props ⟨e, by omega⟩).2.2.2.1; simpa using this
  have h2 : (digitChar e == '+') = false := by
    have := (digitChar_props ⟨e, by omega⟩).2.2.2.2.1; simpa using this
  simp only [parseBoard, h1, h2, hd, hv, hp, Bool.false_eq_true, ite_false, ite_true]
  rw [if_neg (by simp; omega)]

theorem parseBoard_piece (pc : Piece) (rest : List Char) (st : BoardSt)
    (hp : st.promoted = false) (hr : st.row < 9) (hc : st.col < 9) :
    parseBoard (pieceChars pc ++ rest) st =
      parseBoard rest ⟨st.row, st.col + 1, false, st.board.set (st.row * 9 + st.col) (some pc)⟩ := by
  obtain ⟨c, t⟩ := pc
  obtain ⟨hcol, hlet, hpro, hnp, hsl, hpl, hdig, _⟩ := letter_facts c t
  rw [pieceChars_eq]
  have hsl' : (caseLetter ⟨c, t⟩ == '/') = false := by simpa using hsl
  have hpl' : (caseLetter ⟨c, t⟩ == '+') = false := by simpa using hpl
  have hr' : ¬ (st.row ≥ 9 || st.col ≥ 9) = true := by simp; omega
  cases hpt : t.isPromoted
  · simp only [hpt, Bool.false_eq_true, ite_false, List.nil_append, List.cons_append,
      parseBoard, hsl', hpl', hdig, hlet, hp, hcol, Bool.not_false, Bool.false_and]
    simp only [hr', ite_false, Bool.false_eq_true]
    rw [hnp hpt]
  · obtain ⟨hcp, hpp⟩ := hpro hpt
    simp only [hpt, ite_true, List.cons_append, List.singleton_append, parseBoard,
      hsl', hpl', hdig, hlet, hp, hcol, Bool.false_eq_true, ite_false, beq_self_eq_true,
      Bool.false_or]
    have e1 : ('+' == '/') = false := by decide
    rw [if_neg (by simp [e1])]
    rw [if_neg (by simp; omega)]
    simp only [List.nil_append, List.cons_append, parseBoard, hsl', hpl', hdig, hlet, hcol,
      Bool.false_eq_true, ite_false]
    simp only [hr', ite_false, hcp, Bool.not_true, Bool.and_false, Bool.false_eq_true,
      ite_true, hpp]

theorem parse_row : ∀ (xs : List (Option Piece)) (e : Nat) (rest : List Char) (r c : Nat)
    (B : List (Option Piece)), r < 9 → c + e + xs.length ≤ 9 → e ≤ 9 →
    parseBoard (rowChars xs e ++ rest) ⟨r, c, false, B⟩ =
      parseBoard rest ⟨r, c + e + xs.length, false, fillRow B (r * 9 + c + e) xs⟩ := by
  intro xs
  induction xs with
  | nil =>
    intro e rest r c B hr hc he
    by_cases h0 : e = 0
    · subst h0; simp [rowChars, fillRow]
    · simp only [rowChars, show e > 0 by omega, ite_true, List.cons_append, List.nil_append,
        List.length_nil, Nat.add_zero, fillRow]
      exact parseBoard_append_digit e rest _ (by omega) he rfl (by simp; omega)
  | cons x xs ih =>
    intro e rest r c B hr hc he
    simp only [List.length_cons] at hc
    cases x with
    | none =>
      simp only [rowChars, fillRow]
      rw [ih (e + 1) rest r c B hr (by omega) (by omega)]
      simp only [List.length_cons]
      congr 2 <;> omega
    | some pc =>
      simp only [rowChars, fillRow, List.append_assoc]
      have step1 : parseBoard ((if e > 0 then [digitChar e] else []) ++
          (pieceChars pc ++ (rowChars xs 0 ++ rest))) ⟨r, c, false, B⟩ =
          parseBoard (pieceChars pc ++ (rowChars xs 0 ++ rest)) ⟨r, c + e, false, B⟩ := by
        by_cases h0 : e = 0
        · subst h0; simp
        · simp only [show e > 0 by omega, ite_true, List.cons_append, List.nil_append]
          exact parseBoard_append_digit e _ _ (by omega) he rfl (by simp; omega)
      rw [step1, parseBoard_piece pc _ _ rfl hr (by simp; omega)]
      simp only
      rw [ih 0 rest r (c + e + 1) _ hr (by omega) (by omega)]
      simp only [List.length_cons]
      congr 2
      · omega
      · rw [show r * 9 + (c + e + 1) + 0 = r * 9 + c + e + 1 by omega, Nat.add_assoc (r * 9) c e]

theorem fillRow_append : ∀ (xs ys : List (Option Piece)) (B : List (Option Piece)) (k : Nat),
    fillRow B k (xs ++ ys) = fillRow (fillRow B k xs) (k + xs.length) ys := by
  intro xs
  induction xs with
  | nil => intro ys B k; rfl
  | cons x xs ih =>
    intro ys B k
    cases x with
    | none => simp only [List.cons_append, fillRow, ih, List.length_cons]; congr 1; omega
    | some pc => simp only [List.cons_append, fillRow, ih, List.length_cons]; congr 1; omega

theorem fillRow_fresh : ∀ (xs pre : List (Option Piece)),
    fillRow (pre ++ List.replicate xs.length none) pre.length xs = pre ++ xs := by
  intro xs
  induction xs with
  | nil => intro pre; simp [fillRow]
  | cons x xs ih =>
    intro pre
    have e : pre ++ List.replicate (xs.length + 1) none = (pre ++ [none]) ++ List.replicate xs.length none := by
      simp [List.replicate_succ]
    cases x with
    | none =>
      simp only [fillRow, List.length_cons, e]
      have := ih (pre ++ [none])
      simp only [List.length_append, List.length_singleton] at this
      rw [this]; simp
    | some pc =>
      simp only [fillRow, List.length_cons, e]
      have hs : ((pre ++ [none]) ++ List.replicate xs.length none).set pre.length (some pc) =
          (pre ++ [some pc]) ++ List.replicate xs.length none := by
        simp [List.set_append_left, List.set_append_right]
      rw [hs]
      have := ih (pre ++ [some pc])
      simp only [List.length_append, List.length_singleton] at this
      rw [this]; simp

theorem boardRow_length {b : List (Option Piece)} (hb : b.length = 81) {r : Nat} (hr : r < 9) :
    (boardRow b r).length = 9 := by
  simp [boardRow, hb]; omega

theorem parse_rows (b : List (Option Piece)) (hb : b.length = 81) : ∀ (k r : Nat)
    (B : List (Option Piece)), r + k = 9 → 1 ≤ k →
    parseBoard (rowsChars b r k) ⟨r, 0, false, B⟩ =
      some (fillRow B (r * 9) ((b.drop (r * 9)).take (9 * k))) := by
  intro k
  induction k using Nat.strongRecOn with
  | ind k ih =>
    intro r B hrk hk
    match k, ih with
    | 0, _ => omega
    | 1, _ =>
      have hr : r = 8 := by omega
      subst hr
      have := parse_row (boardRow b 8) 0 [] 8 0 B (by decide)
        (by rw [boardRow_length hb (by decide)]; decide) (by decide)
      simp only [List.append_nil] at this
      simp only [rowsChars, this, boardRow_length hb (by decide : 8 < 9)]
      simp [parseBoard, boardRow]
    | j + 2, ih =>
      have hr : r < 9 := by omega
      simp only [rowsChars]
      rw [parse_row (boardRow b r) 0 _ r 0 B hr (by rw [boardRow_length hb hr]; decide) (by decide)]
      rw [boardRow_length hb hr]
      have hsl : ('/' : Char) = '/' := rfl
      simp only [parseBoard, beq_self_eq_true, ite_true, Nat.zero_add, Nat.add_zero]
      rw [if_neg (by simp; omega)]
      rw [ih (j + 1) (by omega) (r + 1) _ (by omega) (by omega)]
      congr 1
      have split : (b.drop (r * 9)).take (9 * (j + 2)) =
          boardRow b r ++ (b.drop ((r + 1) * 9)).take (9 * (j + 1)) := by
        rw [show 9 * (j + 2) = 9 + 9 * (j + 1) by omega, List.take_add, List.drop_drop]
        simp only [boardRow]
        congr 3; omega
      rw [split, fillRow_append, boardRow_length hb hr]
      congr 1; omega

/-- **Board round trip.** -/
theorem parseBoard_boardChars (b : List (Option Piece)) (hb : b.length = 81) :
    parseBoard (boardChars b) ⟨0, 0, false, Position.emptyBoard⟩ = some b := by
  unfold boardChars
  rw [parse_rows b hb 9 0 _ (by decide) (by decide)]
  have := fillRow_fresh b []
  simp only [List.nil_append, List.length_nil, hb] at this
  simp only [Nat.zero_mul, List.drop_zero, Position.emptyBoard]
  rw [show 9 * 9 = 81 by rfl, List.take_of_length_le (by omega), this]

/-! ## Hands -/

def handLetterC (c : Color) (i : Fin 7) : Char :=
  if c == .black then toUpper (PieceType.ofHandIndex i).letter else (PieceType.ofHandIndex i).letter

/-- One printed hand entry. -/
def entry (c : Color) (i : Fin 7) (n : Nat) : List Char :=
  if n == 0 then [] else (if n > 1 then showNat n else []) ++ [handLetterC c i]

theorem handLetter_facts (c : Color) : ∀ i : Fin 7,
    let l := handLetterC c i
    isDigit l = false ∧ (if isUpper l then Color.black else Color.white) = c ∧
    handLetter? (toLower l) = some (PieceType.ofHandIndex i) ∧ l ≠ '-' ∧ isSpace l = false := by
  cases c <;> decide

theorem digitsVal_ge : ∀ (ds : List Char) (acc : Nat), acc ≤ digitsVal ds acc := by
  intro ds
  induction ds with
  | nil => intro acc; exact Nat.le_refl _
  | cons d ds ih => intro acc; exact Nat.le_trans (by omega) (ih _)

theorem handsGo_digits : ∀ (ds cs : List Char) (pend : Option Nat) (h : Hands),
    ds ≠ [] → ds.all isDigit = true → digitsVal ds (pend.getD 0) ≤ 18 →
    handsGo (ds ++ cs) pend h = handsGo cs (some (digitsVal ds (pend.getD 0))) h := by
  intro ds
  induction ds with
  | nil => intro _ _ _ hne; exact absurd rfl hne
  | cons d ds ih =>
    intro cs pend h _ hd hv
    simp only [List.all_cons, Bool.and_eq_true] at hd
    have hge := digitsVal_ge ds (pend.getD 0 * 10 + digitVal d)
    simp only [digitsVal] at hv
    simp only [List.cons_append, handsGo, hd.1, ite_true]
    rw [if_neg (by omega)]
    by_cases hds : ds = []
    · subst hds; simp [digitsVal]
    · rw [ih cs _ h hds hd.2 (by simpa using hv)]
      simp [digitsVal]

theorem handsGo_entry {c : Color} {i : Fin 7} {n : Nat} (rest : List Char) (h : Hands)
    (hn1 : 1 ≤ n) (hn : n ≤ 18) (h0 : h.get c i = 0) :
    handsGo (entry c i n ++ rest) none h = handsGo rest none (h.set c i n) := by
  obtain ⟨hdig, hcol, hlet, _, _⟩ := handLetter_facts c i
  have hidx := PieceType.handIndex_ofHandIndex i
  unfold entry
  rw [if_neg (by simp; omega)]
  by_cases h1 : n = 1
  · subst h1
    simp only [show ¬ (1 > 1) by omega, ite_false, List.nil_append, List.singleton_append,
      handsGo, hdig, Bool.false_eq_true, hcol, hlet, hidx, h0, Nat.zero_add]
    rw [if_neg (by omega)]
  · have hgt : n > 1 := by omega
    obtain ⟨hne, hd, hv⟩ := showNat_spec (n := n) (by unfold ulongMax; omega)
    simp only [hgt, ite_true, List.append_assoc, List.singleton_append]
    rw [handsGo_digits _ _ none h hne hd (by simpa [hv] using hn)]
    simp only [Option.getD_none, hv, handsGo, hdig, Bool.false_eq_true, ite_false, hcol, hlet,
      hidx, h0, Nat.zero_add]
    obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
    simp only
    rw [if_neg (by omega)]

def slots : List (Color × Fin 7) := handOrder.map (Color.black, ·) ++ handOrder.map (Color.white, ·)

theorem slots_nodup : slots.Nodup := by decide

theorem slots_complete (c : Color) (j : Fin 7) : (c, j) ∈ slots := by
  revert j; cases c <;> decide

def applyEntries (p : Position) (L : List (Color × Fin 7)) (h : Hands) : Hands :=
  L.foldl (fun h x => if p.hand x.1 x.2 = 0 then h else h.set x.1 x.2 (p.hand x.1 x.2)) h

theorem handsChars_eq (p : Position) :
    handsChars p =
      let hs := slots.flatMap fun x => entry x.1 x.2 (p.hand x.1 x.2)
      if hs.isEmpty then ['-'] else hs := by
  simp only [handsChars, handChars, slots, List.flatMap_append, List.flatMap_map]
  rfl

theorem Hands.set_lens {h : Hands} (hb : h.black.length = 7) (hw : h.white.length = 7)
    (c : Color) (i : Fin 7) (n : Nat) :
    (h.set c i n).black.length = 7 ∧ (h.set c i n).white.length = 7 := by
  cases c <;> simp [Hands.set, hb, hw]

theorem parse_entries (p : Position) : ∀ (L : List (Color × Fin 7)) (h : Hands) (rest : List Char),
    L.Nodup → (∀ x ∈ L, h.get x.1 x.2 = 0) → (∀ x ∈ L, p.hand x.1 x.2 ≤ 18) →
    h.black.length = 7 → h.white.length = 7 →
    handsGo ((L.flatMap fun x => entry x.1 x.2 (p.hand x.1 x.2)) ++ rest) none h =
      handsGo rest none (applyEntries p L h) := by
  intro L
  induction L with
  | nil => intro h rest _ _ _ _ _; rfl
  | cons x L ih =>
    intro h rest hnd h0 h18 hb hw
    simp only [List.nodup_cons] at hnd
    simp only [List.flatMap_cons, List.append_assoc, applyEntries, List.foldl_cons]
    by_cases hz : p.hand x.1 x.2 = 0
    · simp only [hz, ite_true]
      have : entry x.1 x.2 0 = [] := rfl
      rw [this, List.nil_append]
      exact ih h rest hnd.2 (fun y hy => h0 y (List.mem_cons_of_mem _ hy))
        (fun y hy => h18 y (List.mem_cons_of_mem _ hy)) hb hw
    · simp only [hz, ite_false]
      rw [handsGo_entry _ h (by omega) (h18 x (List.mem_cons_self ..)) (h0 x (List.mem_cons_self ..))]
      obtain ⟨hb', hw'⟩ := Hands.set_lens hb hw x.1 x.2 (p.hand x.1 x.2)
      apply ih _ rest hnd.2 _ (fun y hy => h18 y (List.mem_cons_of_mem _ hy)) hb' hw'
      intro y hy
      rw [Position.Hands.get_set_len hb hw]
      have hne : y ≠ x := fun e => hnd.1 (e ▸ hy)
      have : ¬ (x.1 = y.1 ∧ x.2 = y.2) := fun ⟨a, b⟩ => hne (Prod.ext a.symm b.symm)
      rw [if_neg this]
      exact h0 y (List.mem_cons_of_mem _ hy)

theorem applyEntries_get (p : Position) : ∀ (L : List (Color × Fin 7)) (h : Hands) (y : Color × Fin 7),
    L.Nodup → h.black.length = 7 → h.white.length = 7 →
    (applyEntries p L h).get y.1 y.2 =
      if y ∈ L ∧ p.hand y.1 y.2 ≠ 0 then p.hand y.1 y.2 else h.get y.1 y.2 := by
  intro L
  induction L with
  | nil => intro h y _ _ _; simp [applyEntries]
  | cons x L ih =>
    intro h y hnd hb hw
    simp only [List.nodup_cons] at hnd
    simp only [applyEntries, List.foldl_cons]
    by_cases hz : p.hand x.1 x.2 = 0
    · simp only [hz, ite_true]
      rw [show List.foldl _ h L = applyEntries p L h from rfl, ih h y hnd.2 hb hw]
      by_cases hyx : y = x
      · subst hyx; simp [hz]
      · simp [hyx]
    · simp only [hz, ite_false]
      obtain ⟨hb', hw'⟩ := Hands.set_lens hb hw x.1 x.2 (p.hand x.1 x.2)
      rw [show List.foldl _ _ L = applyEntries p L _ from rfl, ih _ y hnd.2 hb' hw',
        Position.Hands.get_set_len hb hw]
      by_cases hyx : y = x
      · subst hyx; simp [hnd.1, hz]
      · have : ¬ (x.1 = y.1 ∧ x.2 = y.2) := fun ⟨a, b⟩ => hyx (Prod.ext a.symm b.symm)
        simp [hyx, this]

theorem Hands.ext' {a b : Hands} (ha : a.black.length = 7 ∧ a.white.length = 7)
    (hb : b.black.length = 7 ∧ b.white.length = 7) (h : ∀ c j, a.get c j = b.get c j) : a = b := by
  obtain ⟨ab, aw⟩ := a
  obtain ⟨bb, bw⟩ := b
  simp only at ha hb
  have e1 : ab = bb := by
    apply List.ext_getElem (by omega)
    intro n h1 h2
    have := h .black ⟨n, by omega⟩
    simp [Hands.get, List.getD, h1, h2] at this
    exact this
  have e2 : aw = bw := by
    apply List.ext_getElem (by omega)
    intro n h1 h2
    have := h .white ⟨n, by omega⟩
    simp [Hands.get, List.getD, h1, h2] at this
    exact this
  rw [e1, e2]

/-- **Hands round trip.** -/
theorem parseHands_handsChars (p : Position) (hb : p.hands.black.length = 7)
    (hw : p.hands.white.length = 7) (h18 : ∀ c i, p.hand c i ≤ 18) :
    parseHands (handsChars p) = some p.hands := by
  have hemp : Hands.empty.black.length = 7 ∧ Hands.empty.white.length = 7 := by decide
  have hget0 : ∀ c j, Hands.empty.get c j = 0 := by intro c j; cases c <;> revert j <;> decide
  rw [handsChars_eq]
  simp only
  split
  · rename_i hemptyhs
    simp only [parseHands, beq_self_eq_true, ite_true, Option.some.injEq]
    apply Hands.ext' hemp ⟨hb, hw⟩
    intro c j
    rw [hget0]
    by_cases hz : p.hand c j = 0
    · exact hz.symm
    · exfalso
      have hmem : entry c j (p.hand c j) ≠ [] := by
        unfold entry; rw [if_neg (by simp; omega)]; simp
      apply hmem
      have := List.isEmpty_iff.mp hemptyhs
      rw [List.flatMap_eq_nil_iff] at this
      exact this (c, j) (slots_complete c j)
  · rename_i hne
    have hnotdash : ((slots.flatMap fun x => entry x.1 x.2 (p.hand x.1 x.2)) == ['-']) = false := by
      rw [beq_eq_false_iff_ne]
      intro e
      have hmem : '-' ∈ slots.flatMap fun x => entry x.1 x.2 (p.hand x.1 x.2) := by rw [e]; simp
      rw [List.mem_flatMap] at hmem
      obtain ⟨x, _, hx⟩ := hmem
      unfold entry at hx
      split at hx
      · simp at hx
      · simp only [List.mem_append, List.mem_singleton] at hx
        rcases hx with hx | hx
        · split at hx
          · obtain ⟨_, hd, _⟩ := showNat_spec (n := p.hand x.1 x.2)
              (by have := h18 x.1 x.2; unfold ulongMax; omega)
            have := List.all_eq_true.mp hd '-' hx
            simp [isDigit] at this
          · simp at hx
        · exact (handLetter_facts x.1 x.2).2.2.2.1 hx.symm
    simp only [parseHands, hnotdash, Bool.false_eq_true, ite_false]
    have := parse_entries p slots Hands.empty [] slots_nodup (fun x _ => hget0 x.1 x.2)
      (fun x _ => h18 x.1 x.2) hemp.1 hemp.2
    simp only [List.append_nil] at this
    rw [this]
    simp only [handsGo, Option.some.injEq]
    have hlen : ∀ (L : List (Color × Fin 7)) (h : Hands), h.black.length = 7 → h.white.length = 7 →
        (applyEntries p L h).black.length = 7 ∧ (applyEntries p L h).white.length = 7 := by
      intro L
      induction L with
      | nil => intro h a b; exact ⟨a, b⟩
      | cons x L ih =>
        intro h a b
        simp only [applyEntries, List.foldl_cons]
        split
        · exact ih h a b
        · obtain ⟨a', b'⟩ := Hands.set_lens a b x.1 x.2 (p.hand x.1 x.2)
          exact ih _ a' b'
    apply Hands.ext' (hlen slots _ hemp.1 hemp.2) ⟨hb, hw⟩
    intro c j
    have := applyEntries_get p slots Hands.empty (c, j) slots_nodup hemp.1 hemp.2
    simp only at this
    rw [this, hget0]
    by_cases hz : p.hand c j = 0
    · simp [hz]; exact hz.symm
    · simp [hz, slots_complete c j]; rfl

/-! ## Alphabet, field shape and size -/

/-- Every character `print` emits, apart from the field separator. -/
def alphabet : List Char := "0123456789+/-bwplnsgrkPLNSGBRK".toList

theorem alphabet_facts : ∀ c ∈ alphabet, isSpace c = false ∧ c.utf8Size = 1 := by decide

theorem digitChar_mem (d : Nat) : digitChar d ∈ alphabet := by
  match d with
  | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 => decide
  | _ + 9 => simp only [digitChar]; decide

theorem caseLetter_mem (pc : Piece) : caseLetter pc ∈ alphabet := by
  obtain ⟨c, t⟩ := pc; cases c <;> cases t <;> decide

theorem handLetterC_mem (c : Color) (i : Fin 7) : handLetterC c i ∈ alphabet := by
  cases c <;> revert i <;> decide

def InAlpha (l : List Char) : Prop := ∀ c ∈ l, c ∈ alphabet

theorem natDigits_alpha : ∀ f n, InAlpha (natDigits f n) := by
  intro f
  induction f with
  | zero => intro n c h; simp [natDigits] at h
  | succ f ih =>
    intro n c h
    unfold natDigits at h
    split at h
    · simp at h; subst h; exact digitChar_mem _
    · simp only [List.mem_append, List.mem_singleton] at h
      rcases h with h | h
      · exact ih _ c h
      · subst h; exact digitChar_mem _

theorem rowChars_alpha : ∀ xs e, InAlpha (rowChars xs e) := by
  intro xs
  induction xs with
  | nil => intro e c h; simp only [rowChars] at h; split at h <;> simp_all [digitChar_mem]
  | cons x xs ih =>
    intro e c h
    cases x with
    | none => exact ih _ c h
    | some pc =>
      simp only [rowChars, List.mem_append] at h
      rcases h with (h | h) | h
      · split at h <;> simp_all [digitChar_mem]
      · rw [pieceChars_eq] at h
        simp only [List.mem_append, List.mem_singleton] at h
        rcases h with h | h
        · split at h <;> simp_all; decide
        · subst h; exact caseLetter_mem _
      · exact ih _ c h

theorem rowsChars_alpha (b : List (Option Piece)) : ∀ k r, InAlpha (rowsChars b r k) := by
  intro k
  induction k using Nat.strongRecOn with
  | ind k ih =>
    intro r c h
    match k, ih with
    | 0, _ => simp [rowsChars] at h
    | 1, _ => exact rowChars_alpha _ _ c h
    | j + 2, ih =>
      simp only [rowsChars, List.mem_append, List.mem_cons] at h
      rcases h with h | h | h
      · exact rowChars_alpha _ _ c h
      · subst h; decide
      · exact ih (j + 1) (by omega) _ c h

theorem entry_alpha (c : Color) (i : Fin 7) (n : Nat) : InAlpha (entry c i n) := by
  intro x h
  unfold entry at h
  split at h
  · simp at h
  · simp only [List.mem_append, List.mem_singleton] at h
    rcases h with h | h
    · split at h
      · exact natDigits_alpha _ _ x h
      · simp at h
    · subst h; exact handLetterC_mem _ _

theorem handsChars_alpha (p : Position) : InAlpha (handsChars p) := by
  rw [handsChars_eq]
  intro x h
  simp only at h
  split at h
  · simp at h; subst h; decide
  · rw [List.mem_flatMap] at h
    obtain ⟨y, _, hy⟩ := h
    exact entry_alpha _ _ _ x hy

theorem noSpace_of_alpha {l : List Char} (h : InAlpha l) : l.all (fun c => !isSpace c) = true := by
  rw [List.all_eq_true]
  intro c hc
  simp [(alphabet_facts c (h c hc)).1]

/-! Lengths -/

theorem rowChars_length : ∀ xs e, (rowChars xs e).length ≤ 3 * xs.length + 1 := by
  intro xs
  induction xs with
  | nil => intro e; simp only [rowChars]; split <;> simp
  | cons x xs ih =>
    intro e
    cases x with
    | none => have := ih (e + 1); simp only [rowChars, List.length_cons]; omega
    | some pc =>
      have := ih 0
      simp only [rowChars, List.length_append, List.length_cons, pieceChars_eq]
      split <;> split <;> simp <;> omega

theorem rowsChars_length (b : List (Option Piece)) : ∀ k r, (rowsChars b r k).length ≤ 29 * k := by
  intro k
  induction k using Nat.strongRecOn with
  | ind k ih =>
    intro r
    have hrow : (boardRow b r).length ≤ 9 := by simp only [boardRow, List.length_take]; omega
    match k, ih with
    | 0, _ => simp [rowsChars]
    | 1, _ => have := rowChars_length (boardRow b r) 0; simp only [rowsChars]; omega
    | j + 2, ih =>
      have := rowChars_length (boardRow b r) 0
      have := ih (j + 1) (by omega) (r + 1)
      simp only [rowsChars, List.length_append, List.length_cons]
      omega

theorem entry_length {c : Color} {i : Fin 7} {n : Nat} (h : n ≤ 18) : (entry c i n).length ≤ 3 := by
  unfold entry
  split
  · simp
  · have := showNat_length18 h
    split <;> simp <;> omega

theorem flatMap_length_le {α} (L : List α) (f : α → List Char) (k : Nat)
    (h : ∀ x ∈ L, (f x).length ≤ k) : (L.flatMap f).length ≤ k * L.length := by
  induction L with
  | nil => simp
  | cons x L ih =>
    simp only [List.flatMap_cons, List.length_append, List.length_cons]
    have := h x (List.mem_cons_self ..)
    have := ih (fun y hy => h y (List.mem_cons_of_mem _ hy))
    rw [Nat.mul_succ]; omega

theorem handsChars_length (p : Position) (h18 : ∀ c i, p.hand c i ≤ 18) :
    (handsChars p).length ≤ 42 := by
  rw [handsChars_eq]
  simp only
  split
  · simp
  · have := flatMap_length_le slots (fun x => entry x.1 x.2 (p.hand x.1 x.2)) 3
      (fun x _ => entry_length (h18 x.1 x.2))
    have hl : slots.length = 14 := by decide
    omega

theorem utf8ByteSize_ofList_alpha : ∀ (l : List Char), InAlpha l →
    (String.ofList l).utf8ByteSize = l.length := by
  intro l
  induction l with
  | nil => intro _; rfl
  | cons c l ih =>
    intro h
    rw [show c :: l = [c] ++ l from rfl, String.ofList_append, String.utf8ByteSize_append,
      ih (fun x hx => h x (List.mem_cons_of_mem _ hx))]
    have hc := (alphabet_facts c (h c (List.mem_cons_self ..))).2
    have : (String.ofList [c]).utf8ByteSize = c.utf8Size := by
      rw [show String.ofList [c] = String.singleton c from rfl, String.utf8ByteSize_singleton]
    simp [this, hc]; omega

theorem utf8ByteSize_ofList_one : ∀ (l : List Char), (∀ c ∈ l, c.utf8Size = 1) →
    (String.ofList l).utf8ByteSize = l.length := by
  intro l
  induction l with
  | nil => intro _; rfl
  | cons c l ih =>
    intro h
    rw [show c :: l = [c] ++ l from rfl, String.ofList_append, String.utf8ByteSize_append,
      ih (fun x hx => h x (List.mem_cons_of_mem _ hx))]
    have hc := h c (List.mem_cons_self ..)
    rw [show String.ofList [c] = String.singleton c from rfl, String.utf8ByteSize_singleton, hc]
    simp; omega

theorem side_field (c : Color) :
    (if [if c == .black then 'b' else 'w'] == ['b'] then some Color.black
     else if [if c == .black then 'b' else 'w'] == ['w'] then some Color.white else none) = some c := by
  cases c <;> rfl

theorem boardChars_ne (b : List (Option Piece)) : boardChars b ≠ [] := by
  simp [boardChars, rowsChars]

theorem handsChars_ne (p : Position) : handsChars p ≠ [] := by
  rw [handsChars_eq]; simp only; split
  · simp
  · rename_i h; intro e; rw [e] at h; simp at h

theorem hand_le_18 {p : Position} (hm : p.materialOk = true) (c : Color) (i : Fin 7) :
    p.hand c i ≤ 18 := by
  have h := List.all_eq_true.mp hm i (List.mem_finRange i)
  simp only [decide_eq_true_eq] at h
  have hmax : PieceType.handMax i ≤ 18 := (by decide : ∀ j : Fin 7, PieceType.handMax j ≤ 18) i
  unfold Position.familyCount at h
  cases c <;> omega

/-- **SFEN round trip.** Printing a well-formed position and parsing it back
    gives the same position. Well-formed means: 81 squares and 7-slot hands,
    exactly one king per side, material within a full set (as
    `validate_material`), and a move number in `[1, UINT_MAX]`. Every
    reachable position satisfies the first three (`reachable_inv`,
    `reachable_kings`, `reachable_materialOk`). -/
theorem parse_print (p : Position) (hs : p.Shaped)
    (hk : p.kingCount .black = 1 ∧ p.kingCount .white = 1) (hm : p.materialOk = true)
    (hn : 1 ≤ p.moveNumber ∧ p.moveNumber ≤ uintMax) :
    parse (print p) = some p := by
  obtain ⟨hb, hhb, hhw⟩ := hs
  have h18 := hand_le_18 hm
  let sc : Char := if p.side == .black then 'b' else 'w'
  have hsc : sc ∈ alphabet := by
    show (if p.side == .black then 'b' else 'w') ∈ alphabet
    split <;> decide
  obtain ⟨hNne, hNd, _⟩ := showNat_spec (n := p.moveNumber) (by
    have := uintMax_le; omega)
  have hNalpha : InAlpha (showNat p.moveNumber) := natDigits_alpha _ _
  have hBalpha : InAlpha (boardChars p.board) := rowsChars_alpha p.board 9 0
  have hHalpha := handsChars_alpha p
  have hpc : printChars p = boardChars p.board ++ ' ' ::
      ([sc] ++ ' ' :: (handsChars p ++ ' ' :: showNat p.moveNumber)) := by
    simp [printChars, sc]
  -- size
  have hsize : (print p).utf8ByteSize < 512 := by
    have h1 : (boardChars p.board).length ≤ 261 := rowsChars_length p.board 9 0
    have h2 := handsChars_length p h18
    have h3 := showNat_length hn.2
    have hlen : (printChars p).length ≤ 317 := by
      rw [hpc]; simp only [List.length_append, List.length_cons, List.length_nil]; omega
    unfold print
    rw [utf8ByteSize_ofList_one]
    · omega
    · intro c hc
      rw [hpc] at hc
      simp only [List.mem_append, List.mem_cons] at hc
      rcases hc with hc | hc | hc | hc | hc | hc
      · exact (alphabet_facts c (hBalpha c hc)).2
      · rw [hc]; rfl
      · rcases hc with hc | hc
        · rw [hc]; exact (alphabet_facts _ hsc).2
        · simp at hc
      · rw [hc]; rfl
      · exact (alphabet_facts c (hHalpha c hc)).2
      · rcases hc with hc | hc
        · rw [hc]; rfl
        · exact (alphabet_facts c (hNalpha c hc)).2
  -- fields
  have hfields : fields (printChars p) =
      [boardChars p.board, [sc], handsChars p, showNat p.moveNumber] := by
    rw [hpc]
    unfold fields
    rw [tokens_field _ _ (noSpace_of_alpha hBalpha) (boardChars_ne _)]
    rw [show [sc] ++ ' ' :: (handsChars p ++ ' ' :: showNat p.moveNumber) =
        [sc] ++ ' ' :: (handsChars p ++ ' ' :: showNat p.moveNumber) from rfl]
    rw [tokens_field [sc] _ (noSpace_of_alpha (fun c h => by simp at h; subst h; exact hsc))
      (by simp)]
    rw [tokens_field _ _ (noSpace_of_alpha hHalpha) (handsChars_ne _)]
    rw [tokens_last _ (noSpace_of_alpha hNalpha) hNne]
  unfold parse
  rw [if_neg (by omega)]
  unfold print
  rw [String.toList_ofList]
  unfold parseChars
  rw [hfields]
  have hside := side_field p.side
  simp only [parseBoard_boardChars p.board hb, parseHands_handsChars p hhb hhw h18,
    parseMoveNumber_showNat hn.1 hn.2]
  have hside' : (if ([sc] == ['b']) = true then some Color.black
      else if ([sc] == ['w']) = true then some Color.white else none) = some p.side := hside
  rw [hside']
  have hp : ({ board := p.board, hands := p.hands, side := p.side, moveNumber := p.moveNumber } :
      Position) = p := rfl
  simp [Option.bind, hk.1, hk.2, hm]

/-- Every reachable position (with a move counter that still fits the C
    `unsigned`) survives an SFEN round trip. -/
theorem parse_print_reachable {p : Position} (h : Position.Reachable p)
    (hn : 1 ≤ p.moveNumber ∧ p.moveNumber ≤ uintMax) : parse (print p) = some p :=
  parse_print p (Position.reachable_inv h).1
    ⟨Position.reachable_kings h .black, Position.reachable_kings h .white⟩
    (Position.reachable_materialOk h) hn

end Shogi.Sfen
