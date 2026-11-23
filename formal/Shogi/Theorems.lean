/-
  Theorems about the rules spec (T2/T3): structure of legal moves, the
  uchifuzume recursion budget, and invariants of reachable positions.
-/
import Shogi.Rules
namespace Shogi.Position

theorem mem_legalAux {fuel : Nat} {p : Position} {m : Move} (h : m ∈ legalAux fuel p) :
    m ∈ p.pseudoMoves ∧ (p.play m).inCheck p.side = false := by
  cases fuel with
  | zero => simp [legalAux] at h
  | succ n =>
    simp only [legalAux, List.mem_filter, Bool.and_eq_true, Bool.not_eq_true'] at h
    exact ⟨h.1, h.2.1⟩

theorem boardMoves_normal {p : Position} {s : Square} {pc : Piece} {m : Move}
    (h : m ∈ p.boardMoves s pc) :
    ∃ d pr, m = .normal s d pr ∧ d ∈ p.attackSquares s pc ∧
      pr ∈ promoChoices pc.color pc.type s d ∧
      (∀ q, p.pieceAt d = some q → q.color ≠ pc.color ∧ q.type ≠ .king) := by
  simp only [boardMoves, List.mem_flatMap] at h
  obtain ⟨d, hd, hm⟩ := h
  split at hm
  · rename_i q hq
    split at hm
    · simp at hm
    · rename_i hne
      simp only [List.mem_map] at hm
      obtain ⟨pr, hpr, rfl⟩ := hm
      refine ⟨d, pr, rfl, hd, hpr, ?_⟩
      intro q' hq'
      rw [hq] at hq'; cases hq'
      simp only [Bool.or_eq_true, beq_iff_eq, not_or] at hne
      exact hne
  · rename_i hq
    simp only [List.mem_map] at hm
    obtain ⟨pr, hpr, rfl⟩ := hm
    exact ⟨d, pr, rfl, hd, hpr, by intro q hq'; rw [hq] at hq'; cases hq'⟩
end Shogi.Position
namespace Shogi.Position

theorem mem_dropMoves {p : Position} {m : Move} (h : m ∈ p.dropMoves) :
    ∃ i d, m = .drop (PieceType.ofHandIndex i) d ∧ p.hand p.side i > 0 ∧
      p.dropAllowed p.side (PieceType.ofHandIndex i) d = true := by
  simp only [dropMoves, List.mem_flatMap, List.mem_filterMap] at h
  obtain ⟨d, _, i, _, hm⟩ := h
  split at hm
  · rename_i hc
    simp only [Option.some.injEq] at hm
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
    exact ⟨i, d, hm.symm, hc.1, hc.2⟩
  · simp at hm

/-- Every pseudo-legal move is either a move of an own piece or a drop. -/
theorem mem_pseudoMoves {p : Position} {m : Move} (h : m ∈ p.pseudoMoves) :
    (∃ s pc, p.pieceAt s = some pc ∧ pc.color = p.side ∧ m ∈ p.boardMoves s pc) ∨
    m ∈ p.dropMoves := by
  simp only [pseudoMoves, List.mem_append, List.mem_flatMap] at h
  rcases h with ⟨s, _, hs⟩ | h
  · left
    split at hs
    · rename_i pc hpc
      split at hs
      · rename_i hc
        exact ⟨s, pc, hpc, by simpa using hc, hs⟩
      · simp at hs
    · simp at hs
  · exact Or.inr h

theorem legalMoves_pseudo {p : Position} {m : Move} (h : m ∈ p.legalMoves) :
    m ∈ p.pseudoMoves := (mem_legalAux h).1

/-- **King safety**: a legal move never leaves the mover's king attacked. -/
theorem legalMoves_safe {p : Position} {m : Move} (h : m ∈ p.legalMoves) :
    (p.play m).inCheck p.side = false := (mem_legalAux h).2

/-- **No king capture, no self-capture**. -/
theorem legalMoves_target {p : Position} {s d : Square} {pr : Bool} {q : Piece}
    (h : Move.normal s d pr ∈ p.legalMoves) (hq : p.pieceAt d = some q) :
    q.color ≠ p.side ∧ q.type ≠ .king := by
  rcases mem_pseudoMoves (legalMoves_pseudo h) with ⟨s', pc, _, hc, hm⟩ | hd
  · obtain ⟨d', pr', he, _, _, hcap⟩ := boardMoves_normal hm
    cases he
    rw [← hc]; exact hcap q hq
  · obtain ⟨_, _, he, _⟩ := mem_dropMoves hd
    cases he

theorem promoChoices_dead {c : Color} {t : PieceType} {s d : Square} {pr : Bool}
    (h : pr ∈ promoChoices c t s d) (hd : deadRow c t d.row = true) : pr = true := by
  simp [promoChoices, hd] at h; exact h

theorem promoChoices_canPromote {c : Color} {t : PieceType} {s d : Square}
    (h : true ∈ promoChoices c t s d) :
    t.canPromote = true ∧ (inZone c s.row = true ∨ inZone c d.row = true) ∨
      deadRow c t d.row = true := by
  unfold promoChoices at h
  split at h
  · exact Or.inr ‹_›
  · split at h
    · rename_i h2
      simp only [Bool.and_eq_true, Bool.or_eq_true] at h2
      exact Or.inl h2
    · simp at h

/-- **Forced promotion**: a piece that would have no further move promotes. -/
theorem legalMoves_forced {p : Position} {s d : Square} {pr : Bool} {pc : Piece}
    (h : Move.normal s d pr ∈ p.legalMoves) (hs : p.pieceAt s = some pc)
    (hd : deadRow pc.color pc.type d.row = true) : pr = true := by
  rcases mem_pseudoMoves (legalMoves_pseudo h) with ⟨s', pc', hs', _, hm⟩ | hd'
  · obtain ⟨d', pr', he, _, hpr, _⟩ := boardMoves_normal hm
    cases he
    rw [hs] at hs'; cases hs'
    exact promoChoices_dead hpr hd
  · obtain ⟨_, _, he, _⟩ := mem_dropMoves hd'
    cases he

/-- **Drop rules**: a dropped piece comes from the hand, lands on an empty
    square, would not be dead, and a pawn drop never makes nifu. -/
theorem legalMoves_drop {p : Position} {t : PieceType} {d : Square}
    (h : Move.drop t d ∈ p.legalMoves) :
    ∃ i, t.handIndex = some i ∧ p.hand p.side i > 0 ∧ p.isEmpty d = true ∧
      deadRow p.side t d.row = false ∧ (t = .pawn → p.pawnOnFile p.side d.col = false) := by
  rcases mem_pseudoMoves (legalMoves_pseudo h) with ⟨s', pc, _, _, hm⟩ | hd
  · obtain ⟨_, _, he, _⟩ := boardMoves_normal hm
    cases he
  · obtain ⟨i, d', he, hh, ha⟩ := mem_dropMoves hd
    cases he
    simp only [dropAllowed, Bool.and_eq_true, Bool.not_eq_true'] at ha
    obtain ⟨⟨he, hdead⟩, hn⟩ := ha
    refine ⟨i, PieceType.handIndex_ofHandIndex i, hh, he, hdead, ?_⟩
    intro ht
    simp [ht] at hn
    exact hn

end Shogi.Position
namespace Shogi

theorem getD_set_self {l : List Nat} {i n : Nat} (h : i < l.length) :
    (l.set i n).getD i 0 = n := by
  simp [List.getD, h]

theorem getD_set_ne {l : List Nat} {i j n : Nat} (h : i ≠ j) :
    (l.set i n).getD j 0 = l.getD j 0 := by
  simp [List.getD, List.getElem?_set, h]

theorem lt_of_getD_pos {l : List Nat} {i : Nat} (h : l.getD i 0 > 0) : i < l.length := by
  rcases Nat.lt_or_ge i l.length with h' | h'
  · exact h'
  · simp [List.getD, List.getElem?_eq_none h'] at h

theorem Hands.get_set_self {h : Hands} {c : Color} {i : Fin 7} {n : Nat}
    (hp : h.get c i > 0) : (h.set c i n).get c i = n := by
  cases c <;> simp only [Hands.get, Hands.set] at * <;>
    exact getD_set_self (lt_of_getD_pos hp)

theorem Hands.get_set_other_color {h : Hands} {c : Color} {i j : Fin 7} {n : Nat} :
    (h.set c i n).get c.opp j = h.get c.opp j := by
  cases c <;> rfl

theorem Hands.get_set_ne {h : Hands} {c c' : Color} {i j : Fin 7} {n : Nat} (hij : i ≠ j) :
    (h.set c i n).get c' j = h.get c' j := by
  have : i.val ≠ j.val := fun e => hij (Fin.ext e)
  cases c <;> cases c' <;> simp only [Hands.get, Hands.set] <;>
    first | rfl | exact getD_set_ne this

namespace Position

theorem pawnsInHands_eq (p : Position) (c : Color) :
    p.pawnsInHands = p.hand c 0 + p.hand c.opp 0 := by
  cases c <;> simp [pawnsInHands, Color.opp] <;> omega

/-- A pawn drop uses up one pawn from the hands. -/
theorem pawnsInHands_play_drop {p : Position} {m : Move}
    (hm : m ∈ p.pseudoMoves) (hp : isPawnDrop m = true) :
    (p.play m).pawnsInHands + 1 = p.pawnsInHands := by
  rcases mem_pseudoMoves hm with ⟨_, _, _, _, hb⟩ | hd
  · obtain ⟨_, _, rfl, _⟩ := boardMoves_normal hb; simp [isPawnDrop] at hp
  · obtain ⟨i, d, rfl, hh, _⟩ := mem_dropMoves hd
    have hi : i = 0 := by
      have key : ∀ j : Fin 7, PieceType.ofHandIndex j = .pawn → j = 0 := by decide
      apply key
      cases ht : PieceType.ofHandIndex i <;> simp_all [isPawnDrop]
    subst hi
    have hpos : p.hands.get p.side 0 > 0 := hh
    rw [pawnsInHands_eq (p.play _) p.side, pawnsInHands_eq p p.side]
    simp only [play, PieceType.ofHandIndex, PieceType.handIndex, hand]
    rw [Hands.get_set_self hpos, Hands.get_set_other_color]
    simp only [hand] at hh
    omega

/-- The uchifuzume budget is adequate: more fuel changes nothing. -/
theorem legalAux_stable : ∀ (n : Nat) (p : Position) (k : Nat),
    p.pawnsInHands < n → legalAux (n + k) p = legalAux n p := by
  intro n
  induction n with
  | zero => intro p k h; omega
  | succ n ih =>
    intro p k h
    rw [show n + 1 + k = (n + k) + 1 by omega]
    simp only [legalAux]
    apply List.filter_congr
    intro m hm
    by_cases hp : isPawnDrop m = true
    · have := pawnsInHands_play_drop hm hp
      rw [ih (p.play m) k (by omega)]
    · simp [hp]

theorem legalMoves_eq_aux (p : Position) (n : Nat) (h : p.pawnsInHands < n) :
    p.legalMoves = legalAux n p := by
  unfold legalMoves legalFuel
  have a := legalAux_stable (p.pawnsInHands + 1) p 1 (by omega)
  have b := legalAux_stable (p.pawnsInHands + 1) p (n - (p.pawnsInHands + 1)) (by omega)
  rw [show p.pawnsInHands + 1 + (n - (p.pawnsInHands + 1)) = n by omega] at b
  rw [b, ← a]

/-- **Legality, fuel-free.** A move is legal iff it is pseudo-legal, does not
    leave the mover in check, and is not uchifuzume — where uchifuzume refers
    back to `legalMoves` of the resulting position (recursion that terminates
    because every nested level consumes a pawn). -/
theorem legalMoves_iff (p : Position) (m : Move) :
    m ∈ p.legalMoves ↔
      m ∈ p.pseudoMoves ∧ (p.play m).inCheck p.side = false ∧ p.uchifuzume m = false := by
  rw [legalMoves_eq_aux p (p.pawnsInHands + 1) (by omega)]
  simp only [legalAux, List.mem_filter, Bool.and_eq_true, Bool.not_eq_true']
  constructor
  · rintro ⟨hm, hc, hu⟩
    refine ⟨hm, hc, ?_⟩
    show (isPawnDrop m && (p.play m).inCheck (p.play m).side &&
      (p.play m).legalMoves.isEmpty) = false
    by_cases hp : isPawnDrop m = true
    · have := pawnsInHands_play_drop hm hp
      rw [legalMoves_eq_aux (p.play m) p.pawnsInHands (by omega)]
      exact hu
    · simp [hp]
  · rintro ⟨hm, hc, hu⟩
    refine ⟨hm, hc, ?_⟩
    change (isPawnDrop m && (p.play m).inCheck (p.play m).side &&
      (p.play m).legalMoves.isEmpty) = false at hu
    by_cases hp : isPawnDrop m = true
    · have := pawnsInHands_play_drop hm hp
      rw [legalMoves_eq_aux (p.play m) p.pawnsInHands (by omega)] at hu
      exact hu
    · simp [hp]

end Position
end Shogi
namespace Shogi

theorem deadRow_promote (c : Color) (t : PieceType) (r : Nat) :
    deadRow c t.promote r = false := by
  cases c <;> cases t <;> rfl

theorem getD_setSq {b : List (Option Piece)} (hl : b.length = 81) (s t : Square)
    (x : Option Piece) :
    (Position.setSq b s x).getD t.val none = if t = s then x else b.getD t.val none := by
  unfold Position.setSq
  by_cases h : t = s
  · subst h; simp [List.getD, hl, t.isLt]
  · have : s.val ≠ t.val := fun e => h (Fin.ext e.symm)
    simp [List.getD, List.getElem?_set, this, h]

namespace Position

/-- No piece stands where it could never move again. -/
def NoDead (p : Position) : Prop :=
  ∀ s pc, p.pieceAt s = some pc → deadRow pc.color pc.type (Square.row s) = false

inductive Reachable : Position → Prop
  | start : Reachable Position.start
  | step {p m} : Reachable p → m ∈ p.legalMoves → Reachable (p.play m)

theorem Hands.set_black_len (h : Hands) (c : Color) (i : Fin 7) (n : Nat) :
    (h.set c i n).black.length = h.black.length := by cases c <;> simp [Hands.set]
theorem Hands.set_white_len (h : Hands) (c : Color) (i : Fin 7) (n : Nat) :
    (h.set c i n).white.length = h.white.length := by cases c <;> simp [Hands.set]

theorem play_shaped {p : Position} (hs : p.Shaped) (m : Move) : (p.play m).Shaped := by
  obtain ⟨hb, hw, hk⟩ := hs
  unfold play Shaped
  refine ⟨?_, ?_, ?_⟩ <;> (repeat' split) <;>
    simp_all [setSq, Hands.set_black_len, Hands.set_white_len]

theorem promoChoices_false {c : Color} {t : PieceType} {s d : Square}
    (h : false ∈ promoChoices c t s d) : deadRow c t d.row = false := by
  cases hd : deadRow c t d.row
  · rfl
  · exact absurd (promoChoices_dead h hd) (by decide)

theorem play_noDead {p : Position} (hs : p.Shaped) (hn : p.NoDead) {m : Move}
    (hm : m ∈ p.pseudoMoves) : (p.play m).NoDead := by
  have hb := hs.1
  intro t pc ht
  rcases mem_pseudoMoves hm with ⟨s, pc0, hs0, hc0, hbm⟩ | hd
  · obtain ⟨d, pr, rfl, _, hpr, _⟩ := boardMoves_normal hbm
    have hs0' : p.board.getD s.val none = some pc0 := hs0
    simp only [play, pieceAt, hs0'] at ht
    rw [getD_setSq (by simp [setSq, hb]), getD_setSq hb] at ht
    by_cases htd : t = d
    · subst htd
      simp only [ite_true, Option.some.injEq] at ht
      subst ht
      cases pr
      · simpa [hc0] using promoChoices_false hpr
      · simpa using deadRow_promote _ _ _
    · simp only [htd, ite_false] at ht
      by_cases hts : t = s
      · simp [hts] at ht
      · simp only [hts, ite_false] at ht
        exact hn t pc ht
  · obtain ⟨i, d, rfl, _, ha⟩ := mem_dropMoves hd
    simp only [play, PieceType.handIndex_ofHandIndex, pieceAt] at ht
    rw [getD_setSq hb] at ht
    by_cases htd : t = d
    · subst htd
      simp only [ite_true, Option.some.injEq] at ht
      subst ht
      simp only [dropAllowed, Bool.and_eq_true, Bool.not_eq_true'] at ha
      exact ha.1.2
    · simp only [htd, ite_false] at ht
      exact hn t pc ht

theorem start_shaped : Position.start.Shaped := by decide
theorem start_noDead : Position.start.NoDead := by
  intro s pc h
  revert pc h
  revert s
  decide

/-- **Invariant**: every reachable position is well-shaped and has no dead piece. -/
theorem reachable_inv {p : Position} (h : Reachable p) : p.Shaped ∧ p.NoDead := by
  induction h with
  | start => exact ⟨start_shaped, start_noDead⟩
  | step _ hm ih => exact ⟨play_shaped ih.1 _, play_noDead ih.1 ih.2 (legalMoves_pseudo hm)⟩

end Position
end Shogi
namespace Shogi.Position

def isK (c : Color) (x : Option Piece) : Bool := x == some ⟨c, .king⟩

theorem isK_moved : ∀ (c c' : Color) (t : PieceType) (pr : Bool),
    isK c (some ⟨c', if pr then t.promote else t⟩) = isK c (some ⟨c', t⟩) := by
  intro c c' t pr; cases c <;> cases c' <;> cases t <;> cases pr <;> rfl

theorem isK_drop : ∀ (c c' : Color) (i : Fin 7),
    isK c (some ⟨c', PieceType.ofHandIndex i⟩) = false := by
  intro c c' i; cases c <;> cases c' <;> revert i <;> decide

theorem getElem_of_getD {b : List (Option Piece)} {i : Nat} (hi : i < b.length)
    {x : Option Piece} (h : b.getD i none = x) : b[i] = x := by
  simpa [List.getD, hi] using h

theorem kingCount_eq (p : Position) (c : Color) : p.kingCount c = p.board.countP (isK c) := rfl

/-- Kings are conserved by every pseudo-legal move (no move captures a king,
    and a king never promotes or comes from a hand). -/
theorem play_kingCount {p : Position} (hs : p.Shaped) {m : Move} (hm : m ∈ p.pseudoMoves)
    (c : Color) : (p.play m).kingCount c = p.kingCount c := by
  have hb := hs.1
  rw [kingCount_eq, kingCount_eq]
  rcases mem_pseudoMoves hm with ⟨s, pc, hs0, hc0, hbm⟩ | hd
  · obtain ⟨d, pr, rfl, _, _, hcap⟩ := boardMoves_normal hbm
    obtain ⟨pcc, pct⟩ := pc
    simp only at hc0
    subst hc0
    have hs0' : p.board.getD s.val none = some ⟨p.side, pct⟩ := hs0
    simp only [play, pieceAt, hs0', setSq]
    have hsl : s.val < p.board.length := by omega
    have hdl : d.val < (p.board.set s.val none).length := by simp [hb]
    rw [List.countP_set hdl, List.countP_set hsl]
    have e1 : p.board[s.val] = some ⟨p.side, pct⟩ := getElem_of_getD hsl hs0'
    have e2 : isK c ((p.board.set s.val none)[d.val]) = false := by
      rw [List.getElem_set]
      split
      · rfl
      · cases hq : p.board[d.val] with
        | none => rfl
        | some q =>
          have hk := (hcap q (by
            have hdl' : d.val < p.board.length := by rw [hb]; exact d.isLt
            simpa [pieceAt, List.getD, hdl'] using hq)).2
          obtain ⟨qc, qt⟩ := q
          simp only at hk
          cases c <;> cases qc <;> cases qt <;> simp_all [isK]
    have hn : isK c none = false := rfl
    rw [e2, hn, e1, isK_moved]
    have pos : (if isK c (some ⟨p.side, pct⟩) = true then 1 else 0) ≤
        p.board.countP (isK c) := by
      split
      · exact List.countP_pos_iff.mpr ⟨_, e1 ▸ List.getElem_mem hsl, ‹_›⟩
      · exact Nat.zero_le _
    split
    · rename_i h
      rw [if_pos h] at pos
      simp only [Bool.false_eq_true, ite_false, Nat.add_zero, Nat.sub_zero]
      omega
    · simp
  · obtain ⟨i, d, rfl, _, ha⟩ := mem_dropMoves hd
    simp only [play, PieceType.handIndex_ofHandIndex, setSq]
    have hdl : d.val < p.board.length := by omega
    rw [List.countP_set hdl, isK_drop]
    have he : p.board[d.val] = none := by
      simp only [dropAllowed, Bool.and_eq_true, isEmpty, pieceAt, Option.isNone_iff_eq_none] at ha
      exact getElem_of_getD hdl ha.1.1
    simp [he, isK]

/-- **Invariant**: every reachable position has exactly one king per side. -/
theorem reachable_kings {p : Position} (h : Reachable p) (c : Color) : p.kingCount c = 1 := by
  induction h with
  | start => cases c <;> decide
  | step hr hm ih =>
    rw [play_kingCount (reachable_inv hr).1 (legalMoves_pseudo hm)]; exact ih

end Shogi.Position

namespace Shogi
namespace Position

/-- Family-`i` indicator of a square's content. -/
def famP (i : Fin 7) (x : Option Piece) : Bool :=
  match x with
  | some pc => pc.type.unpromote.handIndex == some i
  | none => false

theorem familyCount_eq (p : Position) (i : Fin 7) :
    p.familyCount i = p.board.countP (famP i) + p.hand .black i + p.hand .white i := rfl

theorem unpromote_promote_any (t : PieceType) : t.promote.unpromote = t.unpromote := by
  cases t <;> rfl

theorem famP_moved (i : Fin 7) (c : Color) (t : PieceType) (pr : Bool) :
    famP i (some ⟨c, if pr then t.promote else t⟩) = famP i (some ⟨c, t⟩) := by
  cases pr <;> simp [famP, unpromote_promote_any]

theorem Hands.get_set_len {h : Hands} (hb : h.black.length = 7) (hw : h.white.length = 7)
    (c c' : Color) (i j : Fin 7) (n : Nat) :
    (h.set c i n).get c' j = if c = c' ∧ i = j then n else h.get c' j := by
  by_cases hc : c = c'
  · subst hc
    by_cases hij : i = j
    · subst hij
      cases c <;> simp [Hands.set, Hands.get, List.getD, hb, hw, i.isLt]
    · simp only [hij, and_false, ite_false]; exact Hands.get_set_ne hij
  · simp only [hc, false_and, ite_false]
    cases c <;> cases c' <;> first | exact absurd rfl hc | rfl

/-- `countP` after `set`, in additive form (no truncated subtraction). -/
theorem countP_set_add {b : List (Option Piece)} {k : Nat} (hk : k < b.length)
    (x : Option Piece) (P : Option Piece → Bool) :
    (b.set k x).countP P + (if P b[k] then 1 else 0) = b.countP P + (if P x then 1 else 0) := by
  rw [List.countP_set hk]
  have : (if P b[k] = true then 1 else 0) ≤ b.countP P := by
    split
    · exact List.countP_pos_iff.mpr ⟨_, List.getElem_mem hk, ‹_›⟩
    · exact Nat.zero_le _
  split <;> split <;> simp_all <;> omega

/-- **Material conservation**: a pseudo-legal move preserves, for every
    unpromoted family, the number of pieces on the board plus in hand. -/
theorem play_familyCount {p : Position} (hs : p.Shaped) {m : Move} (hm : m ∈ p.pseudoMoves)
    (i : Fin 7) : (p.play m).familyCount i = p.familyCount i := by
  obtain ⟨hb, hbw, hww⟩ := hs
  rw [familyCount_eq, familyCount_eq]
  rcases mem_pseudoMoves hm with ⟨s, pc, hs0, hc0, hbm⟩ | hd
  · obtain ⟨d, pr, rfl, _, _, hcap⟩ := boardMoves_normal hbm
    obtain ⟨pcc, pct⟩ := pc
    simp only at hc0
    subst hc0
    have hs0' : p.board.getD s.val none = some ⟨p.side, pct⟩ := hs0
    have hsl : s.val < p.board.length := by rw [hb]; exact s.isLt
    have hdl : d.val < p.board.length := by rw [hb]; exact d.isLt
    have e1 : p.board[s.val] = some ⟨p.side, pct⟩ := getElem_of_getD hsl hs0'
    have hdl' : d.val < (p.board.set s.val none).length := by simpa using hdl
    have h1 := countP_set_add hsl none (famP i)
    have h2 := countP_set_add hdl' (some ⟨p.side, if pr then pct.promote else pct⟩) (famP i)
    rw [famP_moved] at h2
    rw [e1] at h1
    have hn : famP i none = false := rfl
    rw [hn] at h1
    have hd' : (p.board.set s.val none)[d.val] =
        if s.val = d.val then none else p.board[d.val] := by
      rw [List.getElem_set]
    have hboard : (p.play (.normal s d pr)).board =
        (p.board.set s.val none).set d.val (some ⟨p.side, if pr then pct.promote else pct⟩) := by
      simp only [play, pieceAt]; rw [hs0']; simp [setSq]
    rw [hboard]
    cases hq : p.board[d.val] with
    | none =>
      have hq' : p.board.getD d.val none = none := by simp [List.getD, hdl, hq]
      have hhands : (p.play (.normal s d pr)).hands = p.hands := by
        simp only [play, pieceAt]; rw [hs0', hq']
      have hb1 : famP i ((p.board.set s.val none)[d.val]) = false := by
        rw [hd']; split <;> simp [hq, famP]
      rw [hb1] at h2
      simp only [hand, hhands]
      simp only [Bool.false_eq_true, ite_false, Nat.add_zero] at h1 h2
      omega
    | some q =>
      have hq' : p.board.getD d.val none = some q := by simp [List.getD, hdl, hq]
      have hcq := hcap q (by simpa [pieceAt] using hq')
      obtain ⟨qc, qt⟩ := q
      simp only at hcq
      have hj : ∃ j, qt.unpromote.handIndex = some j := by
        cases qt <;> simp_all [PieceType.unpromote, PieceType.handIndex]
      obtain ⟨j, hj⟩ := hj
      have hhands : (p.play (.normal s d pr)).hands =
          p.hands.set p.side j (p.hand p.side j + 1) := by
        simp only [play, pieceAt]; rw [hs0', hq']; simp [hj]
      have hsd : s.val ≠ d.val := by
        intro e
        have : p.board[d.val] = some ⟨p.side, pct⟩ := by simp only [← e]; exact e1
        rw [this] at hq; cases hq
        exact hcq.1 rfl
      rw [hd', if_neg hsd, hq] at h2
      have hfq : famP i (some ⟨qc, qt⟩) = (j == i) := by simp [famP, hj]
      rw [hfq] at h2
      simp only [hand, hhands]
      rw [Hands.get_set_len hbw hww, Hands.get_set_len hbw hww]
      cases hside : p.side <;> by_cases hji : j = i <;>
        simp_all [Hands.get, hand] <;> omega
  · obtain ⟨k, d, rfl, hh, ha⟩ := mem_dropMoves hd
    simp only [play, PieceType.handIndex_ofHandIndex, setSq, hand]
    have hdl : d.val < p.board.length := by rw [hb]; exact d.isLt
    have he : p.board[d.val] = none := by
      simp only [dropAllowed, Bool.and_eq_true, isEmpty, pieceAt, Option.isNone_iff_eq_none] at ha
      exact getElem_of_getD hdl ha.1.1
    have h := countP_set_add hdl (some ⟨p.side, PieceType.ofHandIndex k⟩) (famP i)
    rw [he] at h
    have hf : famP i (some ⟨p.side, PieceType.ofHandIndex k⟩) = (k == i) := by
      have := PieceType.handIndex_ofHandIndex k
      have hu : (PieceType.ofHandIndex k).unpromote = PieceType.ofHandIndex k :=
        (by decide : ∀ k : Fin 7, (PieceType.ofHandIndex k).unpromote = PieceType.ofHandIndex k) k
      simp [famP, hu, this]
    rw [hf] at h
    simp only [famP, Bool.false_eq_true, ite_false, Nat.add_zero] at h
    rw [Hands.get_set_len hbw hww, Hands.get_set_len hbw hww]
    simp only [hand] at hh
    cases hside : p.side <;> by_cases hki : k = i <;> simp_all [Hands.get] <;> omega

theorem start_familyCount : ∀ i : Fin 7, Position.start.familyCount i = PieceType.handMax i := by
  decide

/-- **Invariant**: every reachable position has exactly a full set of each
    unpromoted family (board plus both hands), so `validate_material` holds. -/
theorem reachable_material {p : Position} (h : Reachable p) (i : Fin 7) :
    p.familyCount i = PieceType.handMax i := by
  induction h with
  | start => exact start_familyCount i
  | step hr hm ih => rw [play_familyCount (reachable_inv hr).1 (legalMoves_pseudo hm)]; exact ih

theorem reachable_materialOk {p : Position} (h : Reachable p) : p.materialOk = true := by
  unfold materialOk
  rw [List.all_eq_true]
  intro i _
  simp [reachable_material h i]

/-- **No side to move is in check.** A legal move always leaves the mover's
    king safe; the side to move after the move is the opponent. This is the
    `hnc` hypothesis of the C generator refinement. -/
theorem reachable_opp_not_in_check {p : Position} (h : Reachable p) :
    p.inCheck p.side.opp = false := by
  induction h with
  | start => decide
  | step hr hm ih =>
      rename_i p0 m0
      have hsafe : (p0.play m0).inCheck p0.side = false := legalMoves_safe hm
      cases p0.side <;> simpa [play] using hsafe

end Position
end Shogi
