/-
  Foundational theorems about `Game`: well-formedness of the history and
  facts about `occurrences`/`repetition`.  These are the spec-level basis for
  the repetition (sennichite) refinement in M7.
-/
import Shogi.Game

namespace Shogi
namespace Game

/-- A game is well-formed when the history length is within bounds and either
    the history is full or its last entry matches the current position. -/
def WellFormed (g : Game) : Prop :=
  g.history.length ≤ maxHistory ∧
  (g.history.length = maxHistory ∨
   ∃ e, g.history.getLast? = some e ∧ e.key = g.pos.key)

theorem init_wf (p : Position) : WellFormed (init p) := by
  constructor
  · simp [init, maxHistory]
  · right
    exact ⟨⟨p.key, none, false⟩, by simp [init], by simp [init]⟩

/-- The guard Bool used by `Game.play` equals the corresponding Prop. -/
theorem guard_eq (g : Game) (m : Move) :
    (g.pos.moveNumber ≥ Sfen.uintMax || !g.pos.legalMoves.contains m) =
      decide (g.pos.moveNumber ≥ Sfen.uintMax ∨ m ∉ g.pos.legalMoves) := by
  simp [Bool.or_eq_true]

/-- A legal play preserves well-formedness. -/
theorem play_wf {g : Game} {m : Move} {g' : Game}
    (hplay : Game.play g m = some g') (hwf : WellFormed g) : WellFormed g' := by
  unfold Game.play at hplay
  by_cases hbad : g.pos.moveNumber ≥ Sfen.uintMax ∨ m ∉ g.pos.legalMoves
  · rw [guard_eq, decide_eq_true hbad] at hplay
    cases hplay
  · rw [guard_eq, decide_eq_false hbad] at hplay
    dsimp only at hplay
    rcases hwf with ⟨hlen, hlast⟩
    by_cases hcap : g.history.length < maxHistory
    · simp only [hcap, ↓reduceIte] at hplay
      cases hplay
      constructor
      · simp only [List.length_append, List.length_singleton]
        omega
      · right
        refine ⟨⟨(g.pos.play m).key, some g.pos.side, (g.pos.play m).inCheck (g.pos.play m).side⟩, ?_, ?_⟩
        · rw [List.getLast?_concat]
        · rfl
    · simp only [hcap, ↓reduceIte] at hplay
      cases hplay
      constructor
      · exact hlen
      · left
        exact Nat.le_antisymm hlen (Nat.le_of_not_gt hcap)

/-- Every occurrence index points at a history entry whose key is the current
    position's. -/
theorem occurrences_spec (g : Game) {i : Nat} (hi : i ∈ g.occurrences) :
    (g.history[i]?).map Entry.key = some g.pos.key := by
  unfold occurrences at hi
  rw [List.mem_map] at hi
  rcases hi with ⟨pair, hpair, hp⟩
  rw [List.mem_filter] at hpair
  rcases hpair with ⟨hmem, hkey⟩
  simp only [beq_iff_eq] at hkey
  have hzi := List.mem_zipIdx' hmem
  have hpj : pair.2 = i := by simpa using hp
  subst i
  rcases pair with ⟨e, j⟩
  simp only [Prod.snd]
  rw [List.getElem?_eq_getElem hzi.1]
  rw [← hzi.2]
  simpa using hkey

/-- Fewer than four occurrences means no repetition result. -/
theorem repetition_none_of_lt_four (g : Game) (h : g.occurrences.length < 4) :
    g.repetition = none := by
  unfold repetition
  simp [h]

end Game
end Shogi
