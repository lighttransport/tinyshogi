/-
  Positions. Only the rule-relevant state is here: board, hands, side to
  move, move number. The Zobrist hash, cached king squares and the
  repetition history of `ShogiPosition` are implementation details; the
  game history used by sennichite is modelled separately (`Shogi/Game.lean`).
-/
import Shogi.Basic

namespace Shogi

/-- Hand counts in slot order P L N S G B R. -/
structure Hands where
  black : List Nat
  white : List Nat
  deriving DecidableEq, Repr

def Hands.empty : Hands := ⟨List.replicate 7 0, List.replicate 7 0⟩

def Hands.get (h : Hands) : Color → Fin 7 → Nat
  | .black, i => h.black.getD i.val 0
  | .white, i => h.white.getD i.val 0

def Hands.set (h : Hands) (c : Color) (i : Fin 7) (n : Nat) : Hands :=
  match c with
  | .black => { h with black := h.black.set i.val n }
  | .white => { h with white := h.white.set i.val n }

structure Position where
  /-- 81 squares, `row * 9 + col`. -/
  board : List (Option Piece)
  hands : Hands
  side : Color
  /-- `move_number` (the SFEN move counter, ≥ 1). -/
  moveNumber : Nat
  deriving DecidableEq, Repr

namespace Position

def pieceAt (p : Position) (s : Square) : Option Piece := p.board.getD s.val none

def hand (p : Position) (c : Color) (i : Fin 7) : Nat := p.hands.get c i

/-- Structural shape: 81 squares and two hands of 7 slots. -/
def Shaped (p : Position) : Prop :=
  p.board.length = 81 ∧ p.hands.black.length = 7 ∧ p.hands.white.length = 7

instance (p : Position) : Decidable p.Shaped := by unfold Shaped; infer_instance

def emptyBoard : List (Option Piece) := List.replicate 81 none

/-- Number of kings of colour `c` on the board. -/
def kingCount (p : Position) (c : Color) : Nat :=
  p.board.countP (· == some ⟨c, .king⟩)

/-- Total number of pieces of unpromoted family `i` on the board and in both hands. -/
def familyCount (p : Position) (i : Fin 7) : Nat :=
  p.board.countP (fun o => match o with
    | some pc => pc.type.unpromote.handIndex == some i
    | none => false)
  + p.hand .black i + p.hand .white i

/-- `validate_material`: no family exceeds a full set. -/
def materialOk (p : Position) : Bool :=
  (List.finRange 7).all fun i => p.familyCount i ≤ PieceType.handMax i

end Position

/-- Rows of the standard initial position, as in `shogi_position_start`. -/
private def startRows : List (List (Option Piece)) :=
  let w (t : PieceType) : Option Piece := some ⟨.white, t⟩
  let b (t : PieceType) : Option Piece := some ⟨.black, t⟩
  let back (f : PieceType → Option Piece) :=
    [f .lance, f .knight, f .silver, f .gold, f .king, f .gold, f .silver, f .knight, f .lance]
  let e := (none : Option Piece)
  [ back w,
    [e, w .rook, e, e, e, e, e, w .bishop, e],
    List.replicate 9 (w .pawn),
    List.replicate 9 e, List.replicate 9 e, List.replicate 9 e,
    List.replicate 9 (b .pawn),
    [e, b .bishop, e, e, e, e, e, b .rook, e],
    back b ]

def Position.start : Position where
  board := startRows.flatten
  hands := Hands.empty
  side := .black
  moveNumber := 1

end Shogi
