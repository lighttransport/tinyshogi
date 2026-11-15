/-
  Games: a position plus its history, sennichite (fourfold repetition) with
  the perpetual-check rule, and the game result, following
  `shogi_repetition_result` and `shogi_game_result`.

  The C identifies positions by a 64-bit Zobrist hash; the spec compares
  the positions themselves (board, hands, side to move). The two agree
  unless the hash collides (PLAN.md §3 T9, `NoCollision`).
-/
import Shogi.Rules
import Shogi.Declaration
import Shogi.Sfen

namespace Shogi

/-- What identifies a position for repetition: everything but the move number. -/
structure Key where
  board : List (Option Piece)
  hands : Hands
  side : Color
  deriving DecidableEq, Repr

def Position.key (p : Position) : Key := ⟨p.board, p.hands, p.side⟩

structure Entry where
  key : Key
  /-- Who made the move that produced this position (`none` for the start). -/
  mover : Option Color
  /-- That move left the opponent in check. -/
  check : Bool
  deriving DecidableEq, Repr

/-- `SHOGI_MAX_HISTORY`; later positions are not recorded. -/
def maxHistory : Nat := 4096

structure Game where
  pos : Position
  history : List Entry
  deriving Repr

inductive Result where
  | ongoing | blackWin | whiteWin | draw
  deriving DecidableEq, Repr

def Result.winFor : Color → Result
  | .black => .blackWin
  | .white => .whiteWin

namespace Game

def init (p : Position) : Game := ⟨p, [⟨p.key, none, false⟩]⟩

/-- Play a legal move. `none` if illegal, or if the move counter would pass
    `UINT_MAX` (the C refuses such a move). -/
def play (g : Game) (m : Move) : Option Game :=
  if g.pos.moveNumber ≥ Sfen.uintMax || !g.pos.legalMoves.contains m then none
  else
    let q := g.pos.play m
    let e : Entry := ⟨q.key, some g.pos.side, q.inCheck q.side⟩
    some ⟨q, if g.history.length < maxHistory then g.history ++ [e] else g.history⟩

/-- Indices of history entries whose key is the current position's. -/
def occurrences (g : Game) : List Nat :=
  (g.history.zipIdx.filter fun (e, _) => e.key == g.pos.key).map (·.2)

/-- Fourfold repetition. The cycle is everything after the first of the last
    four occurrences; a side that moved in the cycle and gave check with every
    one of its moves loses (black is examined first); otherwise a draw. -/
def repetition (g : Game) : Option Result :=
  let occ := g.occurrences
  if occ.length < 4 then none
  else
    let start := occ[occ.length - 4]!
    let cycle := g.history.drop (start + 1)
    let perpetual (c : Color) : Bool :=
      let mine := cycle.filter (·.mover == some c)
      !mine.isEmpty && mine.all (·.check)
    if perpetual .black then some .whiteWin
    else if perpetual .white then some .blackWin
    else some .draw

/-- `shogi_game_result`: repetition, then declaration by the side to move,
    then mate (no legal move loses). -/
def result (g : Game) : Result :=
  match g.repetition with
  | some r => r
  | none =>
    if g.pos.declarationWin g.pos.side then Result.winFor g.pos.side
    else if g.pos.legalMoves.isEmpty then Result.winFor g.pos.side.opp
    else .ongoing

end Game
end Shogi
