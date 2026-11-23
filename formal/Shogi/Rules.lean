/-
  Movement, attacks, pseudo-legal moves and legality.

  This is the executable reference. It is written for clarity, not speed:
  attacks are computed from the attacker's side (the C computes them
  target-centred from precomputed tables), and every candidate move is
  checked by playing it (the C skips the check for pieces that are not
  pinned).

  Conventions shared with `src/shogi.c`, all stated as rules:
  * a move that would capture a king is never generated (in a position
    reached by legal play, the side to move cannot capture a king);
  * a position without a king of the side to move is never "in check";
  * uchifuzume: a pawn drop that checks and leaves the opponent no legal
    reply is illegal. "Legal reply" itself respects uchifuzume, so the
    definition is recursive; each nested level consumes one pawn from a
    hand, which bounds the recursion (`legalFuel`).
-/
import Shogi.Position

namespace Shogi

/-- Rows towards the opponent: black moves to smaller rows. -/
def Color.fwd : Color → Int
  | .black => -1
  | .white => 1

/-- Single-step offsets `(dRow, dCol)` of a piece type (relative to `fwd = f`). -/
def stepOffsets (f : Int) : PieceType → List (Int × Int)
  | .pawn => [(f, 0)]
  | .knight => [(2 * f, -1), (2 * f, 1)]
  | .silver => [(f, -1), (f, 0), (f, 1), (-f, -1), (-f, 1)]
  | .gold | .proPawn | .proLance | .proKnight | .proSilver =>
    [(f, -1), (f, 0), (f, 1), (0, -1), (0, 1), (-f, 0)]
  | .king => [(-1, -1), (-1, 0), (-1, 1), (0, -1), (0, 1), (1, -1), (1, 0), (1, 1)]
  | .horse => [(-1, 0), (1, 0), (0, -1), (0, 1)]
  | .dragon => [(-1, -1), (-1, 1), (1, -1), (1, 1)]
  | _ => []

def diagonals : List (Int × Int) := [(-1, -1), (-1, 1), (1, -1), (1, 1)]
def orthogonals : List (Int × Int) := [(-1, 0), (1, 0), (0, -1), (0, 1)]

/-- Sliding directions of a piece type. -/
def slideDirs (f : Int) : PieceType → List (Int × Int)
  | .lance => [(f, 0)]
  | .bishop | .horse => diagonals
  | .rook | .dragon => orthogonals
  | _ => []

def Square.offset (s : Square) (d : Int × Int) : Option Square :=
  Square.mk? ((s.row : Int) + d.1) ((s.col : Int) + d.2)

/-- Squares along a ray from `s` (exclusive) up to the edge. -/
def ray (s : Square) (d : Int × Int) : List Square :=
  go 8 s
where
  go : Nat → Square → List Square
    | 0, _ => []
    | n + 1, t => match t.offset d with
      | some u => u :: go n u
      | none => []

namespace Position

def isEmpty (p : Position) (s : Square) : Bool := (p.pieceAt s).isNone

/-- Squares reachable by sliding from `s` in direction `d`: empties, then the
    first occupied square (whatever its colour). -/
def slideTargets (p : Position) (s : Square) (d : Int × Int) : List Square :=
  go (ray s d)
where
  go : List Square → List Square
    | [] => []
    | t :: r => if p.isEmpty t then t :: go r else [t]

/-- Squares a piece of colour `c` and type `t` on `s` attacks (the
    occupancy of the destination is ignored). -/
def attackSquares (p : Position) (s : Square) (pc : Piece) : List Square :=
  let f := pc.color.fwd
  (stepOffsets f pc.type).filterMap s.offset ++
    (slideDirs f pc.type).flatMap (p.slideTargets s)

/-- `by` attacks square `sq`. -/
def attacked (p : Position) (sq : Square) (by_ : Color) : Bool :=
  (List.finRange 81).any fun s =>
    match p.pieceAt s with
    | some pc => pc.color == by_ && (p.attackSquares s pc).contains sq
    | none => false

def kingSquare (p : Position) (c : Color) : Option Square :=
  (List.finRange 81).find? fun s => p.pieceAt s == some ⟨c, .king⟩

def inCheck (p : Position) (c : Color) : Bool :=
  match p.kingSquare c with
  | some k => p.attacked k c.opp
  | none => false

/-! ## Pseudo-legal moves -/

/-- Promotion choices for a piece of type `t` moving `src → dst`:
    forced promotion if it would be dead, optional inside the zone. -/
def promoChoices (c : Color) (t : PieceType) (src dst : Square) : List Bool :=
  if deadRow c t dst.row then [true]
  else if t.canPromote && (inZone c src.row || inZone c dst.row) then [false, true]
  else [false]

def boardMoves (p : Position) (s : Square) (pc : Piece) : List Move :=
  (p.attackSquares s pc).flatMap fun d =>
    match p.pieceAt d with
    | some q => if q.color == pc.color || q.type == .king then []
                else (promoChoices pc.color pc.type s d).map (.normal s d)
    | none => (promoChoices pc.color pc.type s d).map (.normal s d)

/-- An unpromoted pawn of colour `c` already stands on file (column) `col`. -/
def pawnOnFile (p : Position) (c : Color) (col : Nat) : Bool :=
  (List.finRange 81).any fun s => Square.col s == col && p.pieceAt s == some ⟨c, .pawn⟩

def dropAllowed (p : Position) (c : Color) (t : PieceType) (d : Square) : Bool :=
  p.isEmpty d && !deadRow c t d.row && !(t == .pawn && p.pawnOnFile c d.col)

def dropMoves (p : Position) : List Move :=
  let c := p.side
  (List.finRange 81).flatMap fun d =>
    (List.finRange 7).filterMap fun i =>
      let t := PieceType.ofHandIndex i
      if p.hand c i > 0 && p.dropAllowed c t d then some (.drop t d) else none

def pseudoMoves (p : Position) : List Move :=
  ((List.finRange 81).flatMap fun s =>
    match p.pieceAt s with
    | some pc => if pc.color == p.side then p.boardMoves s pc else []
    | none => []) ++ p.dropMoves

/-! ## Playing a move -/

def setSq (b : List (Option Piece)) (s : Square) (x : Option Piece) : List (Option Piece) :=
  b.set s.val x

/-- Play a move without any legality check (the caller guarantees it is
    pseudo-legal). -/
def play (p : Position) (m : Move) : Position :=
  let c := p.side
  let p' : Position := match m with
    | .drop t d =>
      match t.handIndex with
      | some i => { p with board := setSq p.board d (some ⟨c, t⟩),
                           hands := p.hands.set c i (p.hand c i - 1) }
      | none => p
    | .normal s d pr =>
      match p.pieceAt s with
      | none => p
      | some pc =>
        let moved : Piece := ⟨c, if pr then pc.type.promote else pc.type⟩
        let hands := match p.pieceAt d with
          | some q => match q.type.unpromote.handIndex with
            | some i => p.hands.set c i (p.hand c i + 1)
            | none => p.hands
          | none => p.hands
        { p with board := setSq (setSq p.board s none) d (some moved), hands }
  { p' with side := c.opp, moveNumber := p.moveNumber + 1 }

/-! ## Legality -/

def pawnsInHands (p : Position) : Nat := p.hand .black 0 + p.hand .white 0

def isPawnDrop : Move → Bool
  | .drop .pawn _ => true
  | _ => false

/-- Legal moves, with a recursion budget for nested uchifuzume checks. -/
def legalAux : Nat → Position → List Move
  | 0, _ => []
  | fuel + 1, p =>
    p.pseudoMoves.filter fun m =>
      let q := p.play m
      !q.inCheck p.side &&
        !(isPawnDrop m && q.inCheck q.side && (legalAux fuel q).isEmpty)

/-- Enough budget: each nested level is entered after a pawn drop. -/
def legalFuel (p : Position) : Nat := p.pawnsInHands + 2

def legalMoves (p : Position) : List Move := legalAux p.legalFuel p

/-- Uchifuzume, stated directly. -/
def uchifuzume (p : Position) (m : Move) : Bool :=
  let q := p.play m
  isPawnDrop m && q.inCheck q.side && (legalMoves q).isEmpty

def perft : Nat → Position → Nat
  | 0, _ => 1
  | n + 1, p => (p.legalMoves.map fun m => perft n (p.play m)).sum

end Position
end Shogi
