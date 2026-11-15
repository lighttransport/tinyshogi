/-
  Basic shogi vocabulary: colours, piece types, pieces, squares, moves.

  Squares are numbered as in `src/shogi.c`: `sq = row * 9 + col`, where
  row 0 is rank `a` (White's back rank) and col 0 is file 9.
-/
namespace Shogi

inductive Color where
  | black
  | white
  deriving DecidableEq, Repr, Inhabited

def Color.opp : Color → Color
  | .black => .white
  | .white => .black

/-- Index as in `ShogiColor` (black = 0, white = 1). -/
def Color.idx : Color → Nat
  | .black => 0
  | .white => 1

@[simp] theorem Color.opp_opp (c : Color) : c.opp.opp = c := by cases c <;> rfl

/-- Piece types, in the order (and with the codes) of `ShogiPieceType`. -/
inductive PieceType where
  | pawn | lance | knight | silver | gold | bishop | rook | king
  | proPawn | proLance | proKnight | proSilver | horse | dragon
  deriving DecidableEq, Repr, Inhabited

namespace PieceType

/-- The C code (`SHOGI_PAWN = 1` … `SHOGI_DRAGON = 14`). -/
def code : PieceType → Nat
  | pawn => 1 | lance => 2 | knight => 3 | silver => 4 | gold => 5
  | bishop => 6 | rook => 7 | king => 8 | proPawn => 9 | proLance => 10
  | proKnight => 11 | proSilver => 12 | horse => 13 | dragon => 14

def ofCode : Nat → Option PieceType
  | 1 => some pawn | 2 => some lance | 3 => some knight | 4 => some silver
  | 5 => some gold | 6 => some bishop | 7 => some rook | 8 => some king
  | 9 => some proPawn | 10 => some proLance | 11 => some proKnight
  | 12 => some proSilver | 13 => some horse | 14 => some dragon
  | _ => none

theorem ofCode_code (t : PieceType) : ofCode t.code = some t := by cases t <;> rfl

def isPromoted : PieceType → Bool
  | proPawn | proLance | proKnight | proSilver | horse | dragon => true
  | _ => false

def canPromote : PieceType → Bool
  | pawn | lance | knight | silver | bishop | rook => true
  | _ => false

def promote : PieceType → PieceType
  | pawn => proPawn | lance => proLance | knight => proKnight
  | silver => proSilver | bishop => horse | rook => dragon
  | t => t

def unpromote : PieceType → PieceType
  | proPawn => pawn | proLance => lance | proKnight => knight
  | proSilver => silver | horse => bishop | dragon => rook
  | t => t

/-- Hand slot (`hand_index`): P L N S G B R = 0..6; `none` for king and promoted. -/
def handIndex : PieceType → Option (Fin 7)
  | pawn => some 0 | lance => some 1 | knight => some 2 | silver => some 3
  | gold => some 4 | bishop => some 5 | rook => some 6
  | _ => none

/-- Inverse of `handIndex`. -/
def ofHandIndex : Fin 7 → PieceType
  | 0 => pawn | 1 => lance | 2 => knight | 3 => silver
  | 4 => gold | 5 => bishop | 6 => rook

theorem handIndex_ofHandIndex (i : Fin 7) : handIndex (ofHandIndex i) = some i := by
  revert i; decide

theorem unpromote_promote (t : PieceType) (h : t.canPromote = true) :
    t.promote.unpromote = t := by cases t <;> simp_all [canPromote, promote, unpromote]

/-- Number of pieces of each unpromoted family in a full set (`validate_material`). -/
def handMax : Fin 7 → Nat
  | 0 => 18 | 1 => 4 | 2 => 4 | 3 => 4 | 4 => 4 | 5 => 2 | 6 => 2

/-- SFEN letter (lower case) of the unpromoted family. -/
def letter (t : PieceType) : Char :=
  match t.unpromote with
  | pawn => 'p' | lance => 'l' | knight => 'n' | silver => 's'
  | gold => 'g' | bishop => 'b' | rook => 'r' | king => 'k'
  | _ => '?'

/-- Parse a lower-case SFEN letter (board pieces, including king). -/
def ofLetter : Char → Option PieceType
  | 'p' => some pawn | 'l' => some lance | 'n' => some knight
  | 's' => some silver | 'g' => some gold | 'b' => some bishop
  | 'r' => some rook | 'k' => some king
  | _ => none

end PieceType

structure Piece where
  color : Color
  type : PieceType
  deriving DecidableEq, Repr, Inhabited

/-- The piece byte of `src/shogi.c`: `type | color << 4`. -/
def Piece.code (p : Piece) : Nat := p.type.code + 16 * p.color.idx

abbrev Square := Fin 81

def Square.row (s : Square) : Nat := s.val / 9
def Square.col (s : Square) : Nat := s.val % 9

def Square.mk? (row col : Int) : Option Square :=
  if h : 0 ≤ row ∧ row < 9 ∧ 0 ≤ col ∧ col < 9 then
    some ⟨(row * 9 + col).toNat, by omega⟩
  else none

/-- Promotion zone (`in_promotion_zone`): the three far ranks. -/
def inZone : Color → Nat → Bool
  | .black, row => row ≤ 2
  | .white, row => row ≥ 6

/-- A piece of this colour and type standing on `row` could never move again
    (`forced_promotion`): pawn/lance on the last rank, knight on the last two. -/
def deadRow : Color → PieceType → Nat → Bool
  | .black, .pawn, r | .black, .lance, r => r == 0
  | .black, .knight, r => r ≤ 1
  | .white, .pawn, r | .white, .lance, r => r == 8
  | .white, .knight, r => r ≥ 7
  | _, _, _ => false

/-- A move. Drops name the piece type; normal moves say whether they promote. -/
inductive Move where
  | normal (src dst : Square) (promote : Bool)
  | drop (type : PieceType) (dst : Square)
  deriving DecidableEq, Repr

def Move.dst : Move → Square
  | .normal _ d _ => d
  | .drop _ d => d

end Shogi
