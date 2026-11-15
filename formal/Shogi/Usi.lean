/-
  USI move text, matching `shogi_parse_usi_move` / `shogi_move_to_usi`.
  Parsing is purely syntactic (legality is checked separately). A file
  digit `f` and a rank letter `r` give the square `(r - 'a') * 9 + (9 - f)`.
-/
import Shogi.Basic

namespace Shogi.Usi

def square? (file rank : Char) : Option Square :=
  if '1' ≤ file && file ≤ '9' && 'a' ≤ rank && rank ≤ 'i' then
    Square.mk? (rank.toNat - 'a'.toNat) (9 - (file.toNat - '0'.toNat))
  else none

def dropType? : Char → Option PieceType
  | 'P' => some .pawn | 'L' => some .lance | 'N' => some .knight
  | 'S' => some .silver | 'G' => some .gold | 'B' => some .bishop
  | 'R' => some .rook
  | _ => none

/-- Same branch structure as the C: length 4 with `*` second is a drop. -/
def parseChars : List Char → Option Move
  | [a, b, c, d] =>
    if b == '*' then do
      let t ← dropType? a
      let sq ← square? c d
      pure (.drop t sq)
    else do
      let s ← square? a b
      let sq ← square? c d
      pure (.normal s sq false)
  | [a, b, c, d, e] =>
    if e == '+' then do
      let s ← square? a b
      let sq ← square? c d
      pure (.normal s sq true)
    else none
  | _ => none

def parse (s : String) : Option Move := parseChars s.toList

def fileChar (s : Square) : Char := Char.ofNat ('0'.toNat + (9 - s.col))
def rankChar (s : Square) : Char := Char.ofNat ('a'.toNat + s.row)

def dropLetter : PieceType → Option Char
  | .pawn => some 'P' | .lance => some 'L' | .knight => some 'N'
  | .silver => some 'S' | .gold => some 'G' | .bishop => some 'B'
  | .rook => some 'R'
  | _ => none

/-- `shogi_move_to_usi`; `none` for a drop of a non-hand piece type. -/
def printChars : Move → Option (List Char)
  | .drop t d => (dropLetter t).map fun l => [l, '*', fileChar d, rankChar d]
  | .normal s d pr =>
    some ([fileChar s, rankChar s, fileChar d, rankChar d] ++ (if pr then ['+'] else []))

def print (m : Move) : Option String := (printChars m).map String.ofList

theorem square_fileRank : ∀ s : Square, square? (fileChar s) (rankChar s) = some s := by
  decide

theorem rankChar_ne_star : ∀ s : Square, (rankChar s == '*') = false := by decide

theorem dropType_letter : ∀ i : Fin 7,
    ((dropLetter (PieceType.ofHandIndex i)).bind dropType?) = some (PieceType.ofHandIndex i) := by
  decide

/-- Every printable move parses back to itself. -/
theorem parse_print (m : Move) (h : (printChars m).isSome) :
    (printChars m).bind parseChars = some m := by
  cases m with
  | normal s d pr =>
    cases pr <;>
      simp [printChars, parseChars, rankChar_ne_star, square_fileRank, bind, Option.bind]
  | drop t d =>
    cases t <;> simp_all [printChars, dropLetter, parseChars, dropType?, square_fileRank,
      bind, Option.bind]

end Shogi.Usi
