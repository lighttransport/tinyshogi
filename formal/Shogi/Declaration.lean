/-
  Entering-king declaration (optional module), as implemented by
  `shogi_is_declaration_win`: the declaring side's king is in its promotion
  zone and not in check, at least 10 other own pieces are in the zone, and
  pieces in the zone plus pieces in hand score at least 28 (black) or 27
  (white) points, with bishop/rook (promoted or not) worth 5 and others 1.
-/
import Shogi.Rules

namespace Shogi.Position

def points (t : PieceType) : Nat :=
  match t.unpromote with
  | .bishop | .rook => 5
  | _ => 1

/-- Own non-king pieces in the promotion zone. -/
def campPieces (p : Position) (c : Color) : List PieceType :=
  (List.finRange 81).filterMap fun s =>
    match p.pieceAt s with
    | some pc => if pc.color == c && pc.type != .king && inZone c (Square.row s)
                 then some pc.type else none
    | none => none

def declarationPoints (p : Position) (c : Color) : Nat :=
  ((p.campPieces c).map points).sum +
    ((List.finRange 7).map fun i => p.hand c i * points (PieceType.ofHandIndex i)).sum

def declarationWin (p : Position) (c : Color) : Bool :=
  match p.kingSquare c with
  | none => false
  | some k =>
    inZone c (Square.row k) && !p.inCheck c && (p.campPieces c).length ≥ 10 &&
      p.declarationPoints c ≥ (if c == .black then 28 else 27)

end Shogi.Position
