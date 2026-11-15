/- Lean side of tools/cdiff.py: same protocol as tools/cdiff_c.c. -/
import Shogi.Sfen
import Shogi.Usi
import Shogi.Rules
import Shogi.Game

open Shogi

def hexVal (c : Char) : Nat :=
  if '0' ≤ c && c ≤ '9' then c.toNat - '0'.toNat else c.toNat - 'a'.toNat + 10

def decodeHex : List Char → List UInt8
  | a :: b :: r => (hexVal a * 16 + hexVal b).toUInt8 :: decodeHex r
  | _ => []

/-- Split at the last `|`. -/
def splitArg (s : String) : String × String :=
  let cs := s.toList
  match (cs.reverse.findIdx? (· == '|')) with
  | some i => (String.ofList (cs.take (cs.length - 1 - i)),
               String.ofList (cs.drop (cs.length - i)))
  | none => (s, "")

def usiOf (m : Move) : String := (Usi.print m).getD "?"

def insertSorted (x : String) : List String → List String
  | [] => [x]
  | y :: ys => if decide (x < y) then x :: y :: ys else y :: insertSorted x ys

def sortStrings (xs : List String) : List String := xs.foldr insertSorted []

def sameMove (a b : Move) : Bool := a == b

def answer (cmd : Char) (payload : String) : String :=
  if cmd == 'S' then ((Sfen.parse payload).map Sfen.print).getD "REJECT" else
  let (sfen, arg) := splitArg payload
  match Sfen.parse sfen with
  | none => "REJECT"
  | some p =>
    if cmd == 'L' then " ".intercalate (sortStrings (p.legalMoves.map usiOf))
    else if cmd == 'M' then
      match Usi.parse arg with
      | some m => match (Game.init p).play m with
        | some g => Sfen.print g.pos
        | none => "ILLEGAL"
      | none => "ILLEGAL"
    else if cmd == 'G' then
      let moves := (arg.splitOn " ").filter (· != "")
      let rec go : List String → Nat → Game → String
        | [], _, g =>
          let r := match g.result with
            | .ongoing => "ONGOING" | .blackWin => "BLACK" | .whiteWin => "WHITE" | .draw => "DRAW"
          r ++ " " ++ Sfen.print g.pos
        | u :: us, i, g =>
          match (Usi.parse u).bind g.play with
          | some g' => go us (i + 1) g'
          | none => "ILLEGAL " ++ toString i
      go moves 0 (Game.init p)
    else if cmd == 'P' then toString (Position.perft arg.toNat! p)
    else "BADCMD"

partial def loop (h : IO.FS.Stream) (o : IO.FS.Stream) : IO Unit := do
  let line ← h.getLine
  if line.isEmpty then return
  let cs := line.toList.filter (· != Char.ofNat 10)
  let cmd := cs.headD ' '
  let bytes := ByteArray.mk (decodeHex (cs.drop 2)).toArray
  let res := match String.fromUTF8? bytes with
    | some s => answer cmd s
    | none => "REJECT"   -- C rejects every non-ASCII byte in every field
  o.putStrLn res
  o.flush
  loop h o

def main : IO Unit := do loop (← IO.getStdin) (← IO.getStdout)
