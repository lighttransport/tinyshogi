/- Lean side of tools/cdiff.py: same protocol as tools/cdiff_c.c. -/
import Shogi.Sfen

def hexVal (c : Char) : Nat :=
  if '0' ≤ c && c ≤ '9' then c.toNat - '0'.toNat else c.toNat - 'a'.toNat + 10

def decodeHex : List Char → List UInt8
  | a :: b :: r => (hexVal a * 16 + hexVal b).toUInt8 :: decodeHex r
  | _ => []

partial def loop (h : IO.FS.Stream) (o : IO.FS.Stream) : IO Unit := do
  let line ← h.getLine
  if line.isEmpty then return
  let bytes := ByteArray.mk (decodeHex (line.toList.filter (· != (Char.ofNat 10)))).toArray
  let res := match String.fromUTF8? bytes with
    | some s => (Shogi.Sfen.parse s).map Shogi.Sfen.print
    | none => none   -- invalid UTF-8: compared separately (see cdiff.py)
  o.putStrLn (res.getD "REJECT")
  loop h o

def main : IO Unit := do loop (← IO.getStdin) (← IO.getStdout)
