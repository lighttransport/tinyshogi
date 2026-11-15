/-
  SFEN parsing and printing, written to agree exactly with
  `shogi_position_from_sfen` / `shogi_position_to_sfen` in `src/shogi.c`,
  including its tolerances:

  * fields are separated by runs of ' ', '\t', '\r', '\n'; exactly four fields;
  * the input must be shorter than 512 bytes;
  * the board may contain dead pieces (e.g. a pawn on its last rank); this is
    an analysis-position format, and the legality rules never create them;
  * a hand count of `0` means 1; counts accumulate (`1R1r` = `Rr`) up to 18;
  * exactly one king per side; no family exceeds a full set;
  * the move number is read with C `strtoul(…, 10)` semantics (optional sign,
    saturation to `ULONG_MAX`) and must be in `[1, UINT_MAX]`.

  The domain is strings without NUL characters (the C side receives a
  NUL-terminated string).
-/
import Shogi.Position

namespace Shogi.Sfen

open Position

def isSpace (c : Char) : Bool := c == ' ' || c == '\t' || c == '\r' || c == '\n'
def isDigit (c : Char) : Bool := '0' ≤ c && c ≤ '9'
def digitVal (c : Char) : Nat := c.toNat - '0'.toNat
def isUpper (c : Char) : Bool := 'A' ≤ c && c ≤ 'Z'
def toLower (c : Char) : Char := if isUpper c then Char.ofNat (c.toNat + 32) else c
def toUpper (c : Char) : Char :=
  if 'a' ≤ c && c ≤ 'z' then Char.ofNat (c.toNat - 32) else c

/-- `strtok_r` with the delimiter set `" \t\r\n"`: maximal runs of
    non-delimiters, in order (`cur` is the token being read, reversed). -/
def tokens : List Char → List Char → List (List Char)
  | [], cur => if cur.isEmpty then [] else [cur.reverse]
  | c :: cs, cur =>
    if isSpace c then (if cur.isEmpty then tokens cs [] else cur.reverse :: tokens cs [])
    else tokens cs (c :: cur)

def fields (cs : List Char) : List (List Char) := tokens cs []

/-! ## Board -/

structure BoardSt where
  row : Nat
  col : Nat
  promoted : Bool
  board : List (Option Piece)

/-- `parse_sfen_board`. -/
def parseBoard : List Char → BoardSt → Option (List (Option Piece))
  | [], st => if st.row == 8 && st.col == 9 && !st.promoted then some st.board else none
  | c :: cs, st =>
    if c == '/' then
      if st.col != 9 || st.row ≥ 8 || st.promoted then none
      else parseBoard cs { st with row := st.row + 1, col := 0 }
    else if c == '+' then
      if st.promoted || st.col ≥ 9 then none
      else parseBoard cs { st with promoted := true }
    else if isDigit c then
      let n := digitVal c
      if n < 1 || n > 9 || st.promoted || st.col + n > 9 then none
      else parseBoard cs { st with col := st.col + n }
    else
      let color := if isUpper c then Color.black else Color.white
      match PieceType.ofLetter (toLower c) with
      | none => none
      | some t =>
        if st.row ≥ 9 || st.col ≥ 9 then none
        else if st.promoted && !t.canPromote then none
        else
          let t' := if st.promoted then t.promote else t
          parseBoard cs { st with
            col := st.col + 1, promoted := false,
            board := st.board.set (st.row * 9 + st.col) (some ⟨color, t'⟩) }

/-! ## Hands -/

/-- Hand letters exclude the king. -/
def handLetter? (c : Char) : Option PieceType :=
  match PieceType.ofLetter c with
  | some .king => none
  | t => t

/-- `parse_sfen_hands` after the `"-"` case, one character at a time.
    `pend` is the count read so far (`none`: no digit since the last letter).
    A count above 18 fails at once; a count of 0 means 1; input ending in
    digits fails (the C would read the terminating NUL as the letter). -/
def handsGo : List Char → Option Nat → Hands → Option Hands
  | [], none, h => some h
  | [], some _, _ => none
  | c :: cs, pend, h =>
    if isDigit c then
      let n := pend.getD 0 * 10 + digitVal c
      if n > 18 then none else handsGo cs (some n) h
    else
      let color := if isUpper c then Color.black else Color.white
      match handLetter? (toLower c) with
      | none => none
      | some t =>
        match t.handIndex with
        | none => none
        | some i =>
          let count := match pend with | none => 1 | some 0 => 1 | some n => n
          let cur := h.get color i
          if cur + count > 18 then none else handsGo cs none (h.set color i (cur + count))

def parseHands (cs : List Char) : Option Hands :=
  if cs == ['-'] then some Hands.empty else handsGo cs none Hands.empty

/-! ## Move number: `strtoul(s, &end, 10)` then range checks -/

def ulongMax : Nat := 2 ^ 64 - 1
def uintMax : Nat := 2 ^ 32 - 1

def digitsVal : List Char → Nat → Nat
  | [], n => n
  | c :: cs, n => digitsVal cs (n * 10 + digitVal c)

/-- Optional sign: (negative?, rest). -/
def signSplit : List Char → Bool × List Char
  | '+' :: r => (false, r)
  | '-' :: r => (true, r)
  | r => (false, r)

/-- Value of the whole field under `strtoul`, or `none` if `*end != '\0'`. -/
def strtoulField (cs : List Char) : Option Nat :=
  let neg := (signSplit cs).1
  let ds := (signSplit cs).2
  if ds.isEmpty || !ds.all isDigit then none
  else
    let v := digitsVal ds 0
    if v > ulongMax then some ulongMax
    else if neg then some ((2 ^ 64 - v) % 2 ^ 64)
    else some v

def parseMoveNumber (cs : List Char) : Option Nat :=
  match strtoulField cs with
  | some n => if n == 0 || n > uintMax then none else some n
  | none => none

/-! ## Whole SFEN -/

def parseChars (cs : List Char) : Option Position := do
  match fields cs with
  | [b, s, h, n] =>
    let side ← (if s == ['b'] then some Color.black else if s == ['w'] then some Color.white
                else none)
    let board ← parseBoard b ⟨0, 0, false, emptyBoard⟩
    let hands ← parseHands h
    let mn ← parseMoveNumber n
    let p : Position := { board, hands, side, moveNumber := mn }
    if p.kingCount .black != 1 || p.kingCount .white != 1 then none
    else if !p.materialOk then none
    else some p
  | _ => none

/-- `shogi_position_from_sfen`. -/
def parse (s : String) : Option Position :=
  if s.utf8ByteSize ≥ 512 then none else parseChars s.toList

/-! ## Printing (`write_sfen`) -/

/-- The decimal digit character for `d < 10`. -/
def digitChar : Nat → Char
  | 0 => '0' | 1 => '1' | 2 => '2' | 3 => '3' | 4 => '4'
  | 5 => '5' | 6 => '6' | 7 => '7' | 8 => '8' | _ => '9'

/-- Decimal digits of `n` (structural, so the kernel can evaluate it). -/
def natDigits : (fuel n : Nat) → List Char
  | 0, _ => []
  | fuel + 1, n =>
    if n < 10 then [digitChar n]
    else natDigits fuel (n / 10) ++ [digitChar (n % 10)]

def showNat (n : Nat) : List Char := natDigits 20 n

def pieceChars (pc : Piece) : List Char :=
  let l := pc.type.letter
  (if pc.type.isPromoted then ['+'] else []) ++
    [if pc.color == .black then toUpper l else l]

def rowChars : List (Option Piece) → Nat → List Char
  | [], e => if e > 0 then [digitChar e] else []
  | none :: r, e => rowChars r (e + 1)
  | some pc :: r, e =>
    (if e > 0 then [digitChar e] else []) ++ pieceChars pc ++ rowChars r 0

def boardRow (b : List (Option Piece)) (r : Nat) : List (Option Piece) := (b.drop (r * 9)).take 9

/-- Rows `r, r+1, …` (`k` of them), separated by `/`. -/
def rowsChars (b : List (Option Piece)) (r : Nat) : Nat → List Char
  | 0 => []
  | 1 => rowChars (boardRow b r) 0
  | k + 2 => rowChars (boardRow b r) 0 ++ '/' :: rowsChars b (r + 1) (k + 1)

def boardChars (b : List (Option Piece)) : List Char := rowsChars b 0 9

/-- Hand print order R B G S N L P (slots 6 5 4 3 2 1 0). -/
def handOrder : List (Fin 7) := [6, 5, 4, 3, 2, 1, 0]

def handChars (p : Position) (c : Color) : List Char :=
  handOrder.flatMap fun i =>
    let n := p.hand c i
    if n == 0 then []
    else (if n > 1 then showNat n else []) ++
      [if c == .black then toUpper (PieceType.ofHandIndex i).letter
       else (PieceType.ofHandIndex i).letter]

def handsChars (p : Position) : List Char :=
  let hs := handChars p .black ++ handChars p .white
  if hs.isEmpty then ['-'] else hs

def printChars (p : Position) : List Char :=
  boardChars p.board ++ [' ', if p.side == .black then 'b' else 'w', ' '] ++
    handsChars p ++ [' '] ++ showNat p.moveNumber

def print (p : Position) : String := String.ofList (printChars p)

end Shogi.Sfen
