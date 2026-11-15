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

/-- `strtok_r` with the delimiter set `" \t\r\n"`. -/
def fields (cs : List Char) : List (List Char) :=
  (cs.splitBy (fun a b => isSpace a == isSpace b)).filter
    (fun g => match g with | c :: _ => !isSpace c | [] => false)

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

/-- Read a run of digits, failing as soon as the count exceeds 18. -/
def readCount : List Char → Nat → Option (Nat × List Char)
  | c :: cs, n =>
    if isDigit c then
      let n' := n * 10 + digitVal c
      if n' > 18 then none else readCount cs n'
    else some (n, c :: cs)
  | [], n => some (n, [])

/-- `parse_sfen_hands` after the `"-"` case. -/
def parseHandsAux : (fuel : Nat) → List Char → Hands → Option Hands
  | 0, _, _ => none
  | _ + 1, [], h => some h
  | fuel + 1, cs, h =>
    match readCount cs 0 with
    | none => none
    | some (_, []) => none     -- the letter would be the terminating NUL
    | some (count, c :: rest) =>
      let color := if isUpper c then Color.black else Color.white
      match handLetter? (toLower c) with
      | none => none
      | some t =>
        match t.handIndex with
        | none => none
        | some i =>
          let count := if count == 0 then 1 else count
          let cur := h.get color i
          if cur + count > 18 then none
          else parseHandsAux fuel rest (h.set color i (cur + count))

def parseHands (cs : List Char) : Option Hands :=
  if cs == ['-'] then some Hands.empty else parseHandsAux (cs.length + 1) cs Hands.empty

/-! ## Move number: `strtoul(s, &end, 10)` then range checks -/

def ulongMax : Nat := 2 ^ 64 - 1
def uintMax : Nat := 2 ^ 32 - 1

def digitsVal : List Char → Nat → Nat
  | [], n => n
  | c :: cs, n => digitsVal cs (n * 10 + digitVal c)

/-- Value of the whole field under `strtoul`, or `none` if `*end != '\0'`. -/
def strtoulField (cs : List Char) : Option Nat :=
  let (neg, ds) := match cs with
    | '+' :: r => (false, r)
    | '-' :: r => (true, r)
    | r => (false, r)
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

/-- Decimal digits of `n` (structural, so the kernel can evaluate it). -/
def natDigits : (fuel n : Nat) → List Char
  | 0, _ => []
  | fuel + 1, n =>
    if n < 10 then [Char.ofNat ('0'.toNat + n)]
    else natDigits fuel (n / 10) ++ [Char.ofNat ('0'.toNat + n % 10)]

def showNat (n : Nat) : List Char := natDigits 20 n

def pieceChars (pc : Piece) : List Char :=
  let l := pc.type.letter
  (if pc.type.isPromoted then ['+'] else []) ++
    [if pc.color == .black then toUpper l else l]

def rowChars : List (Option Piece) → Nat → List Char
  | [], e => if e > 0 then [Char.ofNat ('0'.toNat + e)] else []
  | none :: r, e => rowChars r (e + 1)
  | some pc :: r, e =>
    (if e > 0 then [Char.ofNat ('0'.toNat + e)] else []) ++ pieceChars pc ++ rowChars r 0

def boardChars (b : List (Option Piece)) : List Char :=
  let rows := (List.range 9).map fun r => (b.drop (r * 9)).take 9
  ((rows.map (rowChars · 0)).intersperse ['/']).flatten

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
