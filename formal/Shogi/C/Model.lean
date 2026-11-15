/-
  The abstraction between spec positions and C memory: the bytes of a
  `ShogiPosition` that represent a spec `Position`, and the MiniC memory in
  which the translated functions run (position block + const tables).

  Only the fields the rules core reads are encoded: `board`, `hand`, `side`,
  `king_square` (offsets measured by c2lean's probe, `Gen.off_*`). The block
  is the prefix of the struct up to and including `king_square`; an access
  beyond it is UB in the model (and would show up as a mismatch in cdiff).
-/
import Shogi.C.Gen
import MiniC.Fuel
import Shogi.Rules

namespace Shogi.C
open MiniC

def pieceByte : Option Piece → UInt8
  | none => 0
  | some pc => pc.code.toUInt8

def le32 (n : Nat) : List UInt8 :=
  [(n % 256).toUInt8, (n / 256 % 256).toUInt8, (n / 65536 % 256).toUInt8,
   (n / 16777216 % 256).toUInt8]

/-- `king_square[c]`: the king's square, or `SHOGI_SQ_NONE` (255). -/
def kingByte (p : Position) (c : Color) : UInt8 :=
  match p.kingSquare c with
  | some s => s.val.toUInt8
  | none => 255

/-- The encoded prefix of `ShogiPosition`. -/
def encode (p : Position) : List UInt8 :=
  let board := (List.finRange 81).map fun s => pieceByte (p.pieceAt s)
  let hand := (List.finRange 7).map (fun i => (p.hand .black i).toUInt8) ++
              (List.finRange 7).map (fun i => (p.hand .white i).toUInt8)
  let pre := board ++ hand
  let toSide := pre ++ List.replicate (Gen.off_side - pre.length) 0 ++ le32 p.side.idx
  let toKing := toSide ++ List.replicate (Gen.off_king_square - toSide.length) 0
  toKing ++ [kingByte p .black, kingByte p .white]

/-- Block holding the position. -/
def posBlock : Nat := 1

def tablesMem : Mem := fun b => (Gen.globals.find? (·.1 == b)).map (·.2)

def memOf (p : Position) : Mem := tablesMem.upd posBlock (encode p)

def posPtr : Val := .ptr posBlock 0

def runC (fuel f : Nat) (args : List Val) (m : Mem) : Option (Option Val) :=
  retOf (callFunc Gen.prog fuel f args m)

end Shogi.C
