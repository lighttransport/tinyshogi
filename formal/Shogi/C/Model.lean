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

theorem encode_length (p : Position) : (encode p).length = 114 := by
  simp [encode, Gen.off_side, Gen.off_king_square, le32]

/-- The 12 implementation-only bytes of `ShogiPosition` (move_number, hash).
    The rules core never reads them, so the R2 proofs keep them parametric:
    `encode p` is `encodeW p` with zeros. -/
def encodeW (p : Position) (w : List UInt8) : Block :=
  (encode p).take 100 ++ w ++ (encode p).drop 112

theorem encodeW_length (p : Position) {w : List UInt8} (hw : w.length = 12) :
    (encodeW p w).length = 114 := by
  simp [encodeW, encode_length p, hw]

def posBlock : Nat := 1

def tablesMem : Mem := fun b => (Gen.globals.find? (·.1 == b)).map (·.2)

/-- Position pointer at an arbitrary block. Proofs bind `posBlock` as a variable
    and use `posPtr' posBlock`; the harness pins it to 1 via `posPtr`. -/
def posPtr' (pb : Nat) : Val := .ptr pb 0

def memOf (p : Position) : Mem := tablesMem.upd posBlock (encode p)

def posPtr : Val := .ptr posBlock 0

def runC (fuel f : Nat) (args : List Val) (m : Mem) : Option (Option Val) :=
  retOf (callFunc Gen.prog fuel f args m)

end Shogi.C

namespace Shogi.C
open MiniC

/-- Allocator block (E5): the next fresh block number. -/
def allocBlock : List UInt8 := encodeLE 8 1000000

/-- Output buffer for `ShogiMove moves[7200]`. -/
def movesBlock : Nat := 2

def memWithMoves (p : Position) : Mem :=
  ((memOf p).upd 0 allocBlock).upd movesBlock (List.replicate (7200 * 5) 0)

/-- Decode `ShogiMove {from, to, piece, promote, drop}` to a spec move. -/
def decodeMove (bs : List UInt8) : Option Move := do
  let fr := (bs.getD 0 0).toNat
  let to := (bs.getD 1 0).toNat
  let pr := (bs.getD 3 0).toNat
  let dr := (bs.getD 4 0).toNat
  if h : to < 81 then
    if fr == 255 then
      let t ← PieceType.ofCode dr
      pure (.drop t ⟨to, h⟩)
    else if h2 : fr < 81 then pure (.normal ⟨fr, h2⟩ ⟨to, h⟩ (pr != 0))
    else none
  else none

/-- Run `shogi_generate_legal_mut` in MiniC and decode its moves
    (`none` on UB, time-out or an undecodable move). -/
def miniLegal (fuel : Nat) (p : Position) : Option (List Move) :=
  match callFunc Gen.prog fuel Gen.fid_shogi_generate_legal_mut
      [posPtr, .ptr movesBlock 0, .int IntTy.u64 7200] (memWithMoves p) with
  | .ok (some (.int _ n), m) =>
    match m movesBlock with
    | some blk => ((List.range n).mapM fun i => decodeMove ((blk.drop (5 * i)).take 5))
    | none => none
  | _ => none

end Shogi.C

namespace Shogi.C
open MiniC

/-- The whole `ShogiPosition` (all 41088 bytes): board, hands, side and
    move number; hash, king squares and history are left for the translated
    `reset_history` to fill, exactly as `shogi_position_from_sfen` does. -/
def encodeFull (p : Position) : List UInt8 :=
  let pre := (encode p).take Gen.off_move_number
  let withMn := pre ++ List.replicate (Gen.off_move_number - pre.length) 0 ++ le32 p.moveNumber
  withMn ++ List.replicate (Gen.sizeof_ShogiPosition - withMn.length) 0

def moveBlock : Nat := 3

/-- `ShogiMove` bytes for a spec move, as the C legal generator emits it
    (`piece` = the moving piece byte, 0 for drops). -/
def moveBytes (p : Position) : Move → List UInt8
  | .normal s d pr => [s.val.toUInt8, d.val.toUInt8, pieceByte (p.pieceAt s), if pr then 1 else 0, 0]
  | .drop t d => [255, d.val.toUInt8, 0, 0, t.code.toUInt8]

def decodeAt (blk : List UInt8) (o n : Nat) : Nat := decodeLE ((blk.drop o).take n)

/-- Read back board/hands/side/move number (as a spec position) and the hash. -/
def decodeFull (blk : List UInt8) : Option (Position × Nat) := do
  let board ← (List.range 81).mapM fun i =>
    let b := (blk.getD i 0).toNat
    if b == 0 then some none
    else do
      let t ← PieceType.ofCode (b % 16)
      some (some ⟨if b / 16 % 2 == 1 then Color.white else Color.black, t⟩)
  let hb := (List.range 7).map fun i => (blk.getD (Gen.off_hand + i) 0).toNat
  let hw := (List.range 7).map fun i => (blk.getD (Gen.off_hand + 7 + i) 0).toNat
  let side := if decodeAt blk Gen.off_side 4 == 1 then Color.white else Color.black
  pure ({ board, hands := ⟨hb, hw⟩, side, moveNumber := decodeAt blk Gen.off_move_number 4 },
        decodeAt blk Gen.off_hash 8)

/-- `reset_history` then `shogi_make_move` in MiniC. -/
def miniMake (fuel : Nat) (p : Position) (m : Move) : Option (Position × Nat) :=
  let mem0 := ((tablesMem.upd 0 allocBlock).upd posBlock (encodeFull p)).upd moveBlock (moveBytes p m)
  match callFunc Gen.prog fuel Gen.fid_reset_history [posPtr] mem0 with
  | .ok (_, mem1) =>
    match callFunc Gen.prog fuel Gen.fid_shogi_make_move [posPtr, .ptr moveBlock 0] mem1 with
    | .ok (some (.int _ 1), mem2) => (mem2 posBlock).bind decodeFull
    | _ => none
  | _ => none

end Shogi.C

namespace Shogi.C
open MiniC

/-- The live state of a `ShogiPosition` block: everything up to and
    including the king squares, the history length, and the history
    entries below it. -/
def activeState (blk : List UInt8) : List UInt8 × List UInt8 :=
  let n := decodeAt blk Gen.off_history_length 8
  (blk.take (Gen.off_king_square + 2) ++ (blk.drop Gen.off_history_length).take 8,
   (blk.drop Gen.off_history).take (8 * n) ++ (blk.drop Gen.off_history_mover).take n ++
     (blk.drop Gen.off_history_check).take n)

def undoBlock : Nat := 4

/-- `make_move_undo{,_fast}` then `unmake_move` restore the live state. -/
def miniUndoRoundTrip (fuel : Nat) (fast : Bool) (p : Position) (m : Move) : Option Bool :=
  let mem0 := (((tablesMem.upd 0 allocBlock).upd posBlock (encodeFull p)).upd moveBlock
    (moveBytes p m)).upd undoBlock (List.replicate Gen.sizeof_ShogiUndo 0)
  let mk := if fast then Gen.fid_shogi_make_move_undo_fast else Gen.fid_shogi_make_move_undo
  match callFunc Gen.prog fuel Gen.fid_reset_history [posPtr] mem0 with
  | .ok (_, mem1) =>
    match callFunc Gen.prog fuel mk [posPtr, .ptr moveBlock 0, .ptr undoBlock 0] mem1 with
    | .ok (some (.int _ 1), mem2) =>
      match callFunc Gen.prog fuel Gen.fid_shogi_unmake_move [posPtr, .ptr undoBlock 0] mem2 with
      | .ok (some (.int _ 1), mem3) => do
        let a ← mem1 posBlock
        let b ← mem3 posBlock
        pure (activeState a == activeState b)
      | _ => none
    | _ => none
  | _ => none

end Shogi.C
