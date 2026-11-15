/-
  The step-attack probe table describes exactly the spec's step attacks:
  for every attacker colour, target, source square and piece type, the piece
  attacks the target by one step iff the target's probe list holds that
  square with the type's bit set (tested as the C does,
  `mask & (1 << type) != 0`). Checked by kernel evaluation (~100 s per colour).
-/
import Shogi.Tables

namespace Shogi.Tables

def maskHas (mask : Nat) (t : PieceType) : Bool := mask &&& (1 <<< t.code) != 0

def probesAgree (c : Color) (t : Fin 81) : Bool :=
  let ps := probes c t
  (List.finRange 81).all fun s =>
    allTypes.all fun ty =>
      ((stepOffsets c.fwd ty).filterMap (Square.offset s)).contains t ==
        ps.any fun pr => pr.square == s.val && maskHas pr.mask ty

theorem probesAgree_black : ∀ t : Fin 81, probesAgree .black t = true := by decide +kernel
theorem probesAgree_white : ∀ t : Fin 81, probesAgree .white t = true := by decide +kernel

theorem probesAgree_all (c : Color) (t : Fin 81) : probesAgree c t = true := by
  cases c
  · exact probesAgree_black t
  · exact probesAgree_white t

/-- Probe squares are on the board, and masks fit in 16 bits. -/
theorem probes_bounds (c : Color) : ∀ t : Fin 81,
    (probes c t).all (fun pr => decide (pr.square < 81) && decide (pr.mask < 65536)) = true := by
  cases c <;> decide +kernel

end Shogi.Tables
