/-
  Kernel-checked rule fixtures (`decide +kernel`: evaluation by the kernel,
  no extra axioms). Each takes 5–25 s, so this file holds only one case per
  rule; perft 2 and deeper are compiled-code tests in tools/cdiff.py
  (see PLAN.md T4).
-/
import Shogi.Sfen
import Shogi.Usi
import Shogi.Rules

namespace Shogi.RuleTests
open Position

/-- Is the USI move legal in the SFEN position? (`none` if either fails to parse.) -/
def legalIn (sfen usi : String) : Option Bool := do
  let p ← Sfen.parse sfen
  let m ← Usi.parse usi
  pure (p.legalMoves.contains m)

/-- perft 1 from the start position. -/
theorem perft1 : Position.start.legalMoves.length = 30 := by decide +kernel

/-- Uchifuzume: P*5b mates, so it is illegal (tests/test_rules.c). -/
example : legalIn "4k4/9/2NG1GN2/9/9/9/9/9/4K4 b P 1" "P*5b" = some false := by decide +kernel

/-- A pawn-drop check that is not mate is legal. -/
example : legalIn "4k4/9/3G5/9/9/9/9/9/4K4 b P 1" "P*5b" = some true := by decide +kernel

/-- Nifu: a second unpromoted pawn on file 5. -/
example : legalIn "4k4/9/9/9/4P4/9/9/9/4K4 b P 1" "P*5c" = some false := by decide +kernel

/-- Dead drop: a knight cannot be dropped on the last two ranks. -/
example : legalIn "4k4/9/9/9/9/9/9/9/4K4 b N 1" "N*1b" = some false := by decide +kernel

/-- A pinned rook may not leave the pin line. -/
example : legalIn "4r3k/9/9/9/9/9/9/4R4/4K4 b - 1" "5h4h" = some false := by decide +kernel

/-- Forced promotion: a pawn reaching the last rank must promote. -/
example : legalIn "4k4/2P6/9/9/9/9/9/9/4K4 b - 1" "7b7a" = some false := by decide +kernel
example : legalIn "4k4/2P6/9/9/9/9/9/9/4K4 b - 1" "7b7a+" = some true := by decide +kernel

end Shogi.RuleTests

namespace Shogi.RuleTests
/-- Uchifuzume where the pawn's only capturer is pinned (found by
    tools/cdiff.py --oracle; python-shogi 1.1.1 wrongly allows it). -/
example : legalIn "9/9/gN7/P3+s4/4+p4/3g1L+s1p/k1p5p/3+PPP3/KG2r4 w 3pSs2P 45" "P*9h"
    = some false := by decide +kernel
end Shogi.RuleTests
