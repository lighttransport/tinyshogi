/-
  Kernel-checked regression tests. Every `example` is decided by the kernel,
  so a wrong verdict fails `lake build`. Cases mirror `tests/test_rules.c`
  and `fuzz/corpus/`.
-/
import Shogi.Sfen
import Shogi.Usi

namespace Shogi.Tests
set_option maxRecDepth 100000
open Sfen

def startSfen := "lnsgkgsnl/1r5b1/ppppppppp/9/9/9/PPPPPPPPP/1B5R1/LNSGKGSNL b - 1"

/-- `shogi_position_start` agrees with the standard start SFEN. -/
example : parse startSfen = some Position.start := by decide
example : print Position.start = startSfen := by decide

/-- Round trip via print, as `test_rules.c` "SFEN roundtrip". -/
def rt (s : String) : Option String := (parse s).map print

example : rt "lnsgkgsnl/1r5b1/ppppppppp/9/9/2P6/PP1PPPPPP/1B5R1/LNSGKGSNL w - 2"
    = some "lnsgkgsnl/1r5b1/ppppppppp/9/9/2P6/PP1PPPPPP/1B5R1/LNSGKGSNL w - 2" := by decide

/-- Counts accumulate and are normalised; both hands, black first. -/
example : rt "4k4/9/9/9/9/9/9/9/4K4 b 1R1r 1" = some "4k4/9/9/9/9/9/9/9/4K4 b Rr 1" := by decide
example : rt "4k4/9/9/9/9/9/9/9/4K4 w 1R1r 2" = some "4k4/9/9/9/9/9/9/9/4K4 w Rr 2" := by decide
example : rt "4k4/9/9/9/9/9/9/9/4K4 b S2Pb3p 1" = some "4k4/9/9/9/9/9/9/9/4K4 b S2Pb3p 1" := by
  decide

/-- Material limits (`validate_material`). -/
example : parse "3RRR3/9/9/9/4k4/9/9/9/4K4 b - 1" = none := by decide
example : (parse "1+R2+R4/9/9/9/4k4/9/9/9/4K4 b - 1").isSome := by decide
example : (parse "1+B2+B4/9/9/9/4k4/9/9/9/4K4 b - 1").isSome := by decide
example : parse "1R2R4/9/9/9/4k4/9/9/9/4K4 b r 1" = none := by decide
example : parse "1+R2+R4/9/9/9/4k4/9/9/9/4K4 b 3R 1" = none := by decide

/-- Gold cannot be promoted; an unpromoted gold on the last rank is accepted. -/
example : (parse "4k4/G8/9/9/9/9/9/9/4K4 b - 1").isSome := by decide
example : parse "4k4/+G8/9/9/9/9/9/9/4K4 b - 1" = none := by decide

/-- Kings: exactly one per side. -/
example : parse "9/9/9/9/9/9/9/9/4K4 b - 1" = none := by decide
example : parse "4k4/9/9/9/9/9/9/9/3KK4 b - 1" = none := by decide

/-- Field and number handling. -/
example : parse "4k4/9/9/9/9/9/9/9/4K4 b - 0" = none := by decide
example : parse "4k4/9/9/9/9/9/9/9/4K4 b - 1 extra" = none := by decide
example : parse "4k4/9/9/9/9/9/9/9/4K4 x - 1" = none := by decide
example : rt "  4k4/9/9/9/9/9/9/9/4K4\tb  -  +7 " = some "4k4/9/9/9/9/9/9/9/4K4 b - 7" := by decide
example : rt "4k4/9/9/9/9/9/9/9/4K4 b 0P 1" = some "4k4/9/9/9/9/9/9/9/4K4 b P 1" := by decide
example : parse "4k4/9/9/9/9/9/9/9/4K4 b 19P 1" = none := by decide
example : parse "4k4/9/9/9/9/9/9/9/4K4 b 2 1" = none := by decide
example : parse "4k4/9/9/9/9/9/9/9/4K4 b K 1" = none := by decide
example : parse "4k4/9/9/9/9/9/9/9/4K4 b - 4294967296" = none := by decide
example : rt "4k4/9/9/9/9/9/9/9/4K4 b - 4294967295"
    = some "4k4/9/9/9/9/9/9/9/4K4 b - 4294967295" := by decide

/-- USI. -/
example : Usi.parse "7g7f" = some (.normal ⟨56, by decide⟩ ⟨47, by decide⟩ false) := by decide
example : Usi.parse "P*5e" = some (.drop .pawn ⟨40, by decide⟩) := by decide
example : Usi.parse "8h2b+" = some (.normal ⟨64, by decide⟩ ⟨16, by decide⟩ true) := by decide
example : Usi.parse "K*5e" = none := by decide
example : Usi.parse "7g7f=" = none := by decide

end Shogi.Tests
