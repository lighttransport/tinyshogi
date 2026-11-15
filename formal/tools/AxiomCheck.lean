/- Run with `lake env lean tools/AxiomCheck.lean`; tools/axiomcheck.sh fails
   if any theorem depends on an axiom other than propext, Classical.choice,
   Quot.sound (in particular `sorryAx` or `Lean.ofReduceBool`). -/
import Shogi
#print axioms Shogi.Usi.parse_print
#print axioms Shogi.Usi.square_fileRank
#print axioms Shogi.PieceType.handIndex_ofHandIndex
#print axioms Shogi.PieceType.unpromote_promote
