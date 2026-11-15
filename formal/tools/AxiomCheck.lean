/- Run with `lake env lean tools/AxiomCheck.lean`; tools/axiomcheck.sh fails
   if any theorem depends on an axiom other than propext, Classical.choice,
   Quot.sound (in particular `sorryAx` or `Lean.ofReduceBool`). -/
import Shogi
#print axioms Shogi.Usi.parse_print
#print axioms Shogi.Usi.square_fileRank
#print axioms Shogi.PieceType.handIndex_ofHandIndex
#print axioms Shogi.PieceType.unpromote_promote
#print axioms Shogi.Position.legalMoves_iff
#print axioms Shogi.Position.legalAux_stable
#print axioms Shogi.Position.legalMoves_safe
#print axioms Shogi.Position.legalMoves_target
#print axioms Shogi.Position.legalMoves_forced
#print axioms Shogi.Position.legalMoves_drop
#print axioms Shogi.Position.reachable_inv
#print axioms Shogi.Position.reachable_kings
#print axioms Shogi.RuleTests.perft1
