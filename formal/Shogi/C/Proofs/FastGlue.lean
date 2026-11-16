/-
  T8: the C fast-path test, read on the `KingSafety` record, implies the
  hypotheses of `fastpath_sound`.
-/
import Shogi.C.Proofs.Geom2

namespace Shogi.C.Proofs
open MiniC Shogi Shogi.C Shogi.Tables

/-- `needs_probe` as the C computes it from the record and the move. -/
def needsProbeC (R : List UInt8) (p : Position) (mv : Move) : Bool :=
  match mv with
  | .drop .. => true
  | .normal s d _ =>
    R.getD 1 0 == 0 || R.getD 2 0 != 0 ||
      (match p.pieceAt s with | some pc => pc.type == .king | none => false) ||
      (R.getD (3 + s.val) 0 != 0 &&
        !(match p.kingSquare p.side with | some k => sameKingRay k s d | none => false))

/-- **The C may skip the probe only for legal moves.** If `needs_probe` is
    false for a pseudo-legal move, the move does not leave the king in check. -/
theorem skip_sound (p : Position) (hS : p.Shaped) (hK : KingsUnique p) (mv : Move) (hm : mv ∈ p.pseudoMoves)
    (hskip : needsProbeC (ksRec p p.side) p mv = false) :
    (p.play mv).inCheck p.side = false := by
  cases mv with
  | drop t d => simp [needsProbeC] at hskip
  | normal sq d pr =>
    simp only [needsProbeC, Bool.or_eq_false_iff] at hskip
    obtain ⟨⟨⟨hv, hc⟩, hkt⟩, hpin⟩ := hskip
    obtain ⟨hval, hkb⟩ := ksRec_valid p p.side
    cases hks : p.kingSquare p.side with
    | none => rw [hval, hks] at hv; simp at hv
    | some k =>
      obtain ⟨pc, hpc, _, _⟩ := pseudo_normal hm
      have hnc : p.inCheck p.side = false := by
        have := ksRec_inCheck p p.side
        rw [this] at hc; cases h : p.inCheck p.side <;> simp_all
      have hkt' : pc.type ≠ .king := by
        rw [hpc] at hkt; simpa using hkt
      apply fastpath_sound p hS hK hm hpc hkt' hks hnc
      have hpb := ksRec_pinned p p.side k sq hks
      rw [hpb, hks] at hpin
      cases h : pinnedSpec p p.side k sq
      · left; rfl
      · right; simp [h] at hpin; exact hpin

end Shogi.C.Proofs
