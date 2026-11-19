/-
  Headline end-to-end theorems for the C rules core.

  This is the layer where the spec invariants are discharged from
  `Position.Reachable` and the remaining `RecSpec` hypothesis of the entry
  points is replaced by `Proofs.RecSpec_discharge`. The statements here are
  about the *MiniC model* of `src/shogi.c`, for an arbitrary position block;
  the step to real 41088-byte `ShogiPosition` blocks is PLAN.md R2.
-/
import Shogi.C.Proofs.EntryPoints
import Shogi.C.Proofs.RecDischarge
import Shogi.C.Proofs.KingsUniq
import Shogi.Theorems
import Shogi.SfenTheorems

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

namespace Shogi.C
open MiniC Shogi Shogi.C
variable {posBlock : Nat}

/-- The spec-level invariant that supplies every hypothesis of the C
    generator refinement. Using `kingCount ≤ 1` (instead of `KingsUnique`
    itself) keeps `reachable_rulesInv` a direct consequence of the spec
    invariants; `KingsUnique` is derived by `kingsUnique_of_count`. -/
def RulesInv (p : Position) : Prop :=
  p.Shaped ∧ (∀ c, p.kingCount c ≤ 1) ∧ p.materialOk = true ∧
    p.inCheck p.side.opp = false

theorem reachable_rulesInv {p : Position} (h : Position.Reachable p) : RulesInv p :=
  ⟨(Position.reachable_inv h).1,
    fun c => by rw [Position.reachable_kings h c]; omega,
    Position.reachable_materialOk h,
    Position.reachable_opp_not_in_check h⟩

theorem RulesInv.kingsUnique {p : Position} (h : RulesInv p) : Proofs.KingsUnique p :=
  Proofs.kingsUnique_of_count p h.1 h.2.1

/-- **`shogi_generate_legal_mut` is correct, unconditionally.** For a
    reachable position, an output block of at least 7200 moves and any
    sufficiently fresh allocator state, the C generator writes a reordering
    of `legalMoves p`, returns its length, leaves the position block and every
    unrelated block unchanged, and stays within its allocation budget.

    No `RecSpec`, `hrec` or `CopyGenSpec` hypothesis remains. -/
theorem shogi_generate_legal_mut_correct {p : Position} (hri : RulesInv p)
    {m : Mem} {n cap mb mo : Nat} {blk : Block}
    (hm : m posBlock = some (encode p)) (ht : Proofs.TablesIn m) (hf : Proofs.Fresh m n)
    (hmb : m mb = some blk) (hlen : mo + 5 * cap ≤ blk.length)
    (hmb0 : mb ≠ 0) (hpm : posBlock ≠ mb) (hmbt : mb < 8192 ∨ 8196 < mb)
    (hn : n < 2 ^ 63) (hcap : cap < 2 ^ 64) (hcap7200 : 7200 ≤ cap) :
    ∃ K : List (List UInt8), K.Perm ((Position.legalMoves p).map (moveBytes p)) ∧
    ∃ s' cb, ExS Gen.prog ⟨frameLocals Gen.shogi_generate_legal_mut.params
        [posPtr' posBlock, .ptr mb mo, .int IntTy.u64 cap], m, false⟩
      Gen.shogi_generate_legal_mut.body (.ret (some (.int ⟨64, false⟩ K.length))) s' ∧
      Proofs.Buf s'.mem mb mo cb 0 cap K ∧ s'.mem posBlock = some (encode p) ∧
      (∀ x, x ≠ 0 → x ≠ mb → x < n → x ≠ posBlock → m x ≠ none → s'.mem x = m x) ∧
      ∃ f, Proofs.Fresh s'.mem f ∧
        f ≤ n + (Proofs.recBigEnough + p.pawnsInHands * Proofs.recDelta) := by
  have hpawns : p.pawnsInHands ≤ 36 := by
    rw [Position.pawnsInHands_eq p .black]
    exact Nat.add_le_add (Sfen.hand_le_18 hri.2.2.1 .black 0)
      (Sfen.hand_le_18 hri.2.2.1 .white 0)
  let rem := Proofs.recBigEnough + p.pawnsInHands * Proofs.recDelta
  have hrembig : Proofs.recDelta ≤ rem := by
    dsimp [rem, Proofs.recBigEnough, Proofs.recDelta]
    omega
  have hremub : rem ≤ 200 * Proofs.recDelta := by
    dsimp [rem, Proofs.recBigEnough, Proofs.recDelta] at *
    omega
  have h64 : n + rem + 2000000 < 2 ^ 64 := by
    dsimp [rem, Proofs.recBigEnough, Proofs.recDelta] at *
    omega
  have hglobal : n + 401 * rem < 2 ^ 64 := by
    dsimp [rem, Proofs.recBigEnough, Proofs.recDelta] at *
    omega
  have hrec : ∀ mv ∈ p.pseudoMoves, Position.isPawnDrop mv →
      (p.play mv).inCheck (p.play mv).side →
      Proofs.RecSpec (posBlock := posBlock) (p.pawnsInHands + 1) (rem - Proofs.recDelta) (p.play mv) := by
    intro mv hmv hpd _
    have hdec : (p.play mv).pawnsInHands + 1 = p.pawnsInHands :=
      Position.pawnsInHands_play_drop hmv hpd
    have hchildFuel : (p.play mv).pawnsInHands + 2 ≤ p.pawnsInHands + 1 := by omega
    have hchildMat : (p.play mv).materialOk = true :=
      Proofs.play_materialOk hri.1 hmv hri.2.2.1
    have hchildRem : Proofs.recBigEnough +
        (p.play mv).pawnsInHands * Proofs.recDelta ≤ rem - Proofs.recDelta := by
      dsimp [rem, Proofs.recBigEnough, Proofs.recDelta]
      omega
    exact Proofs.RecSpec_discharge (p.play mv) (Position.play_shaped hri.1 mv)
      (fun c => by rw [Position.play_kingCount hri.1 hmv c]; exact hri.2.1 c)
      hchildMat
      (fun i => Proofs.hand_lt_256_of_materialOk hchildMat (p.play mv).side i)
      hchildFuel (rem - Proofs.recDelta) hchildRem
  obtain ⟨K, hperm, s', cb, e, hb, hp, hframe, f, hf', hfl⟩ :=
    Proofs.shogi_generate_legal_mut_spec p hri.1 (RulesInv.kingsUnique hri)
      (fun i => Proofs.hand_lt_256_of_materialOk hri.2.2.1 p.side i)
      (p.pawnsInHands + 1) rem hrec hm ht hf hri.2.2.2 h64 hglobal hrembig hremub
      hmb hlen hmb0 hcap hpm hmbt hcap7200
  refine ⟨K, ?_, s', cb, e, hb, hp, hframe, f, hf', ?_⟩
  · simpa [Position.legalMoves, Position.legalFuel, Nat.add_assoc] using hperm
  · simpa [rem] using hfl

end Shogi.C
