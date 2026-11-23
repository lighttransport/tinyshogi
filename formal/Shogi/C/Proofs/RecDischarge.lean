/-
  M4c: discharge `RecSpec` by strong induction on `q.pawnsInHands`.
-/

import Shogi.C.Proofs.LegalMain
import Shogi.C.Proofs.KingsUniq
import Shogi.SfenTheorems
import Shogi.MoveCount

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

namespace Shogi.C.Proofs
variable {posBlock : Nat}
open MiniC Shogi Shogi.C

/-- The minimum budget at which the internal generator can be applied. -/
def recBigEnough : Nat := 1000000000000000

/-- A pseudo-legal move preserves the at-most-one-king-per-colour invariant. -/
theorem play_kingCount_le {p : Position} (hs : p.Shaped) {m : Move} (hm : m ∈ p.pseudoMoves)
    {c : Color} (hK : p.kingCount c ≤ 1) : (p.play m).kingCount c ≤ 1 := by
  rw [Shogi.Position.play_kingCount hs hm c]; exact hK

/-- A pseudo-legal move preserves the "full set of each family" invariant. -/
theorem play_materialOk {p : Position} (hs : p.Shaped) {m : Move} (hm : m ∈ p.pseudoMoves)
    (hmat : p.materialOk = true) : (p.play m).materialOk = true := by
  unfold Position.materialOk at hmat ⊢
  rw [List.all_eq_true] at hmat ⊢
  intro i _
  have eq : (p.play m).familyCount i = p.familyCount i := Position.play_familyCount hs hm i
  have hle := hmat i (List.mem_finRange i)
  simpa [eq] using hle

/-- Material in each hand slot is bounded by a full set, so it fits in a byte. -/
theorem hand_lt_256_of_materialOk {p : Position} (hmat : p.materialOk = true) (c : Color) (i : Fin 7) :
    p.hand c i < 256 := by
  exact Nat.lt_of_le_of_lt (Shogi.Sfen.hand_le_18 hmat c i) (by decide)

/-- Strong induction on the pawn count.  Keeping `n` as an explicit argument
    (rather than using `generalizing`) makes the recursive call unambiguous. -/
private theorem recSpec_aux (n : Nat) :
    ∀ (q : Position), q.pawnsInHands = n → q.Shaped → (∀ c, q.kingCount c ≤ 1) →
      q.materialOk = true → (∀ (i : Fin 7), q.hand q.side i < 256) →
      ∀ (fuel : Nat), n + 2 ≤ fuel → ∀ rem, recBigEnough + n * recDelta ≤ rem →
        RecSpec (posBlock := posBlock) fuel rem q := by
  induction n using Nat.strongRecOn with
  | _ n ih =>
    intro q hq hs hku hmat hwq fuel hf1 rem hbig
    have hrembig : recDelta ≤ rem := by
      unfold recBigEnough at hbig
      unfold recDelta
      omega
    have hrec : ∀ mv ∈ q.pseudoMoves, Position.isPawnDrop mv →
        (q.play mv).inCheck (q.play mv).side → RecSpec (posBlock := posBlock) (fuel - 1) (rem - recDelta) (q.play mv) := by
      intro mv hmv hp hc
      have hdrop : (q.play mv).pawnsInHands + 1 = q.pawnsInHands :=
        Position.pawnsInHands_play_drop hmv hp
      have hlt : (q.play mv).pawnsInHands < n := by omega
      have hshape : (q.play mv).Shaped := Position.play_shaped hs mv
      have hkc : ∀ c, (q.play mv).kingCount c ≤ 1 := fun c => by
        rw [Position.play_kingCount hs hmv c]; exact hku c
      have hmat' := play_materialOk hs hmv hmat
      have hwq' : ∀ i, (q.play mv).hand (q.play mv).side i < 256 :=
        fun i => hand_lt_256_of_materialOk hmat' _ i
      have hnd : n = (q.play mv).pawnsInHands + 1 := by omega
      have hbig' := hbig
      rw [hnd, Nat.succ_mul] at hbig'
      have hchild : recBigEnough + (q.play mv).pawnsInHands * recDelta ≤ rem - recDelta := by omega
      exact ih (q.play mv).pawnsInHands hlt (q.play mv) rfl hshape hkc hmat' hwq' (fuel - 1) (by omega)
        (rem - recDelta) hchild
    intro M rb k hM ht hf hrb hnc h64 hglobal hremub
    have hgen64 : k + 8000 * RB + 5000000000 < 2 ^ 64 := by
      unfold recBigEnough at hbig
      unfold RB
      unfold recDelta at hbig hrembig
      omega
    obtain ⟨blk, hmb, hbl, hrb0, hrbp, h188⟩ := hrb
    obtain ⟨Ms, hperm, s', cb, e, hb, hp, hfr, f, hf, hfbound⟩ :=
      generate_legal_main (fuel := fuel - 1) (mb := rb) (mo := 0) (cap := 7200)
        hs (kingsUnique_of_count q hs hku) hwq rem hrec hM ht hf hnc h64 hglobal hrembig hremub
        hmb (by omega) hrb0 (by decide : 7200 < 2 ^ 64) (by omega)
        (by
          rcases h188 with h | h
          · exact Or.inl (by omega)
          · exact Or.inr (by omega))
    let K : List (List UInt8) := keepBytes q (fuel - 1) Ms
    have hKperm : K.Perm ((Position.legalAux fuel q).map (moveBytes q)) := by
      have hf' : (fuel - 1) + 1 = fuel := by omega
      rw [← hf']
      exact keepBytes_perm q (fuel - 1) hperm
    have hKlen : K.length = (Position.legalAux fuel q).length := by
      rw [List.Perm.length_eq hKperm, List.length_map]
    have hk_le : K.length ≤ 7200 := by
      have h1 : K.length ≤ Ms.length := by
        dsimp [K, keepBytes]
        exact List.length_filterMap_le _ _
      rw [hperm.length_eq] at h1
      exact Nat.le_trans h1 (pseudoMoves_le_7200 q)
    have hmin : min (keepBytes q (fuel - 1) Ms).length 7200 = K.length := by
      dsimp [K]
      exact Nat.min_eq_left hk_le
    rw [hmin] at e
    refine ⟨s', K.length, f, e, ?_, hp, hf, hfbound, hfr⟩
    · constructor
      · intro hne
        cases hE : Position.legalAux fuel q with
        | nil =>
            have hz : K.length = 0 := by rw [hKlen, hE]; rfl
            exact (hne hz).elim
        | cons x xs => simp
      · intro hne hZ
        have hl : Position.legalAux fuel q = [] :=
          (List.length_eq_zero_iff).mp (by rw [← hKlen]; exact hZ)
        rw [hl] at hne
        simp at hne

/-- **M4c.** `RecSpec` is discharged for every well-formed position. -/
theorem RecSpec_discharge (q : Position) (hs : q.Shaped) (hku : ∀ c, q.kingCount c ≤ 1)
    (hmat : q.materialOk = true) (hwq : ∀ (i : Fin 7), q.hand q.side i < 256)
    {fuel : Nat} (hf1 : q.pawnsInHands + 2 ≤ fuel) :
    ∀ rem, recBigEnough + q.pawnsInHands * recDelta ≤ rem → RecSpec (posBlock := posBlock) fuel rem q :=
  recSpec_aux q.pawnsInHands q rfl hs hku hmat hwq fuel hf1

end Shogi.C.Proofs
