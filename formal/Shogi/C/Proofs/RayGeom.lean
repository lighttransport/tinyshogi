/-
  Finite geometry facts for the fid 18 ray walk, checked in the kernel.
  They relate `Position.ray` to the cursor path walked by
  `shogi_piece_attacks_square_loop0`.
-/
import Shogi.C.Proofs.RayWalk
import Shogi.C.Proofs.SquareAttack
set_option maxRecDepth 100000
namespace Shogi.C.Proofs
open MiniC Shogi Shogi.C

theorem ray_nodup_finite : ∀ (s : Square) (r : Fin 8), (ray s (rdir r.val)).Nodup := by
  decide +kernel

theorem ray_index_finite : ∀ (s : Square) (r : Fin 8) (k : Fin 8)
    (hk : k.val < (ray s (rdir r.val)).length),
    Square.mk? ((s.row : Int) + ((k.val + 1 : Nat) : Int) * (rdir r.val).1)
               ((s.col : Int) + ((k.val + 1 : Nat) : Int) * (rdir r.val).2) =
      some ((ray s (rdir r.val))[k.val]'hk) := by
  decide +kernel

theorem ray_suffix_finite : ∀ (s : Square) (r : Fin 8) (j : Fin 8)
    (hj : j.val < (ray s (rdir r.val)).length),
    ray ((ray s (rdir r.val))[j.val]'hj) (rdir r.val) ==
      (ray s (rdir r.val)).drop (j.val + 1) := by
  decide +kernel

theorem exists_rdir (rs cs : Int) (hrs : rs = -1 ∨ rs = 0 ∨ rs = 1)
    (hcs : cs = -1 ∨ cs = 0 ∨ cs = 1) (hnz : rs ≠ 0 ∨ cs ≠ 0) :
    ∃ r : Fin 8, rdir r.val = (rs, cs) := by
  rcases hrs with rfl | rfl | rfl <;> rcases hcs with rfl | rfl | rfl <;>
    first | decide | (rcases hnz with h | h <;> exact False.elim (h rfl))

end Shogi.C.Proofs
