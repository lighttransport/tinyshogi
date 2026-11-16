/-
  Positions reached by legal play satisfy the `KingsUnique` hypothesis of the
  probe and fast-path theorems.
-/
import Shogi.C.Proofs.LegalIter2
import Shogi.Theorems

namespace Shogi.C.Proofs
open Shogi

theorem kingsUnique_of_count (p : Position) (hS : p.Shaped) (h1 : ∀ c, p.kingCount c ≤ 1) : KingsUnique p := by
  intro c x y hx hy
  refine Classical.byContradiction (fun hne => ?_)
  have hxl : x.val < p.board.length := by rw [hS.1]; exact x.isLt
  have hyl : y.val < p.board.length := by rw [hS.1]; exact y.isLt
  have hbx : p.board[x.val] = some ⟨c, .king⟩ := by
    simp [Position.pieceAt, List.getD_eq_getElem?_getD, hxl] at hx; exact hx
  have hby : p.board[y.val] = some ⟨c, .king⟩ := by
    simp [Position.pieceAt, List.getD_eq_getElem?_getD, hyl] at hy; exact hy
  have hset := List.countP_set (p := (· == some ⟨c, .king⟩)) (a := none) hxl
  have hpos : 0 < (p.board.set x.val none).countP (· == some ⟨c, .king⟩) :=
    List.countP_pos_iff.mpr ⟨some ⟨c, .king⟩, by
      rw [List.mem_iff_getElem]
      refine ⟨y.val, by simpa using hyl, ?_⟩
      rw [List.getElem_set_ne (fun e => hne (Fin.ext e))]; exact hby, by simp⟩
  have := h1 c
  unfold Position.kingCount at this
  rw [hset, hbx] at hpos
  simp at hpos; omega

theorem reachable_kingsUnique {p : Position} (h : Position.Reachable p) : KingsUnique p :=
  kingsUnique_of_count p (Position.reachable_inv h).1 (fun c => by rw [Position.reachable_kings h c]; exact Nat.le_refl 1)

end Shogi.C.Proofs

namespace Shogi.C.Proofs
open MiniC Shogi Shogi.C

/-- For positions reached by legal play, the probe round trip holds with no
    side conditions on the position. -/
theorem probe_roundtrip_reachable {p : Position} (hr : Position.Reachable p) (mv : Move) (hm : mv ∈ p.pseudoMoves)
    {M : Mem} {mvb ub n : Nat} {UB : List UInt8}
    (hp : M posBlock = some (encode p)) (hmv : M mvb = some (moveBytes p mv)) (hub : M ub = some UB)
    (hUB : UB.length = 20) (hf : Fresh M n) (h64 : n + 2 < 2 ^ 64)
    (hmvb0 : mvb ≠ 0) (hub0 : ub ≠ 0) (hpu : posBlock ≠ ub) :
    ∃ s1 s2, ExS Gen.prog ⟨frameLocals Gen.make_legal_probe.params [posPtr, .ptr mvb 0, .ptr ub 0], M, false⟩
        Gen.make_legal_probe.body .normal s1 ∧ s1.mem posBlock = some (encode (p.play mv)) ∧
      ExS Gen.prog ⟨frameLocals Gen.unmake_legal_probe.params [posPtr, .ptr ub 0], s1.mem, false⟩
        Gen.unmake_legal_probe.body .normal s2 ∧ s2.mem posBlock = some (encode p) :=
  probe_roundtrip p (Position.reachable_inv hr).1 (reachable_kingsUnique hr) mv hm hp hmv hub hUB hf h64 hmvb0 hub0 hpu

end Shogi.C.Proofs
