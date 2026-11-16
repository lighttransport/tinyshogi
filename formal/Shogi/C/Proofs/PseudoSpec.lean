/-
  T7: `generate_pseudo_for_color` produces the spec's pseudo-legal moves
  (`Position.pseudoMoves`) as move bytes, up to order (the C emits a horse's
  or dragon's slides before its steps; the spec lists steps first).
-/
import Shogi.C.Proofs.Pseudo5

namespace Shogi.C.Proofs
open MiniC Shogi Shogi.C

/-- Spec bytes for a move of piece `q` from `s` to `d` (the `boardMoves` body). -/
def tgtB (p : Position) (s : Square) (q : Piece) (d : Square) : List (List UInt8) :=
  (match p.pieceAt d with
    | some r => if r.color == q.color || r.type == PieceType.king then []
                else (Position.promoChoices q.color q.type s d).map (Move.normal s d)
    | none => (Position.promoChoices q.color q.type s d).map (Move.normal s d)).map (moveBytes p)

theorem ray_fuel : ∀ s : Square, ∀ d ∈ Tables.rayDirs, ray.go d 10 s = ray.go d 9 s ∧ ray.go d 9 s = ray.go d 8 s := by
  decide +kernel

section rel
variable (p : Position) (s : Square) (q : Piece) (hq : p.pieceAt s = some q)
include hq

theorem promo_eq (d : Square) :
    promoC q.color q.type d.row q.type.canPromote (inZone q.color (s.val / 9)) = Position.promoChoices q.color q.type s d := by
  simp [promoC, Position.promoChoices, Square.row]

theorem nm_eq (d : Square) (pr : Bool) :
    nmBytes s.val d.val q.code pr = moveBytes p (.normal s d pr) := by
  simp [nmBytes, moveBytes, hq, pieceByte]

theorem tgt_eq (d : Square) :
    (match p.pieceAt d with
      | some r => if r.color == q.color || r.type == .king then []
                  else (promoC q.color q.type d.row q.type.canPromote (inZone q.color (s.val / 9))).map
                    (nmBytes s.val d.val q.code)
      | none => (promoC q.color q.type d.row q.type.canPromote (inZone q.color (s.val / 9))).map
                    (nmBytes s.val d.val q.code)) = tgtB p s q d := by
  unfold tgtB
  rw [promo_eq p s q hq d]
  have : nmBytes s.val d.val q.code = fun pr => moveBytes p (.normal s d pr) := funext (nm_eq p s q hq d)
  rw [this]
  cases p.pieceAt d with
  | none => simp [List.map_map]
  | some r => by_cases h : r.color = q.color ∨ r.type = PieceType.king <;> simp [h, List.map_map] <;> rfl

theorem step_eq (dr dc : Int) :
    opOut p q.color q.type s.val q.code (s.val / 9) (s.val % 9) q.type.canPromote (inZone q.color (s.val / 9))
      (.step dr dc) = (s.offset (dr, dc)).toList.flatMap (tgtB p s q) := by
  simp only [opOut, stepOut, Square.offset, Square.row, Square.col]
  cases h : Square.mk? (((s.val / 9 : Nat) : Int) + dr) (((s.val % 9 : Nat) : Int) + dc) with
  | none => rfl
  | some d =>
    simp only [Option.toList, List.flatMap_cons, List.flatMap_nil, List.append_nil]
    rw [← tgt_eq p s q hq d]; rfl

theorem slide_go (dr dc : Int) :
    ∀ k (u : Square), ray.go (dr, dc) (k + 1) u = ray.go (dr, dc) k u →
      slideC p q.color q.type s.val q.code q.type.canPromote (inZone q.color (s.val / 9)) dr dc k
        ((u.val / 9 : Nat) + dr) ((u.val % 9 : Nat) + dc) =
      (Position.slideTargets.go p (ray.go (dr, dc) k u)).flatMap (tgtB p s q) := by
  intro k; induction k with
  | zero => intro u _; simp [slideC, ray.go, Position.slideTargets.go]
  | succ k ih =>
    intro u hu
    have hoff : u.offset (dr, dc) = Square.mk? ((u.val / 9 : Nat) + dr) ((u.val % 9 : Nat) + dc) := rfl
    simp only [ray.go, hoff] at hu ⊢
    cases hm : Square.mk? (((u.val / 9 : Nat) : Int) + dr) (((u.val % 9 : Nat) : Int) + dc) with
    | none => simp only [slideC]; rw [hm]; rfl
    | some v =>
      simp only [hm] at hu
      have hu' : ray.go (dr, dc) (k + 1) v = ray.go (dr, dc) k v := List.cons.inj hu |>.2
      have hv : (((v.val / 9 : Nat) : Int) + dr) = ((u.val / 9 : Nat) + dr) + dr ∧
          (((v.val % 9 : Nat) : Int) + dc) = ((u.val % 9 : Nat) + dc) + dc := by
        unfold Square.mk? at hm; split at hm
        · next hh => cases hm; simp only; constructor <;> omega
        · cases hm
      simp only [slideC]; rw [hm]
      have hpre := tgt_eq p s q hq v
      cases hp : p.pieceAt v with
      | none =>
        have he : p.isEmpty v = true := by simp [Position.isEmpty, hp]
        simp only [Position.slideTargets.go, he, ite_true, List.flatMap_cons]
        rw [← hv.1, ← hv.2, ih v hu', ← hpre, hp]
      | some r =>
        have he : p.isEmpty v = false := by simp [Position.isEmpty, hp]
        simp only [Position.slideTargets.go, he, Bool.false_eq_true, ite_false, List.flatMap_cons,
          List.flatMap_nil, List.append_nil]
        rw [← hpre, hp]
        by_cases h : r.color = q.color ∨ r.type = PieceType.king
        · have : (r.color != q.color && r.type != PieceType.king) = false := by
            rcases h with h | h <;> simp [h]
          simp [this, h]
        · have : (r.color != q.color && r.type != PieceType.king) = true := by
            simp only [not_or] at h; simp [h.1, h.2]
          simp [this, h]

theorem slide_eq (dr dc : Int) (hd : (dr, dc) ∈ Tables.rayDirs) :
    opOut p q.color q.type s.val q.code (s.val / 9) (s.val % 9) q.type.canPromote (inZone q.color (s.val / 9))
      (.slide dr dc) = (p.slideTargets s (dr, dc)).flatMap (tgtB p s q) := by
  have hf := ray_fuel s (dr, dc) hd
  simp only [opOut, Position.slideTargets, ray]
  rw [slide_go p s q hq dr dc 9 s hf.1, hf.2]

theorem steps_eq (L : List (Int × Int)) :
    (L.map (fun d => Op.step d.1 d.2)).flatMap (opOut p q.color q.type s.val q.code (s.val / 9) (s.val % 9)
      q.type.canPromote (inZone q.color (s.val / 9))) = (L.filterMap s.offset).flatMap (tgtB p s q) := by
  induction L with
  | nil => rfl
  | cons d r ih =>
    simp only [List.map_cons, List.flatMap_cons, List.filterMap_cons]
    rw [step_eq p s q hq, ih]
    cases s.offset (d.1, d.2) <;> simp

theorem slides_eq (L : List (Int × Int)) (hL : ∀ d ∈ L, d ∈ Tables.rayDirs) :
    (L.map (fun d => Op.slide d.1 d.2)).flatMap (opOut p q.color q.type s.val q.code (s.val / 9) (s.val % 9)
      q.type.canPromote (inZone q.color (s.val / 9))) = (L.flatMap (p.slideTargets s)).flatMap (tgtB p s q) := by
  induction L with
  | nil => rfl
  | cons d r ih =>
    simp only [List.map_cons, List.flatMap_cons, List.flatMap_append]
    rw [slide_eq p s q hq d.1 d.2 (hL d (by simp)), ih (fun x hx => hL x (by simp [hx]))]

end rel

def stepsC (f : Int) (t : PieceType) : List Op := (stepOffsets f t).map (fun d => Op.step d.1 d.2)
def slidesC (f : Int) (t : PieceType) : List Op := (slideDirs f t).map (fun d => Op.slide d.1 d.2)

theorem cOps_shape (f : Int) (t : PieceType) :
    cOps f t = (if t = .horse ∨ t = .dragon then slidesC f t ++ stepsC f t else stepsC f t ++ slidesC f t) := by
  cases t <;> first | rfl | decide

/-- Spec bytes of the board moves from square `s` for side `c`. -/
def specSq (p : Position) (c : Color) (s : Square) : List (List UInt8) :=
  (match p.pieceAt s with
    | some pc => if pc.color == c then p.boardMoves s pc else []
    | none => []).map (moveBytes p)

theorem boardMoves_bytes (p : Position) (s : Square) (q : Piece) :
    (p.boardMoves s q).map (moveBytes p) = (p.attackSquares s q).flatMap (tgtB p s q) := by
  unfold Position.boardMoves; rw [List.map_flatMap]; rfl

theorem sq_perm (p : Position) (c : Color) (fr : Nat) (hfr : fr < 81) :
    (sqOut p c fr).Perm (specSq p c ⟨fr, hfr⟩) := by
  unfold sqOut specSq
  rw [dif_pos hfr]
  cases hq : p.pieceAt ⟨fr, hfr⟩ with
  | none => exact List.Perm.refl _
  | some q =>
    by_cases hc : q.color = c
    · subst hc
      simp only [ite_true, beq_self_eq_true]
      rw [boardMoves_bytes, Position.attackSquares, List.flatMap_append, cOps_shape]
      have hst := steps_eq p ⟨fr, hfr⟩ q hq (stepOffsets q.color.fwd q.type)
      have hsl := slides_eq p ⟨fr, hfr⟩ q hq (slideDirs q.color.fwd q.type) (Position.slideDirs_sub q.color q.type)
      simp only at hst hsl
      split
      · rw [List.flatMap_append]; unfold stepsC slidesC; rw [hst, hsl]; exact List.perm_append_comm
      · rw [List.flatMap_append]; unfold stepsC slidesC; rw [hst, hsl]
    · have : (q.color == c) = false := by simp [hc]
      simp [hc, this]

theorem flatMap_perm {α β : Type} {f g : α → List β} :
    ∀ l : List α, (∀ x ∈ l, (f x).Perm (g x)) → (l.flatMap f).Perm (l.flatMap g) := by
  intro l; induction l with
  | nil => intro _; exact List.Perm.refl _
  | cons a l ih =>
    intro h; simp only [List.flatMap_cons]
    exact (h a (by simp)).append (ih (fun x hx => h x (by simp [hx])))

/-- **`generate_pseudo_for_color` refines `Position.pseudoMoves`** (for the side
    to move, hand counts < 256): the bytes it appends are the spec's
    pseudo-legal moves, up to permutation. -/
theorem pseudoC_spec (p : Position) (hw : ∀ i, p.hand p.side i < 256) :
    (pseudoC p p.side).Perm (p.pseudoMoves.map (moveBytes p)) := by
  unfold pseudoC Position.pseudoMoves
  rw [List.map_append, ← dropsC_spec p hw]
  refine List.Perm.append ?_ (List.Perm.refl _)
  rw [List.map_flatMap]
  have h1 : boardOut p p.side 0 81 = (List.finRange 81).flatMap (fun x => sqOut p p.side x.val) := by
    rw [boardOut, ← List.range_eq_range', ← finRange81_val, List.flatMap_map]
  rw [h1]
  apply flatMap_perm; intro x _
  exact sq_perm p p.side x.val x.isLt

end Shogi.C.Proofs
