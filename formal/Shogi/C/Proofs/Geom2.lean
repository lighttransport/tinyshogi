/-
  T8: the clearance a move "along the pin" needs, derived from the move's
  geometry.
-/
import Shogi.C.Proofs.Geom

namespace Shogi.C.Proofs
open MiniC Shogi Shogi.C Shogi.Tables

/-- A pin found by the scan: an empty stretch, then the pinned own piece. -/
theorem kres_pin_split (P : Position) (c : Color) (mk : Nat) (o : Square) :
    ∀ L : List Square, (kres P c mk L none).2 = some o →
      ∃ A B, L = A ++ o :: B ∧ (∀ x ∈ A, P.pieceAt x = none) := by
  intro L; induction L with
  | nil => intro h; simp [kres] at h
  | cons x r ih =>
    intro h
    simp only [kres] at h
    cases hx : P.pieceAt x with
    | none =>
      rw [hx] at h
      obtain ⟨A, B, hL, hA⟩ := ih h
      exact ⟨x :: A, B, by simp [hL], fun y hy => by
        rcases List.mem_cons.mp hy with e | e
        · subst e; exact hx
        · exact hA y e⟩
    | some q =>
      rw [hx] at h; simp only at h
      split at h
      · rw [kres_some] at h
        split at h
        · cases h; exact ⟨[], r, rfl, fun _ h => by cases h⟩
        · cases h
      · simp at h

theorem slide_go_prefix (p : Position) (d : Square) :
    ∀ l : List Square, d ∈ Position.slideTargets.go p l → ∀ x ∈ l.takeWhile (· ≠ d), p.pieceAt x = none := by
  intro l; induction l with
  | nil => intro h; cases h
  | cons y r ih =>
    intro h x hx
    simp only [Position.slideTargets.go] at h
    by_cases hyd : y = d
    · subst hyd; simp [List.takeWhile_cons] at hx
    · rw [List.takeWhile_cons, if_pos (by simpa using hyd)] at hx
      split at h
      · next he =>
        rcases List.mem_cons.mp hx with e | e
        · subst e; simpa [Position.isEmpty] using he
        · exact ih ((List.mem_cons.mp h).resolve_left (Ne.symm hyd)) x e
      · simp at h; exact absurd h.symm hyd

theorem pseudo_target {p : Position} {s d : Square} {pr : Bool} {pc : Piece}
    (h : Move.normal s d pr ∈ p.pseudoMoves) (hpc : p.pieceAt s = some pc) : d ∈ p.attackSquares s pc := by
  unfold Position.pseudoMoves at h
  rw [List.mem_append] at h
  rcases h with h | h
  · rw [List.mem_flatMap] at h
    obtain ⟨s', _, hs'⟩ := h
    cases hp : p.pieceAt s' with
    | none => simp [hp] at hs'
    | some pc' =>
      simp only [hp] at hs'
      split at hs'
      · unfold Position.boardMoves at hs'
        rw [List.mem_flatMap] at hs'
        obtain ⟨d', hd', hm'⟩ := hs'
        have key : s' = s ∧ d' = d := by
          cases hq : p.pieceAt d' with
          | none =>
            simp only [hq, List.mem_map] at hm'
            obtain ⟨_, _, e⟩ := hm'; cases e; exact ⟨rfl, rfl⟩
          | some q =>
            simp only [hq] at hm'
            split at hm'
            · simp at hm'
            · simp only [List.mem_map] at hm'
              obtain ⟨_, _, e⟩ := hm'; cases e; exact ⟨rfl, rfl⟩
        obtain ⟨rfl, rfl⟩ := key
        rw [hpc] at hp; cases hp; exact hd'
      · simp at hs'
  · unfold Position.dropMoves at h
    rw [List.mem_flatMap] at h
    obtain ⟨_, _, h⟩ := h
    rw [List.mem_filterMap] at h
    obtain ⟨_, _, h⟩ := h
    simp only at h; split at h <;> simp at h

theorem go_sub (p : Position) (d : Square) : ∀ l : List Square, d ∈ Position.slideTargets.go p l → d ∈ l := by
  intro l; induction l with
  | nil => intro h; cases h
  | cons y r ih =>
    intro h; simp only [Position.slideTargets.go] at h
    split at h
    · rcases List.mem_cons.mp h with e | e
      · simp [e]
      · exact List.mem_cons_of_mem _ (ih e)
    · simp at h; simp [h]

theorem takeWhile_append_of_mem {α : Type} [DecidableEq α] (d : α) :
    ∀ (A R : List α), d ∈ A → (A ++ R).takeWhile (· ≠ d) = A.takeWhile (· ≠ d) := by
  intro A; induction A with
  | nil => intro _ h; cases h
  | cons y r ih =>
    intro R h
    by_cases hy : y = d
    · subst hy; simp [List.takeWhile_cons]
    · simp only [List.cons_append, List.takeWhile_cons, show (y ≠ d) = True from propext ⟨fun _ => trivial, fun _ => hy⟩,
        decide_true, if_true]
      rw [ih R ((List.mem_cons.mp h).resolve_left (Ne.symm hy))]

theorem takeWhile_append_of_not_mem {α : Type} [DecidableEq α] (d : α) :
    ∀ (A R : List α), d ∉ A → (A ++ R).takeWhile (· ≠ d) = A ++ R.takeWhile (· ≠ d) := by
  intro A; induction A with
  | nil => intro _ _; rfl
  | cons y r ih =>
    intro R h
    have hy : y ≠ d := fun e => h (by simp [e])
    simp only [List.cons_append, List.takeWhile_cons, show (y ≠ d) = True from propext ⟨fun _ => trivial, fun _ => hy⟩,
      decide_true, if_true]
    rw [ih R (fun h' => h (List.mem_cons_of_mem _ h'))]

/-- **Clearance.** A pinned piece (the first piece on ray `r`, after the empty
    stretch `A`) that moves to another square of the same ray: everything on
    the ray before the destination is empty, apart from its own square. -/
theorem clear_along (p : Position) {sq d : Square} {pr : Bool} {pc : Piece}
    (hm : Move.normal sq d pr ∈ p.pseudoMoves) (hpc : p.pieceAt sq = some pc) (k : Square) {r : Nat} (hr : r < 8)
    {A B : List Square} (hL : ray k (rdir r) = A ++ sq :: B) (hA : ∀ x ∈ A, p.pieceAt x = none)
    (hdL : d ∈ ray k (rdir r)) (hds : d ≠ sq) :
    ∀ x ∈ (ray k (rdir r)).takeWhile (· ≠ d), x = sq ∨ p.pieceAt x = none := by
  rw [hL]
  by_cases hdA : d ∈ A
  · rw [takeWhile_append_of_mem d A _ hdA]
    intro x hx; right; exact hA x ((List.takeWhile_sublist _).subset hx)
  · rw [takeWhile_append_of_not_mem d A _ hdA, List.takeWhile_cons,
      if_pos (by simpa using Ne.symm hds)]
    have hdB : d ∈ B := by
      rw [hL] at hdL; simp [List.mem_append] at hdL
      rcases hdL with h | h | h
      · exact absurd h hdA
      · exact absurd h hds
      · exact h
    -- facts about the index of `sq`
    let L := ray k (rdir r)
    let i := A.length
    have hlen : i < L.length := by simp [L, hL, i]
    have hsqi : L.getD i k = sq := by simp [L, hL, i, List.getD_eq_getElem?_getD]
    have hdrop : L.drop (i + 1) = B := by simp [L, hL, i]
    have hsuf : ray sq (rdir r) = B := by
      have := List.all_eq_true.mp (ray_suffix_all k ⟨r, hr⟩) i (List.mem_range.mpr hlen)
      simp only [beq_iff_eq] at this
      rw [← hsqi, ← hdrop]; exact this
    intro x hx
    rcases List.mem_append.mp hx with h | h
    · right; exact hA x h
    rcases List.mem_cons.mp h with h | h
    · left; exact h
    right
    -- `x` lies on `B` strictly before `d`
    have hatk := pseudo_target hm hpc
    unfold Position.attackSquares at hatk
    rcases List.mem_append.mp hatk with hs | hs
    · -- a single step: `d` must be the square right after `sq`
      obtain ⟨o, ho, hoff⟩ := List.mem_filterMap.mp hs
      obtain ⟨j', hj', hBj⟩ := List.getElem_of_mem hdB
      have hj0 : j' = 0 := by
        cases j' with
        | zero => rfl
        | succ j'' =>
        exfalso
        have hall := List.all_eq_true.mp (ray_suffix_all k ⟨r, hr⟩) i (List.mem_range.mpr hlen)
        have hadj := List.all_eq_true.mp (List.all_eq_true.mp (step_adj_all k ⟨r, hr⟩) i (List.mem_range.mpr hlen))
          (i + 1 + (j'' + 1)) (List.mem_range.mpr (by simp [L, hL, i] at hj' ⊢; omega))
        simp only [Bool.or_eq_true, decide_eq_true_eq] at hadj
        rcases hadj with h1 | h1
        · omega
        · have := List.all_eq_true.mp h1 o (stepOffsets_sub pc.color pc.type o ho)
          have hd' : L.getD (i + 1 + (j'' + 1)) k = d := by
            rw [← hBj]; simp [L, hL, i, List.getD_eq_getElem?_getD, List.getElem?_append_right]
            rw [List.getElem?_append_right (by omega), show A.length + 1 + (j'' + 1) - A.length = (j'' + 1) + 1 by omega]
            simp [hj']
          rw [hsqi, hd'] at this; simp [hoff] at this
      subst hj0
      have : B.takeWhile (· ≠ d) = [] := by
        cases B with
        | nil => simp at hdB
        | cons b B' => simp at hBj; subst hBj; simp [List.takeWhile_cons]
      rw [this] at h; cases h
    · -- a slide: along this ray the path is clear; other directions never meet `B`
      obtain ⟨dir, hdir, hdt⟩ := List.mem_flatMap.mp hs
      have hdir' := Position.slideDirs_sub pc.color pc.type dir hdir
      obtain ⟨r', hr', rfl⟩ : ∃ r', r' < 8 ∧ dir = rdir r' := by
        rw [rayDirs_eq, List.mem_map] at hdir'; obtain ⟨r', hr', e⟩ := hdir'; exact ⟨r', List.mem_range.mp hr', e.symm⟩
      by_cases hrr : r' = r
      · subst hrr
        unfold Position.slideTargets at hdt
        rw [hsuf] at hdt
        exact slide_go_prefix p d B hdt x h
      · exfalso
        unfold Position.slideTargets at hdt
        have hdray := go_sub p d _ hdt
        have hoff := List.all_eq_true.mp (List.all_eq_true.mp (offline_all k ⟨r, hr⟩) i (List.mem_range.mpr hlen))
          ⟨r', hr'⟩ (List.mem_finRange _)
        simp only [Bool.or_eq_true, beq_iff_eq] at hoff
        rcases hoff with e | e
        · exact hrr (by simpa using congrArg Fin.val e)
        · have := List.all_eq_true.mp e d (by rw [hsqi]; exact hdray)
          rw [hdrop] at this; simp [hdB] at this

/-- **Fast path, pinned piece moving along the pin.** -/
theorem fastpath_pinned (p : Position) (hS : p.Shaped) (hK : KingsUnique p) {sq d : Square} {pr : Bool}
    (hm : Move.normal sq d pr ∈ p.pseudoMoves) {pc : Piece} (hpc : p.pieceAt sq = some pc)
    (hkt : pc.type ≠ .king) {k : Square} (hks : p.kingSquare p.side = some k) (hnc : p.inCheck p.side = false)
    (hpin : pinnedSpec p p.side k sq = true) (hray : sameKingRay k sq d = true) :
    (p.play (.normal sq d pr)).inCheck p.side = false := by
  unfold pinnedSpec at hpin
  obtain ⟨r, hr, hr2⟩ := List.any_eq_true.mp hpin
  have hr8 := List.mem_range.mp hr
  simp only [beq_iff_eq] at hr2
  obtain ⟨A, B, hL, hA⟩ := kres_pin_split p p.side _ sq _ hr2
  have hsq : sq ∈ ray k (rdir r) := by rw [hL]; simp
  have hd : d ∈ ray k (rdir r) := by
    have := List.all_eq_true.mp (List.all_eq_true.mp (sameKingRay_ray k ⟨r, hr8⟩) sq hsq) d (List.mem_finRange d)
    simp only [Bool.or_eq_true, Bool.not_eq_true'] at this
    rcases this with h | h
    · rw [hray] at h; cases h
    · simpa using h
  exact fastpath_along p hS hK hm hpc hkt hks hnc hr8 hsq hd
    (clear_along p hm hpc k hr8 hL hA hd (pseudo_ne hm))

/-- **Soundness of the legality filter's fast path.** If the side to move is
    not in check and moves a non-king piece that is not pinned, or is pinned
    and stays on the king's ray (`same_king_ray`), the move is legal: the
    king is not attacked afterwards. This is the condition under which the C
    skips the probe. -/
theorem fastpath_sound (p : Position) (hS : p.Shaped) (hK : KingsUnique p) {sq d : Square} {pr : Bool}
    (hm : Move.normal sq d pr ∈ p.pseudoMoves) {pc : Piece} (hpc : p.pieceAt sq = some pc)
    (hkt : pc.type ≠ .king) {k : Square} (hks : p.kingSquare p.side = some k) (hnc : p.inCheck p.side = false)
    (hcond : pinnedSpec p p.side k sq = false ∨ sameKingRay k sq d = true) :
    (p.play (.normal sq d pr)).inCheck p.side = false := by
  cases hpn : pinnedSpec p p.side k sq
  · exact fastpath_unpinned p hS hK hm hpc hkt hks hnc hpn
  · rcases hcond with h | h
    · rw [hpn] at h; cases h
    · exact fastpath_pinned p hS hK hm hpc hkt hks hnc hpn h

end Shogi.C.Proofs
