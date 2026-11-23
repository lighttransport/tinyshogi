/-
  T8: why the legality filter may skip the probe. A non-king move of a
  non-pinned piece, made while not in check, never leaves the king attacked
  (spec level, no C).
-/
import Shogi.C.Proofs.SameRay

namespace Shogi.C.Proofs
variable {posBlock : Nat}
open MiniC Shogi Shogi.C Shogi.Tables

/-- The first occupied square of `L` holds an attacker slider (colour `a`, mask `mk`). -/
def atkFirst (P : Position) (a : Color) (mk : Nat) (L : List Square) : Bool :=
  match Position.firstOcc P L with
  | some y => match P.pieceAt y with
    | some pc => pc.color == a && maskHas mk pc.type
    | none => false
  | none => false

theorem atkFirst_cons (P : Position) (a : Color) (mk : Nat) (x : Square) (L : List Square) :
    atkFirst P a mk (x :: L) = match P.pieceAt x with
      | none => atkFirst P a mk L
      | some pc => pc.color == a && maskHas mk pc.type := by
  unfold atkFirst
  cases h : P.pieceAt x with
  | none => simp [Position.firstOcc, Position.isEmpty, h]
  | some pc => simp [Position.firstOcc, Position.isEmpty, h]

/-- Replacing squares by pieces not of colour `a` never creates an attack. -/
theorem atkFirst_addOwn (P Q : Position) (a : Color) (mk : Nat) :
    ∀ L : List Square, (∀ x ∈ L, Q.pieceAt x = P.pieceAt x ∨ ∃ o, Q.pieceAt x = some o ∧ o.color ≠ a) →
      atkFirst Q a mk L = true → atkFirst P a mk L = true := by
  intro L; induction L with
  | nil => intro _ h; simp [atkFirst, Position.firstOcc] at h
  | cons x r ih =>
    intro hc hq
    rw [atkFirst_cons] at hq ⊢
    rcases hc x (by simp) with he | ⟨o, ho, hoc⟩
    · rw [he] at hq
      cases hp : P.pieceAt x with
      | none => rw [hp] at hq; exact ih (fun y hy => hc y (by simp [hy])) hq
      | some pc => rw [hp] at hq; exact hq
    · rw [ho] at hq; simp [hoc] at hq

theorem kres_some (P : Position) (c : Color) (mk : Nat) (o : Square) :
    ∀ r : List Square, (kres P c mk r (some o)).2 = if atkFirst P c.opp mk r then some o else none := by
  intro r; induction r with
  | nil => simp [kres, atkFirst, Position.firstOcc]
  | cons x r ih =>
    simp only [kres]
    rw [atkFirst_cons]
    cases hx : P.pieceAt x with
    | none => exact ih
    | some q =>
      simp only
      by_cases h : q.color = c
      · have : (q.color == c.opp) = false := by rw [h]; cases c <;> rfl
        have hc : (c == c.opp) = false := by cases c <;> rfl
        simp only [h, if_true, hc, Bool.false_and]; rfl
      · have hq := opp_of_ne h
        simp only [h, if_false, hq, beq_self_eq_true, Bool.true_and, maskHas, shl_eq]
        by_cases h' : mk &&& 2 ^ q.type.code = 0 <;> simp [h', opp_ne c]

/-- One ray, after moving a piece that is not pinned on it. -/
theorem ray_safe (P Q : Position) (c : Color) (mk : Nat) (s d : Square) (M pc : Piece)
    (hQ : ∀ x, Q.pieceAt x = if x = d then some M else if x = s then none else P.pieceAt x)
    (hM : M.color = c) (hPs : P.pieceAt s = some pc) (hpc : pc.color = c) (hds : d ≠ s) :
    ∀ L : List Square, L.Nodup → atkFirst P c.opp mk L = false → (kres P c mk L none).2 ≠ some s →
      atkFirst Q c.opp mk L = false := by
  have hMo : M.color ≠ c.opp := by rw [hM]; exact Ne.symm (opp_ne c)
  intro L; induction L with
  | nil => intro _ _ _; rfl
  | cons x r ih =>
    intro hnd hP hpin
    have hxr : x ∉ r := (List.nodup_cons.mp hnd).1
    have hnr : r.Nodup := (List.nodup_cons.mp hnd).2
    rw [atkFirst_cons, hQ x]
    by_cases hxd : x = d
    · simp [hxd, hMo]
    · rw [if_neg hxd]
      by_cases hxs : x = s
      · subst hxs
        simp only [if_true]
        -- the piece on `s` was the first one; what is behind it is not an attacker
        simp only [kres, hPs, hpc, if_true] at hpin
        rw [kres_some] at hpin
        have hPr : atkFirst P c.opp mk r = false := by
          cases hc : atkFirst P c.opp mk r
          · rfl
          · simp [hc] at hpin
        cases hc : atkFirst Q c.opp mk r
        · rfl
        have := atkFirst_addOwn P Q c.opp mk r (fun y hy => ?_) hc
        · rw [hPr] at this; cases this
        · rw [hQ y]
          by_cases hyd : y = d
          · right; exact ⟨M, by simp [hyd], hMo⟩
          · left; rw [if_neg hyd, if_neg (fun (e : y = x) => hxr (e ▸ hy))]
      · rw [if_neg hxs]
        rw [atkFirst_cons] at hP
        cases hpx : P.pieceAt x with
        | none =>
          rw [hpx] at hP
          simp only [kres, hpx] at hpin
          exact ih hnr hP hpin
        | some q => rw [hpx] at hP; exact hP

theorem pseudo_ne {p : Position} {s d : Square} {pr : Bool} (h : Move.normal s d pr ∈ p.pseudoMoves) : d ≠ s := by
  intro hds; subst hds
  unfold Position.pseudoMoves at h
  rw [List.mem_append] at h
  rcases h with h | h
  · rw [List.mem_flatMap] at h
    obtain ⟨s', _, hs'⟩ := h
    cases hp : p.pieceAt s' with
    | none => simp [hp] at hs'
    | some pc =>
      simp only [hp] at hs'
      split at hs'
      · unfold Position.boardMoves at hs'
        rw [List.mem_flatMap] at hs'
        obtain ⟨d', _, hd'⟩ := hs'
        cases hq : p.pieceAt d' with
        | none =>
          simp only [hq, List.mem_map] at hd'
          obtain ⟨_, _, e⟩ := hd'; cases e; rw [hq] at hp; cases hp
        | some q =>
          simp only [hq] at hd'
          split at hd'
          · simp at hd'
          · next hk =>
            simp only [List.mem_map] at hd'
            obtain ⟨_, _, e⟩ := hd'; cases e
            rw [hq] at hp; cases hp; simp at hk
      · simp at hs'
  · unfold Position.dropMoves at h
    rw [List.mem_flatMap] at h
    obtain ⟨_, _, h⟩ := h
    rw [List.mem_filterMap] at h
    obtain ⟨_, _, h⟩ := h
    simp only at h; split at h <;> simp at h

theorem rayAttacked_atk (p : Position) (t : Square) (a : Color) :
    p.rayAttacked t a = rayDirs.any fun d => atkFirst p a (rayMask a d) (ray t d) := rfl

/-- **Fast path, unpinned case.** Not in check, a non-king piece that is not
    pinned: any pseudo-legal move of it keeps the king safe. -/
theorem fastpath_unpinned (p : Position) (hS : p.Shaped) (hK : KingsUnique p) {sq d : Square} {pr : Bool}
    (hm : Move.normal sq d pr ∈ p.pseudoMoves) {pc : Piece} (hpc : p.pieceAt sq = some pc)
    (hkt : pc.type ≠ .king) {k : Square} (hks : p.kingSquare p.side = some k) (hnc : p.inCheck p.side = false)
    (hnp : pinnedSpec p p.side k sq = false) :
    (p.play (.normal sq d pr)).inCheck p.side = false := by
  obtain ⟨pc', hpc', hcol, hcap⟩ := pseudo_normal hm
  rw [hpc] at hpc'; cases hpc'
  have hds := pseudo_ne hm
  let q := p.play (.normal sq d pr)
  have hQ := play_normal_pieceAt p hS.1 (pr := pr) (d := d) hpc
  have hkq : q.kingSquare p.side = some k := by
    rw [play_normal_kingSquare p hS.1 hK hpc hcol (fun c' h => hcap _ h rfl)]
    unfold kingAfter; rw [if_neg (fun h => hkt h.1)]; exact hks
  unfold Position.inCheck at hnc ⊢
  rw [hks] at hnc; rw [hkq]
  simp only at hnc ⊢
  rw [Position.attacked_eq] at hnc ⊢
  simp only [Bool.or_eq_false_iff] at hnc ⊢
  obtain ⟨hstep, hray⟩ := hnc
  have hM : (movedPiece p.side pc pr).color = p.side := rfl
  constructor
  · -- step attacks: only squares whose piece is unchanged can attack
    unfold Position.stepAttackedS at hstep ⊢
    rw [List.any_eq_false] at hstep ⊢
    intro x hx
    have := hstep x hx
    rw [hQ x]
    by_cases hxd : x = d
    · simp only [hxd, if_true]
      have : (movedPiece p.side pc pr).color = p.side := rfl
      simp only [this]
      have hne : (p.side == p.side.opp) = false := by cases p.side <;> rfl
      simp [hne]
    · rw [if_neg hxd]
      by_cases hxs : x = sq
      · simp [hxs]
      · rw [if_neg hxs]; exact this
  · rw [rayAttacked_atk] at hray ⊢
    rw [List.any_eq_false] at hray ⊢
    intro dir hdir
    have hdr := hray dir hdir
    simp only [Bool.not_eq_true] at hdr ⊢
    obtain ⟨r, hr, rfl⟩ : ∃ r, r < 8 ∧ dir = rdir r := by
      rw [rayDirs_eq, List.mem_map] at hdir; obtain ⟨r, hr, e⟩ := hdir; exact ⟨r, List.mem_range.mp hr, e.symm⟩
    refine ray_safe p q p.side _ sq d (movedPiece p.side pc pr) pc hQ hM hpc hcol hds _ (Position.ray_nodup k hdir) hdr ?_
    intro hpin
    unfold pinnedSpec at hnp
    rw [List.any_eq_false] at hnp
    exact hnp r (List.mem_range.mpr hr) (by simp [hpin])

theorem rays_disjoint : ∀ k : Square, ∀ r1 : Fin 8, ∀ r2 : Fin 8, r1 ≠ r2 →
    (ray k (rdir r1.val)).all (fun x => !(ray k (rdir r2.val)).contains x) = true := by
  decide +kernel

theorem ray_disj (k : Square) {r1 r2 : Nat} (h1 : r1 < 8) (h2 : r2 < 8) (hne : r1 ≠ r2) {x : Square}
    (hx : x ∈ ray k (rdir r1)) : x ∉ ray k (rdir r2) := by
  have := List.all_eq_true.mp (rays_disjoint k ⟨r1, h1⟩ ⟨r2, h2⟩ (fun e => hne (by simpa using congrArg Fin.val e))) x hx
  simpa using this

theorem kres_snd_mem (P : Position) (c : Color) (mk : Nat) :
    ∀ (L : List Square) (own : Option Square) (o : Square), (kres P c mk L own).2 = some o →
      (o ∈ L ∨ own = some o) := by
  intro L; induction L with
  | nil => intro own o h; cases own <;> simp [kres] at h
  | cons x r ih =>
    intro own o h
    simp only [kres] at h
    cases hx : P.pieceAt x with
    | none => rw [hx] at h; rcases ih own o h with h' | h' <;> simp_all
    | some q =>
      rw [hx] at h; simp only at h
      split at h
      · cases own with
        | some _ => simp at h
        | none => rcases ih (some x) o h with h' | h' <;> simp_all
      · cases own with
        | none => simp at h
        | some o' => simp only at h; split at h <;> simp_all

theorem mem_takeWhile_pred {α : Type} (P : α → Bool) :
    ∀ (L : List α) (x : α), x ∈ L.takeWhile P → P x = true := by
  intro L; induction L with
  | nil => intro x h; cases h
  | cons y r ih =>
    intro x h
    rw [List.takeWhile_cons] at h
    split at h
    · next hy => rcases List.mem_cons.mp h with e | h'
                 · subst e; exact hy
                 · exact ih x h'
    · cases h

/-- On the ray of the move: everything before `d` is empty after the move, and
    `d` holds the mover's piece. -/
theorem atk_along (Q : Position) (a : Color) (mk : Nat) (d : Square) (M : Piece) (hM : M.color ≠ a)
    (hQd : Q.pieceAt d = some M) :
    ∀ L : List Square, d ∈ L → (∀ x ∈ L.takeWhile (· ≠ d), Q.pieceAt x = none) → atkFirst Q a mk L = false := by
  intro L; induction L with
  | nil => intro h; cases h
  | cons x r ih =>
    intro hd hpre
    rw [atkFirst_cons]
    by_cases hxd : x = d
    · subst hxd; rw [hQd]; simp [hM]
    · have htw : (x :: r).takeWhile (· ≠ d) = x :: r.takeWhile (· ≠ d) := by
        rw [List.takeWhile_cons, if_pos (by simpa using hxd)]
      have hx : Q.pieceAt x = none := hpre x (by rw [htw]; exact List.mem_cons_self)
      rw [hx]
      exact ih ((List.mem_cons.mp hd).resolve_left (Ne.symm hxd))
        (fun y hy => hpre y (by rw [htw]; exact List.mem_cons_of_mem _ hy))

/-- **Fast path, along the pin.** Not in check, a non-king piece on ray `r` of
    the king moves to `d` further along that ray with the ray clear before `d`
    (apart from its own square): the king stays safe. -/
theorem fastpath_along (p : Position) (hS : p.Shaped) (hK : KingsUnique p) {sq d : Square} {pr : Bool}
    (hm : Move.normal sq d pr ∈ p.pseudoMoves) {pc : Piece} (hpc : p.pieceAt sq = some pc)
    (hkt : pc.type ≠ .king) {k : Square} (hks : p.kingSquare p.side = some k) (hnc : p.inCheck p.side = false)
    {r : Nat} (hr : r < 8) (hsr : sq ∈ ray k (rdir r)) (hdr : d ∈ ray k (rdir r))
    (hclear : ∀ x ∈ (ray k (rdir r)).takeWhile (· ≠ d), x = sq ∨ p.pieceAt x = none) :
    (p.play (.normal sq d pr)).inCheck p.side = false := by
  obtain ⟨pc', hpc', hcol, hcap⟩ := pseudo_normal hm
  rw [hpc] at hpc'; cases hpc'
  have hds := pseudo_ne hm
  let q := p.play (.normal sq d pr)
  have hQ := play_normal_pieceAt p hS.1 (pr := pr) (d := d) hpc
  have hkq : q.kingSquare p.side = some k := by
    rw [play_normal_kingSquare p hS.1 hK hpc hcol (fun c' h => hcap _ h rfl)]
    unfold kingAfter; rw [if_neg (fun h => hkt h.1)]; exact hks
  unfold Position.inCheck at hnc ⊢
  rw [hks] at hnc; rw [hkq]
  simp only at hnc ⊢
  rw [Position.attacked_eq] at hnc ⊢
  simp only [Bool.or_eq_false_iff] at hnc ⊢
  obtain ⟨hstep, hray⟩ := hnc
  have hM : (movedPiece p.side pc pr).color = p.side := rfl
  have hMo : (movedPiece p.side pc pr).color ≠ p.side.opp := by rw [hM]; exact Ne.symm (opp_ne _)
  constructor
  · unfold Position.stepAttackedS at hstep ⊢
    rw [List.any_eq_false] at hstep ⊢
    intro x hx
    have := hstep x hx
    rw [hQ x]
    by_cases hxd : x = d
    · simp only [hxd, if_true, hM]
      have hne : (p.side == p.side.opp) = false := by cases p.side <;> rfl
      simp [hne]
    · rw [if_neg hxd]
      by_cases hxs : x = sq
      · simp [hxs]
      · rw [if_neg hxs]; exact this
  · rw [rayAttacked_atk] at hray ⊢
    rw [List.any_eq_false] at hray ⊢
    intro dir hdir
    have hdr' := hray dir hdir
    simp only [Bool.not_eq_true] at hdr' ⊢
    obtain ⟨r', hr', rfl⟩ : ∃ r', r' < 8 ∧ dir = rdir r' := by
      rw [rayDirs_eq, List.mem_map] at hdir; obtain ⟨r', hr', e⟩ := hdir; exact ⟨r', List.mem_range.mp hr', e.symm⟩
    by_cases hrr : r' = r
    · subst hrr
      refine atk_along q p.side.opp _ d (movedPiece p.side pc pr) hMo (by rw [hQ d]; simp) _ hdr (fun x hx => ?_)
      have hxd : x ≠ d := by have := mem_takeWhile_pred _ _ x hx; simpa using this
      rw [hQ x, if_neg hxd]
      rcases hclear x hx with h | h
      · simp [h]
      · split <;> simp [h]
    · refine ray_safe p q p.side _ sq d (movedPiece p.side pc pr) pc hQ hM hpc hcol hds _
        (Position.ray_nodup k hdir) hdr' ?_
      intro hpin
      rcases kres_snd_mem p p.side _ _ none sq hpin with h | h
      · exact ray_disj k hr hr' (Ne.symm hrr) hsr h
      · cases h

end Shogi.C.Proofs
