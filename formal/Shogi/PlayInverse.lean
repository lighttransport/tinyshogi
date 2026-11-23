/-
  Spec-level inverse of `Position.play`.  The C make/unmake proofs need the
  fact that undoing a pseudo-legal move restores the pre-move position; this
  file records that fact at the abstraction level, independently of the C.
-/
import Shogi.Rules
import Shogi.Theorems
import Shogi.AttackSpec

namespace Shogi

/-- Undo `m` from `p.play m`, using the pre-move position `p` to restore
    whatever `play` overwrote (the source square and a captured piece). -/
def unplay (p : Position) (m : Move) : Position :=
  let q := p.play m
  match m with
  | .drop t d =>
      match t.handIndex with
      | some i => { q with board := Position.setSq q.board d none,
                           hands := q.hands.set p.side i (q.hand p.side i + 1),
                           side := p.side, moveNumber := p.moveNumber }
      | none => q
  | .normal s d _ =>
      { q with board := Position.setSq (Position.setSq q.board d (p.pieceAt d)) s (p.pieceAt s),
               hands := p.hands, side := p.side, moveNumber := p.moveNumber }

/-! ### List helpers (indexed extensionality) -/

theorem setList_getElem? {α : Type _} {l : List α} {i : Nat} {a : α} {j : Nat} :
    (l.set i a)[j]? = if i = j then (if i < l.length then some a else none) else l[j]? := by
  simpa using (List.getElem?_set (l := l) (i := i) (j := j) (a := a))

theorem setList_ne {α : Type _} {l : List α} {i j : Nat} {a : α} (hij : i ≠ j) :
    (l.set i a)[j]? = l[j]? := by
  simp [setList_getElem?, hij]

theorem setList_self {α : Type _} {l : List α} {i : Nat} {a : α} (hi : i < l.length) :
    (l.set i a)[i]? = some a := by
  simp [setList_getElem?, hi]

theorem setList_getD_ne {α : Type _} {l : List α} {i j : Nat} {a d : α} (hij : i ≠ j) :
    (l.set i a).getD j d = l.getD j d := by
  unfold List.getD
  rw [setList_ne hij]

theorem setList_restore {α : Type _} {l : List α} {i : Nat} {d : α}
    (hi : i < l.length) : l.set i (l.getD i d) = l := by
  apply List.ext_getElem?
  intro j
  by_cases hji : j = i
  · subst j
    rw [setList_self hi]
    simp [List.getD, hi]
  · rw [setList_ne (fun h => hji h.symm)]

theorem setList_sub_add {l : List Nat} {i : Nat} (hi : i < l.length) (hc : 0 < l.getD i 0) :
    l.set i ((l.set i (l.getD i 0 - 1)).getD i 0 + 1) = l := by
  apply List.ext_getElem?
  intro j
  by_cases hji : j = i
  · subst j
    have hci : 0 < l[i] := by simpa [List.getD, hi] using hc
    simp [List.getD, hi, Nat.sub_add_cancel hci]
  · rw [setList_ne (fun h => hji h.symm)]

theorem setList_comm {α : Type _} {l : List α} {i j : Nat} {a b : α} (hij : i ≠ j) :
    (l.set i a).set j b = (l.set j b).set i a := by
  apply List.ext_getElem?
  intro k
  simp only [setList_getElem?]
  by_cases hik : i = k
  · subst k
    have hji : ¬ j = i := fun h => hij h.symm
    simp [hji, hij]
  · by_cases hjk : j = k
    · subst k
      simp [hij, hik]
    · simp [hik, hjk]

/-! ### Round trip -/

theorem unplay_drop (p : Position) (hS : p.Shaped) (t : PieceType) (d : Square)
    (hidx : ∃ i, t.handIndex = some i) (hempty : p.isEmpty d)
    (hcnt : ∀ i, t.handIndex = some i → 0 < p.hand p.side i) :
    unplay p (.drop t d) = p := by
  rcases hidx with ⟨i, hi⟩
  rcases p with ⟨board, hands, side, moveNumber⟩
  simp only [Position.Shaped] at hS
  simp only [hi] at hcnt ⊢
  have hi_lt : i.val < 7 := i.isLt
  have hd_lt : d.val < board.length := by rw [hS.1]; exact d.isLt
  have hget : board.getD d.val none = none := by
    simpa [Position.isEmpty, Position.pieceAt] using hempty
  simp only [unplay, Position.play, Position.setSq, hi, Position.pieceAt]
  congr 1
  · rw [List.set_set]
    have hh := setList_restore (l := board) (i := d.val) (d := none) hd_lt
    rw [hget] at hh
    exact hh
  · cases hands with
    | mk bl wh =>
      cases side
      · simp only [Hands.set, Hands.get, Position.hand] at hcnt ⊢
        congr 1
        rw [List.set_set]
        exact setList_sub_add (by rw [hS.2.1]; exact hi_lt) (by simpa using hcnt i rfl)
      · simp only [Hands.set, Hands.get, Position.hand] at hcnt ⊢
        congr 1
        rw [List.set_set]
        exact setList_sub_add (by rw [hS.2.2]; exact hi_lt) (by simpa using hcnt i rfl)

theorem unplay_normal (p : Position) (hS : p.Shaped) (s d : Square) (pr : Bool) (hsne : s ≠ d)
    (hocc : ∃ pc, p.pieceAt s = some pc) :
    unplay p (.normal s d pr) = p := by
  have hs_lt : s.val < p.board.length := by rw [hS.1]; exact s.isLt
  have hd_lt : d.val < p.board.length := by rw [hS.1]; exact d.isLt
  have hsd : s.val ≠ d.val := fun h => hsne (Fin.ext h)
  rcases hocc with ⟨pc, hpc⟩
  rcases p with ⟨board, hands, side, moveNumber⟩
  simp only [Position.pieceAt] at hpc
  simp only [hpc, unplay, Position.play, Position.setSq, Position.pieceAt] at hs_lt hd_lt hsd ⊢
  congr 1
  rw [List.set_set]
  have hget : (board.set s.val none).getD d.val none = board.getD d.val none := by
    unfold List.getD
    simp only [List.getElem?_set]
    simp [hsd]
  rw [← hget]
  rw [setList_restore (l := board.set s.val none) (i := d.val) (d := none) (by simpa using hd_lt)]
  rw [List.set_set]
  rw [← hpc]
  exact setList_restore hs_lt




/-! ### A square never attacks itself -/

theorem square_offset_ne_self (s : Square) (o : Int × Int) (hone : o ≠ (0, 0)) :
    Square.offset s o ≠ some s := by
  unfold Square.offset Square.mk?
  split
  · rename_i h
    intro heq
    simp only [Option.some.injEq] at heq
    have heqv : (((s.row : Int) + o.1) * 9 + ((s.col : Int) + o.2)).toNat = s.val :=
      congrArg Fin.val heq
    have hnonneg : 0 ≤ ((s.row : Int) + o.1) * 9 + ((s.col : Int) + o.2) := by omega
    have hto : ((((s.row : Int) + o.1) * 9 + ((s.col : Int) + o.2)).toNat : Int) =
        ((s.row : Int) + o.1) * 9 + ((s.col : Int) + o.2) := by omega
    have heqvi : ((((s.row : Int) + o.1) * 9 + ((s.col : Int) + o.2)).toNat : Int) =
        (s.val : Int) := by rw [heqv]
    rw [hto] at heqvi
    have hv : s.val = s.row * 9 + s.col := by
      rw [Square.row, Square.col]
      have := Nat.div_add_mod s.val 9
      omega
    have hcol : s.col < 9 := Nat.mod_lt _ (by decide)
    have hvi : (s.val : Int) = (s.row : Int) * 9 + (s.col : Int) := by omega
    have h1 : o.1 = 0 := by omega
    have h2 : o.2 = 0 := by omega
    exact hone (Prod.ext h1 h2)
  · intro h; cases h

theorem stepOffsets_ne_zero_color : ∀ c : Color, ∀ t : PieceType, ∀ o ∈ stepOffsets c.fwd t,
    o ≠ (0, 0) := by
  intro c t
  cases c <;> cases t <;> simp [stepOffsets, Color.fwd] <;> intro o ho <;> omega

theorem ray_ne_self_finite : ∀ s : Square, ∀ d ∈ Shogi.Tables.rayDirs,
    ∀ t ∈ ray s d, t ≠ s := by
  decide +kernel

theorem slideTargets_go_sub (p : Position) {L : List Square} {t : Square} :
    t ∈ Position.slideTargets.go p L → t ∈ L := by
  induction L with
  | nil => intro h; cases h
  | cons x xs ih =>
      intro h
      simp only [Position.slideTargets.go] at h
      by_cases he : p.isEmpty x
      · rw [if_pos he] at h
        simp only [List.mem_cons] at h
        rcases h with rfl | h
        · simp
        · exact List.mem_cons_of_mem _ (ih h)
      · rw [if_neg he] at h
        simp only [List.mem_singleton] at h
        subst t
        simp

theorem slideTargets_sub (p : Position) (s : Square) (d : Int × Int) {t : Square}
    (h : t ∈ p.slideTargets s d) : t ∈ ray s d := by
  unfold Position.slideTargets at h
  exact slideTargets_go_sub p h

theorem attackSquares_ne_self (p : Position) (s : Square) (pc : Piece) {d : Square}
    (h : d ∈ p.attackSquares s pc) : d ≠ s := by
  unfold Position.attackSquares at h
  rw [List.mem_append] at h
  rcases h with h | h
  · rw [List.mem_filterMap] at h
    rcases h with ⟨o, ho, hsome⟩
    intro hds
    have hone := stepOffsets_ne_zero_color pc.color pc.type o ho
    have hself : Square.offset s o = some s := by simpa [hds] using hsome
    exact square_offset_ne_self s o hone hself
  · rw [List.mem_flatMap] at h
    rcases h with ⟨v, hv, ht⟩
    exact ray_ne_self_finite s v (Position.slideDirs_sub pc.color pc.type v hv) d
      (slideTargets_sub p s v ht)

theorem boardMoves_mem_attack {p : Position} {s : Square} {pc : Piece} {m : Move}
    (h : m ∈ p.boardMoves s pc) : ∃ d pr, m = Move.normal s d pr ∧ d ∈ p.attackSquares s pc := by
  unfold Position.boardMoves at h
  rw [List.mem_flatMap] at h
  rcases h with ⟨d, hd, hrest⟩
  cases hpd : p.pieceAt d with
  | none =>
      simp [hpd] at hrest
      rcases hrest with ⟨_, hm⟩ | ⟨_, hm⟩
      · exact ⟨d, false, hm.symm, hd⟩
      · exact ⟨d, true, hm.symm, hd⟩
  | some q =>
      by_cases hcapb : (q.color == pc.color || q.type == PieceType.king) = true
      · simp [hpd, hcapb] at hrest
      · simp [hpd, hcapb] at hrest
        rcases hrest with ⟨_, hm⟩ | ⟨_, hm⟩
        · exact ⟨d, false, hm.symm, hd⟩
        · exact ⟨d, true, hm.symm, hd⟩

/-- A pseudo-legal drop always satisfies the hypotheses of `unplay_drop`. -/
theorem unplay_pseudo_drop (p : Position) (hS : p.Shaped) (t : PieceType) (d : Square)
    (hm : Move.drop t d ∈ p.pseudoMoves) : unplay p (.drop t d) = p := by
  have hdrop : Move.drop t d ∈ p.dropMoves := by
    simp only [Position.pseudoMoves, List.mem_append] at hm
    rcases hm with h | h
    · exfalso
      rw [List.mem_flatMap] at h
      rcases h with ⟨s', _, hs'⟩
      cases hp : p.pieceAt s' with
      | none => simp [Position.boardMoves, hp] at hs'
      | some pc =>
          simp [Position.boardMoves, hp] at hs'
          rcases hs' with ⟨hcolor, a, ha, hmboard⟩
          cases hpa : p.pieceAt a with
          | none => simp [hpa] at hmboard
          | some q =>
              by_cases hcap : q.color == pc.color ∨ q.type == PieceType.king <;>
                simp [hpa, hcap] at hmboard
    · exact h
  obtain ⟨i, d', hmv, hcnt, hallow⟩ := Shogi.Position.mem_dropMoves hdrop
  cases hmv
  simp only [Position.dropAllowed] at hallow
  have hempty : p.isEmpty d = true := by
    cases h : p.isEmpty d <;> simp [h] at hallow ⊢
  exact unplay_drop p hS (PieceType.ofHandIndex i) d
    ⟨i, PieceType.handIndex_ofHandIndex i⟩ hempty (by
      intro j hj
      have hs : some i = some j := by simpa [PieceType.handIndex_ofHandIndex] using hj
      cases hs
      exact hcnt)


/-- A pseudo-legal board move always satisfies the hypotheses of `unplay_normal`. -/
theorem unplay_pseudo_normal (p : Position) (hS : p.Shaped) (s d : Square) (pr : Bool)
    (hm : Move.normal s d pr ∈ p.pseudoMoves) : unplay p (.normal s d pr) = p := by
  rcases Position.mem_pseudoMoves hm with ⟨s', pc, hpc, hcolor, hboard⟩ | hdrop
  · obtain ⟨d', pr', heq, hdatk⟩ := boardMoves_mem_attack hboard
    injection heq with hs hdpr
    subst s'
    subst d'
    exact unplay_normal p hS s d pr
      (fun h => attackSquares_ne_self p s pc hdatk h.symm) ⟨pc, hpc⟩
  · exfalso
    simp [Position.dropMoves] at hdrop


/-- Every pseudo-legal move is undone by `unplay`. -/
theorem unplay_pseudo (p : Position) (hS : p.Shaped) (m : Move) (hm : m ∈ p.pseudoMoves) :
    unplay p m = p := by
  cases m with
  | drop t d => exact unplay_pseudo_drop p hS t d hm
  | normal s d pr => exact unplay_pseudo_normal p hS s d pr hm


/-! ### Pawn attack geometry (toward the checking-pawn-drop bound) -/

/-- In this model a pawn attacks exactly one square: the one directly forward.
    Consequently `k` is attacked by a pawn on `d` iff `d` offsets to `k`. -/
theorem pawn_attackSquares_mem (p : Position) (c : Color) (d k : Square) :
    k ∈ p.attackSquares d ⟨c, .pawn⟩ ↔ Square.offset d (c.fwd, 0) = some k := by
  cases c
  · cases h : Square.offset d ((-1 : Int), 0) <;>
      simp [Position.attackSquares, stepOffsets, slideDirs, Color.fwd, List.filterMap, h, eq_comm]
  · cases h : Square.offset d ((1 : Int), 0) <;>
      simp [Position.attackSquares, stepOffsets, slideDirs, Color.fwd, List.filterMap, h, eq_comm]

/-- `Square.offset` by a fixed displacement is injective on its domain: two
    squares whose pawn attacks land on the same square are equal. -/
theorem square_offset_injective (o : Int × Int) {s t u : Square}
    (hs : Square.offset s o = some u) (ht : Square.offset t o = some u) : s = t := by
  apply Fin.ext
  unfold Square.offset Square.mk? at hs ht
  split at hs
  · rename_i hsok
    split at ht
    · rename_i htok
      simp only [Option.some.injEq] at hs ht
      have hsv : (((s.row : Int) + o.1) * 9 + ((s.col : Int) + o.2)).toNat = u.val :=
        congrArg Fin.val hs
      have htv : (((t.row : Int) + o.1) * 9 + ((t.col : Int) + o.2)).toNat = u.val :=
        congrArg Fin.val ht
      have hsn : 0 ≤ ((s.row : Int) + o.1) * 9 + ((s.col : Int) + o.2) := by omega
      have htn : 0 ≤ ((t.row : Int) + o.1) * 9 + ((t.col : Int) + o.2) := by omega
      have hsi : ((((s.row : Int) + o.1) * 9 + ((s.col : Int) + o.2)).toNat : Int) =
          ((s.row : Int) + o.1) * 9 + ((s.col : Int) + o.2) := by omega
      have hti : ((((t.row : Int) + o.1) * 9 + ((t.col : Int) + o.2)).toNat : Int) =
          ((t.row : Int) + o.1) * 9 + ((t.col : Int) + o.2) := by omega
      have hsvi : ((s.row : Int) + o.1) * 9 + ((s.col : Int) + o.2) = (u.val : Int) := by
        have hh := congrArg (fun n : Nat => (n : Int)) hsv
        rw [hsi] at hh
        exact hh
      have htvi : ((t.row : Int) + o.1) * 9 + ((t.col : Int) + o.2) = (u.val : Int) := by
        have hh := congrArg (fun n : Nat => (n : Int)) htv
        rw [hti] at hh
        exact hh
      have huv : (u.val : Int) = (u.row : Int) * 9 + (u.col : Int) := by
        rw [Square.row, Square.col]
        have := Nat.div_add_mod u.val 9
        omega
      have hscol : (s.col : Int) + o.2 = (u.col : Int) := by
        have hc := hsok.2.1
        have hucol : u.col < 9 := Nat.mod_lt _ (by omega)
        omega
      have htcol : (t.col : Int) + o.2 = (u.col : Int) := by
        have hc := htok.2.1
        have hucol : u.col < 9 := Nat.mod_lt _ (by omega)
        omega
      have hsrow : (s.row : Int) + o.1 = (u.row : Int) := by
        have hurowlt : u.row < 9 := Nat.div_lt_of_lt_mul (by omega : u.val < 81)
        omega
      have htrow : (t.row : Int) + o.1 = (u.row : Int) := by
        have hurowlt : u.row < 9 := Nat.div_lt_of_lt_mul (by omega : u.val < 81)
        omega
      have hrow : s.row = t.row := by omega
      have hcol : s.col = t.col := by omega
      have hsval : s.val = s.row * 9 + s.col := by
        rw [Square.row, Square.col]
        have := Nat.div_add_mod s.val 9
        omega
      have htval : t.val = t.row * 9 + t.col := by
        rw [Square.row, Square.col]
        have := Nat.div_add_mod t.val 9
        omega
      omega
    · cases ht
  · cases hs

/-- At most one square can carry a pawn that attacks a given king square
    (for a fixed mover).  This is the geometric core of the bound on checking
    pawn drops: a pawn drop gives check from only one possible destination. -/
theorem pawn_drop_attack_unique (p : Position) (d₁ d₂ k : Square)
    (h₁ : Square.offset d₁ (p.side.fwd, 0) = some k)
    (h₂ : Square.offset d₂ (p.side.fwd, 0) = some k) : d₁ = d₂ :=
  square_offset_injective (p.side.fwd, 0) h₁ h₂

end Shogi
