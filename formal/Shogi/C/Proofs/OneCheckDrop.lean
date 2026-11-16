/-
  T8/M3: at most one pawn drop gives check to the opponent.

  A pawn attacks exactly one square (directly forward), and adding a piece
  never shortens another piece's attack set.  So if the side not to move is
  not in check, a dropped pawn can only create a check by attacking the
  opponent's king itself; the drop square is then determined by the king
  square, and `dropMoves` emits at most one pawn drop per square.
-/
import Shogi.Rules
import Shogi.Theorems
import Shogi.C.Proofs.PlaySpec

namespace Shogi.C.Proofs
open Shogi

/-! ### The board after a pawn drop -/

theorem play_drop_pieceAt (p : Position) (hS : p.board.length = 81) (d s : Square) :
    (p.play (Move.drop .pawn d)).pieceAt s =
      if s.val = d.val then some ⟨p.side, .pawn⟩ else p.pieceAt s := by
  have hb : (p.play (Move.drop .pawn d)).board = p.board.set d.val (some ⟨p.side, .pawn⟩) := by
    simp [Position.play, Position.setSq, PieceType.handIndex]
  simp only [Position.pieceAt]
  rw [hb, List.getD_eq_getElem?_getD, List.getElem?_set]
  by_cases hx : s.val = d.val
  · rw [if_pos hx.symm, if_pos (by rw [hS]; omega), if_pos hx]
    simp
  · rw [if_neg (Ne.symm hx), List.getD_eq_getElem?_getD, if_neg hx]

theorem play_drop_pieceAt_ne {p : Position} (hS : p.board.length = 81) {d s : Square}
    (h : s.val ≠ d.val) :
    (p.play (Move.drop .pawn d)).pieceAt s = p.pieceAt s := by
  rw [play_drop_pieceAt p hS, if_neg h]

theorem play_drop_self (p : Position) (hS : p.board.length = 81) (d : Square) :
    (p.play (Move.drop .pawn d)).pieceAt d = some ⟨p.side, .pawn⟩ := by
  rw [play_drop_pieceAt p hS, if_pos rfl]

theorem play_drop_side (p : Position) (d : Square) :
    (p.play (Move.drop .pawn d)).side = p.side.opp := rfl

/-- Dropping a pawn (on any square, empty or not) does not move the king of
    colour `c`, provided the drop square does not hold that king. -/
theorem play_drop_kingSquare {p : Position} (hS : p.board.length = 81) {d : Square} (c : Color)
    (hE : p.pieceAt d ≠ some ⟨c, .king⟩) :
    (p.play (Move.drop .pawn d)).kingSquare c = p.kingSquare c := by
  apply kingSquare_iff
  intro x
  rw [play_drop_pieceAt p hS]
  by_cases hx : x.val = d.val
  · have xe : x = d := Fin.val_inj.mp hx
    subst xe
    rw [if_pos rfl]
    simp [hE]
  · rw [if_neg hx]

/-! ### Slides never get longer when a piece is added -/

theorem slideTargets_go_mono {p q : Position}
    (hE : ∀ x, q.pieceAt x = none → p.pieceAt x = none)
    {r : List Square} {k : Square} :
    k ∈ Position.slideTargets.go q r → k ∈ Position.slideTargets.go p r := by
  induction r with
  | nil => intro h; simp only [Position.slideTargets.go] at h; cases h
  | cons t r ih =>
    intro h
    by_cases hq : q.isEmpty t
    · have hp : p.isEmpty t := by simpa [Position.isEmpty] using hE t (by simpa [Position.isEmpty] using hq)
      have e1 : Position.slideTargets.go q (t :: r) = t :: Position.slideTargets.go q r := by
        simp [Position.slideTargets.go, hq]
      rw [e1] at h
      rcases List.mem_cons.mp h with he | hm
      · rw [he]
        rw [show Position.slideTargets.go p (t :: r) = t :: Position.slideTargets.go p r from
          (by simp [Position.slideTargets.go, hp])]
        exact List.mem_cons_self
      · rw [show Position.slideTargets.go p (t :: r) = t :: Position.slideTargets.go p r from
          (by simp [Position.slideTargets.go, hp])]
        exact List.mem_cons_of_mem _ (ih hm)
    · have e2 : Position.slideTargets.go q (t :: r) = [t] := by
        simp [Position.slideTargets.go, hq]
      rw [e2] at h
      rcases List.mem_cons.mp h with he | hm
      · rw [he]
        by_cases hp : p.isEmpty t
        · rw [show Position.slideTargets.go p (t :: r) = t :: Position.slideTargets.go p r from
            (by simp [Position.slideTargets.go, hp])]
          exact List.mem_cons_self
        · rw [show Position.slideTargets.go p (t :: r) = [t] from
            (by simp [Position.slideTargets.go, hp])]
          exact List.mem_cons_self
      · exact absurd hm (by simp)

theorem attackSquares_mono {p q : Position} {s : Square} {pc : Piece} {k : Square}
    (hE : ∀ x, q.pieceAt x = none → p.pieceAt x = none)
    (hmem : k ∈ q.attackSquares s pc) : k ∈ p.attackSquares s pc := by
  unfold Position.attackSquares at hmem ⊢
  rw [List.mem_append] at hmem ⊢
  rcases hmem with h | h
  · exact Or.inl h
  · right
    rw [List.mem_flatMap] at h ⊢
    obtain ⟨dir, hd, hm⟩ := h
    exact ⟨dir, hd, slideTargets_go_mono hE hm⟩

/-! ### A pawn attacks exactly one square -/

theorem pawn_attackSquares (q : Position) (c : Color) (d : Square) :
    q.attackSquares d ⟨c, .pawn⟩ =
      match d.offset (c.fwd, 0) with | some u => [u] | none => [] := by
  simp only [Position.attackSquares, stepOffsets, slideDirs, List.filterMap_cons,
    List.filterMap_nil]
  cases ho : d.offset (c.fwd, 0) <;> simp [ho]

theorem offset_fwd_eq {d k : Square} {f : Int} (h : d.offset (f, 0) = some k) :
    ((k.val : Int)) = ((d.val : Int)) + f * 9 := by
  unfold Square.offset Square.mk? at h
  split at h
  · next hpos =>
    rw [Option.some_inj] at h
    have hv : k.val = (((Square.row d : Int) + f) * 9 + ((Square.col d : Int) + 0)).toNat := by
      rw [← h]
    unfold Square.row Square.col at hv hpos
    rw [Int.add_mul] at hv
    omega
  · exact absurd h (by simp)

/-! ### Uniqueness of the checking pawn drop -/

/-- If the side not to move is not in check, a checking pawn drop attacks the
    opponent's king itself, which pins its square. -/
theorem checkingPawnDrop_unique {p : Position} (hS : p.Shaped) (hK : KingsUnique p)
    (hnc : p.inCheck p.side.opp = false)
    {d1 d2 : Square}
    (hc1 : (p.play (Move.drop .pawn d1)).inCheck (p.play (Move.drop .pawn d1)).side = true)
    (hc2 : (p.play (Move.drop .pawn d2)).inCheck (p.play (Move.drop .pawn d2)).side = true) :
    d1 = d2 := by
  have key : ∀ d : Square,
      (p.play (Move.drop .pawn d)).inCheck (p.play (Move.drop .pawn d)).side = true →
      ∃ kk, p.kingSquare p.side.opp = some kk ∧
        ((kk.val : Int)) = ((d.val : Int)) + p.side.fwd * 9 := by
    intro d hc
    have hside : (p.play (Move.drop .pawn d)).side = p.side.opp := play_drop_side p d
    have hEq : ∀ x, (p.play (Move.drop .pawn d)).pieceAt x = none → p.pieceAt x = none := by
      intro x hx
      rw [play_drop_pieceAt p hS.1] at hx
      split at hx
      · simp at hx
      · exact hx
    -- the drop square does not hold the opponent's king: otherwise the drop
    -- would remove that (unique) king and the position would not be in check
    have hE : p.pieceAt d ≠ some ⟨p.side.opp, .king⟩ := by
      intro hKd
      have hKq' : (p.play (Move.drop .pawn d)).kingSquare p.side.opp = none := by
        apply kingSquare_none
        intro x hx
        rw [play_drop_pieceAt p hS.1] at hx
        by_cases hxv : x.val = d.val
        · have xe : x = d := Fin.val_inj.mp hxv
          subst xe
          rw [if_pos rfl] at hx
          simp at hx
        · rw [if_neg hxv] at hx
          exact absurd (hK p.side.opp x d hx hKd) (by
            intro e
            exact hxv (congrArg (fun s : Square => s.val) e))
      unfold Position.inCheck at hc
      rw [hside, hKq'] at hc
      simp at hc
    have hKq : (p.play (Move.drop .pawn d)).kingSquare p.side.opp = p.kingSquare p.side.opp :=
      play_drop_kingSquare hS.1 (p.side.opp) hE
    have hksome : (p.play (Move.drop .pawn d)).kingSquare
        ((p.play (Move.drop .pawn d)).side) ≠ none := by
      intro hnone
      unfold Position.inCheck at hc
      rw [hnone] at hc
      simp at hc
    obtain ⟨kk, hkk⟩ := Option.ne_none_iff_exists.mp hksome
    rw [hside] at hkk
    have hkkv : p.kingSquare p.side.opp = some kk := hKq.symm.trans hkk.symm
    have hc' : (p.play (Move.drop .pawn d)).attacked kk p.side = true := by
      unfold Position.inCheck at hc
      rw [hside, hKq, hkkv] at hc
      simpa using hc
    unfold Position.attacked at hc'
    rw [List.any_eq_true] at hc'
    obtain ⟨s, _, hf⟩ := hc'
    cases hpq : (p.play (Move.drop .pawn d)).pieceAt s with
    | none => rw [hpq] at hf; simp at hf
    | some pc =>
      rw [hpq] at hf
      simp only [Bool.and_eq_true, beq_iff_eq, List.contains_iff_mem] at hf
      have hcol : pc.color = p.side := hf.1
      by_cases hsd : s.val = d.val
      · -- the dropped pawn itself attacks the king
        have hsq : s = d := Fin.val_inj.mp hsd
        rw [hsq] at hpq hf
        have hpc : pc = ⟨p.side, .pawn⟩ := by
          rw [play_drop_self p hS.1] at hpq
          exact Option.some_inj.mp hpq.symm
        rw [hpc] at hf
        rw [pawn_attackSquares] at hf
        cases ho : d.offset (p.side.fwd, 0) with
        | none => rw [ho] at hf; simp at hf
        | some u =>
          simp only [ho] at hf
          rcases List.mem_cons.mp hf.2 with hh | hh2
          · rw [hh] at hkkv
            exact ⟨u, hkkv, offset_fwd_eq ho⟩
          · exact absurd hh2 (by simp)
      · -- an existing piece attacks the king: it already attacked it before
        have hp' : p.pieceAt s = some pc :=
          (play_drop_pieceAt_ne hS.1 (s := s) hsd).symm.trans hpq
        have hmem : kk ∈ p.attackSquares s pc :=
          attackSquares_mono (p := p) (q := p.play (Move.drop .pawn d)) hEq hf.2
        have hatt : p.attacked kk p.side = true := by
          unfold Position.attacked
          rw [List.any_eq_true]
          exact ⟨s, List.mem_finRange s, by simp [hp', hcol, hmem]⟩
        have hin : p.inCheck p.side.opp = true := by
          unfold Position.inCheck
          rw [hkkv]
          simpa using hatt
        exact absurd hin (by rw [hnc]; simp)
  obtain ⟨kk1, eq1, v1⟩ := key d1 hc1
  obtain ⟨kk2, eq2, v2⟩ := key d2 hc2
  have hkk : kk1 = kk2 := Option.some_inj.mp (eq1.symm.trans eq2)
  have v2' : ((kk1.val : Int)) = ((d2.val : Int)) + p.side.fwd * 9 := by
    rw [hkk]; exact v2
  have : d1.val = d2.val := by
    have h := v1.symm.trans v2'
    omega
  exact Fin.val_inj.mp this

/-! ### A drop value occurs at most once in `dropMoves` -/

theorem filterMap_as_flatMap {α β : Type} (f : α → Option β) (l : List α) :
    l.filterMap f = l.flatMap (fun x => match f x with | some y => [y] | none => []) := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    cases h : f a with
    | none => simp [List.filterMap_cons, List.flatMap_cons, h, ih]
    | some b => simp [List.filterMap_cons, List.flatMap_cons, h, ih]

theorem filter_flatMap_comm {α β : Type} [DecidableEq β] (l : List α) (g : α → List β) (v : β) :
    (l.flatMap g).filter (fun x => decide (x = v)) =
      l.flatMap (fun x => (g x).filter (fun x => decide (x = v))) := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    rw [List.flatMap_cons, List.filter_append, ih, List.flatMap_cons]

theorem flatMap_nil_of_forall {α β : Type} (l : List α) (g : α → List β)
    (h : ∀ x ∈ l, g x = []) : l.flatMap g = [] := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    rw [List.flatMap_cons, h a (List.mem_cons_self),
      ih (fun x hx => h x (List.mem_cons_of_mem _ hx))]
    simp

theorem flatMap_single {α β : Type} (l : List α) (a₀ : α) (g : α → List β)
    (h₀ : a₀ ∈ l) (hnd : l.Nodup) (h : ∀ x ∈ l, x ≠ a₀ → g x = []) :
    l.flatMap g = g a₀ := by
  induction l with
  | nil => cases h₀
  | cons a l ih =>
    by_cases he : a = a₀
    · subst he
      rw [List.flatMap_cons, flatMap_nil_of_forall l g (fun x hx => h x
        (List.mem_cons_of_mem _ hx) (fun e => (List.nodup_cons.mp hnd).1 (e ▸ hx)))]
      simp
    · rw [List.flatMap_cons, h a (List.mem_cons_self) he, List.nil_append]
      exact ih ((List.mem_cons.mp h₀).resolve_left (Ne.symm he)) (List.nodup_cons.mp hnd).2
        (fun x hx => h x (List.mem_cons_of_mem _ hx))

theorem ofHandIndex_eq_pawn (i : Fin 7) : PieceType.ofHandIndex i = .pawn ↔ i.val = 0 := by
  revert i; decide

theorem filterMap_nodup_of_inj {α β : Type} (f : α → Option β) (l : List α)
    (hnd : l.Nodup) (hinj : ∀ a b y, f a = some y → f b = some y → a = b) :
    (l.filterMap f).Nodup := by
  induction l with
  | nil => simp
  | cons a l ih =>
    cases h : f a with
    | none =>
      rw [List.filterMap_cons, h]
      exact ih (List.nodup_cons.mp hnd).2
    | some w =>
      rw [List.filterMap_cons, h, List.nodup_cons]
      refine ⟨?_, ih (List.nodup_cons.mp hnd).2⟩
      intro hmem
      rw [List.mem_filterMap] at hmem
      obtain ⟨b, hb, hbw⟩ := hmem
      exact absurd (hinj a b w h hbw) (by
        intro e; subst e; exact (List.nodup_cons.mp hnd).1 hb)

def dropCell (p : Position) (x : Square) (i : Fin 7) : Option Move :=
  if p.hand p.side i > 0 && p.dropAllowed p.side (PieceType.ofHandIndex i) x then
    some (.drop (PieceType.ofHandIndex i) x) else none

theorem dropMoves_eq (p : Position) :
    p.dropMoves = (List.finRange 81).flatMap (fun x => (List.finRange 7).filterMap (dropCell p x)) := rfl

theorem dropCell_val {p : Position} {x : Square} {i : Fin 7} {w : Move}
    (h : dropCell p x i = some w) : w = .drop (PieceType.ofHandIndex i) x := by
  unfold dropCell at h
  split at h
  · exact (Option.some_inj.mp h).symm
  · simp at h

theorem dropCell_inj {p : Position} {x : Square} {i j : Fin 7} {w : Move}
    (h1 : dropCell p x i = some w) (h2 : dropCell p x j = some w) : i = j := by
  have e1 := dropCell_val h1
  have e2 := dropCell_val h2
  have h : Move.drop (PieceType.ofHandIndex i) x = Move.drop (PieceType.ofHandIndex j) x :=
    e1.symm.trans e2
  have hinj := Move.drop.inj h
  have hh : (PieceType.ofHandIndex i).handIndex = (PieceType.ofHandIndex j).handIndex := by
    rw [hinj.1]
  rw [PieceType.handIndex_ofHandIndex, PieceType.handIndex_ofHandIndex] at hh
  exact Option.some_inj.mp hh

theorem cell_nodup (p : Position) (x : Square) :
    ((List.finRange 7).filterMap (dropCell p x)).Nodup := by
  refine filterMap_nodup_of_inj (dropCell p x) (List.finRange 7) (List.nodup_finRange 7) ?_
  intro a b y h1 h2
  exact dropCell_inj h1 h2

/-- A move in a cell determined by square `x` has destination `x`. -/
theorem cell_dst {p : Position} {x : Square} {w : Move}
    (h : w ∈ (List.finRange 7).filterMap (dropCell p x)) : w.dst = x := by
  rw [List.mem_filterMap] at h
  obtain ⟨i, _, hi⟩ := h
  rw [dropCell_val hi]; rfl



/-- Distinct squares give disjoint cell move sets (a drop's destination is its
    square). -/
theorem cells_disjoint {p : Position} {x y : Square} (hxy : x ≠ y) {w : Move}
    (hx : w ∈ (List.finRange 7).filterMap (dropCell p x))
    (hy : w ∈ (List.finRange 7).filterMap (dropCell p y)) : False := by
  have e1 := cell_dst hx
  have e2 := cell_dst hy
  exact hxy (e1.symm.trans e2)



theorem flatMap_nodup {α β : Type} (l : List α) (g : α → List β)
    (hnd : l.Nodup)
    (hcell : ∀ x ∈ l, (g x).Nodup)
    (hdisj : ∀ x ∈ l, ∀ y ∈ l, x ≠ y → ∀ a ∈ g x, ∀ b ∈ g y, a ≠ b) :
    (l.flatMap g).Nodup := by
  induction l with
  | nil => simp
  | cons a t ih =>
    rw [List.flatMap_cons, List.nodup_append]
    have hnd' := List.nodup_cons.mp hnd
    refine ⟨hcell a List.mem_cons_self, ?_, ?_⟩
    · exact ih hnd'.2
        (fun x hx => hcell x (List.mem_cons_of_mem a hx))
        (fun x hx y hy hxy => hdisj x (List.mem_cons_of_mem a hx)
          y (List.mem_cons_of_mem a hy) hxy)
    · intro p hp q hq
      rw [List.mem_flatMap] at hq
      obtain ⟨y, hy, hqy⟩ := hq
      exact hdisj a List.mem_cons_self y (List.mem_cons_of_mem a hy)
        (fun e => hnd'.1 (e ▸ hy)) p hp q hqy



theorem dropMoves_nodup (p : Position) : p.dropMoves.Nodup := by
  rw [dropMoves_eq]
  exact flatMap_nodup (List.finRange 81)
    (fun x => (List.finRange 7).filterMap (dropCell p x))
    (List.nodup_finRange 81) (fun x _ => cell_nodup p x)
    (fun x _ y _ hxy a ha b hb heq => by
      rw [heq] at ha
      exact cells_disjoint hxy ha hb)



/-- A Nodup list whose elements are all equal has length at most one. -/
theorem nodup_all_eq_len_le {α : Type} {l : List α} {v : α}
    (hnd : l.Nodup) (h : ∀ a ∈ l, a = v) : l.length ≤ 1 := by
  cases l with
  | nil => simp
  | cons a t =>
    cases t with
    | nil => simp
    | cons b t' =>
      exfalso
      have hnb : a ∉ b :: t' := (List.nodup_cons.mp hnd).1
      have hab : a = b := (h a List.mem_cons_self).trans
        (h b (List.mem_cons_of_mem a List.mem_cons_self)).symm
      exact hnb (hab ▸ List.mem_cons_self)

theorem boardMoves_normal {p : Position} {s : Square} {pc : Piece} {m : Move}
    (h : m ∈ p.boardMoves s pc) : ∃ d pr, m = .normal s d pr := by
  unfold Position.boardMoves at h
  rw [List.mem_flatMap] at h
  obtain ⟨d, _, hd⟩ := h
  cases hpd : p.pieceAt d with
  | none =>
    simp only [hpd] at hd
    rw [List.mem_map] at hd
    obtain ⟨pr, _, rfl⟩ := hd
    exact ⟨d, pr, rfl⟩
  | some q =>
    simp only [hpd] at hd
    split at hd
    · simp at hd
    · rw [List.mem_map] at hd
      obtain ⟨pr, _, rfl⟩ := hd
      exact ⟨d, pr, rfl⟩

theorem checkFilter_eq_dropFilter (p : Position) :
    (p.pseudoMoves.filter (fun m => Position.isPawnDrop m &&
      (p.play m).inCheck (p.play m).side))
    = p.dropMoves.filter (fun m => Position.isPawnDrop m &&
        (p.play m).inCheck (p.play m).side) := by
  have key : p.pseudoMoves =
      (List.finRange 81).flatMap (fun s : Square =>
        match p.pieceAt s with
        | some pc => if (pc.color == p.side) = true then p.boardMoves s pc else []
        | none => []) ++ p.dropMoves := rfl
  rw [key, List.filter_append]
  have hboard : ((List.finRange 81).flatMap (fun s : Square =>
      match p.pieceAt s with
      | some pc => if (pc.color == p.side) = true then p.boardMoves s pc else []
      | none => [])).filter (fun m => Position.isPawnDrop m &&
        (p.play m).inCheck (p.play m).side) = [] := by
    rw [List.filter_eq_nil_iff.mpr]
    intro x hx hxc
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hxc
    have hpd : Position.isPawnDrop x = true := hxc.1
    rw [List.mem_flatMap] at hx
    obtain ⟨s, _, hx2⟩ := hx
    by_cases hpc : p.pieceAt s = none
    · simp only [hpc] at hx2; simp at hx2
    · cases hp : p.pieceAt s with
      | none => simp only [hp] at hx2; simp at hx2
      | some pc =>
        simp only [hp] at hx2
        by_cases hcol : pc.color = p.side
        · rw [if_pos (show (pc.color == p.side) = true by rw [hcol]; simp)] at hx2
          obtain ⟨d, pr, rfl⟩ := boardMoves_normal hx2
          simp [Position.isPawnDrop] at hpd
        · rw [if_neg (show ¬((pc.color == p.side) = true) by
            simp [show pc.color ≠ p.side from hcol])] at hx2
          simp at hx2
  rw [hboard, List.nil_append]

theorem filter_pawn_check_pair {p : Position} (hS : p.Shaped) (hK : KingsUnique p)
    (hnc : p.inCheck p.side.opp = false) {a b : Move}
    (hpd : Position.isPawnDrop a = true)
    (hca : (p.play a).inCheck (p.play a).side = true)
    (hpb : Position.isPawnDrop b = true)
    (hcb : (p.play b).inCheck (p.play b).side = true) : a = b := by
  cases a with
  | normal => simp [Position.isPawnDrop] at hpd
  | drop ta da =>
    cases b with
    | normal => simp [Position.isPawnDrop] at hpb
    | drop tb db =>
      simp only [Position.isPawnDrop] at hpd hpb
      cases ta with
      | pawn =>
        cases tb with
        | pawn => exact congrArg _ (checkingPawnDrop_unique hS hK hnc hca hcb)
        | _ => simp at hpb
      | _ => simp at hpd

theorem checkingPawnDrops_le_one {p : Position} (hS : p.Shaped) (hK : KingsUnique p)
    (hnc : p.inCheck p.side.opp = false) :
    (p.pseudoMoves.filter (fun m => Position.isPawnDrop m &&
      (p.play m).inCheck (p.play m).side)).length ≤ 1 := by
  rw [checkFilter_eq_dropFilter p]
  have hnd : (p.dropMoves.filter (fun m => Position.isPawnDrop m &&
      (p.play m).inCheck (p.play m).side)).Nodup :=
    List.Nodup.sublist List.filter_sublist (dropMoves_nodup p)
  cases hL : (p.dropMoves.filter (fun m => Position.isPawnDrop m &&
      (p.play m).inCheck (p.play m).side)) with
  | nil => simp
  | cons x t =>
    have hxmem : x ∈ p.dropMoves.filter (fun m => Position.isPawnDrop m &&
        (p.play m).inCheck (p.play m).side) := by
      rw [hL]; exact List.mem_cons_self
    simp only [List.mem_filter, Bool.and_eq_true] at hxmem
    obtain ⟨hxd, hpx, hcx⟩ := hxmem
    have hlen : (x :: t).length ≤ 1 := by
      refine nodup_all_eq_len_le (v := x) ?_ ?_
      · rw [hL] at hnd; exact hnd
      · intro a ha
        have hamem : a ∈ p.dropMoves.filter (fun m => Position.isPawnDrop m &&
            (p.play m).inCheck (p.play m).side) := by
          rw [hL]; exact ha
        simp only [List.mem_filter, Bool.and_eq_true] at hamem
        obtain ⟨had, hpa, hca⟩ := hamem
        exact filter_pawn_check_pair hS hK hnc hpa hca hpx hcx
    simpa using hlen

theorem play_drop_kingsUnique {p : Position} (hS : p.board.length = 81) {d : Square}
    (hK : KingsUnique p) : KingsUnique (p.play (Move.drop .pawn d)) := by
  intro c x y hx hy
  rw [play_drop_pieceAt p hS] at hx hy
  by_cases hxd : x.val = d.val <;> by_cases hyd : y.val = d.val
  · exact Fin.val_inj.mp (hxd.trans hyd.symm)
  · rw [if_pos hxd] at hx; rw [if_neg hyd] at hy
    exact absurd hx (by simp)
  · rw [if_neg hxd] at hx; rw [if_pos hyd] at hy
    exact absurd hy (by simp)
  · rw [if_neg hxd] at hx; rw [if_neg hyd] at hy
    exact hK c x y hx hy

/-- A pawn drop preserves the "every hand slot < 256" invariant. The dropped
    pawn leaves the mover's hand; the opponent's hand is untouched, and after
    the drop the opponent is to move. -/
theorem play_drop_hand_le {p : Position} (hS : p.Shaped)
    (h : ∀ c i, p.hand c i < 256) (d : Square) :
    ∀ i, (p.play (Move.drop .pawn d)).hand (p.play (Move.drop .pawn d)).side i < 256 := by
  intro i
  have hside : (p.play (Move.drop .pawn d)).side = p.side.opp := play_drop_side p d
  have hbw := hS.2.2
  have hbl := hS.2.1
  have hne : p.side ≠ p.side.opp := by cases p.side <;> simp [Color.opp]
  show (p.hands.set p.side 0 (p.hand p.side 0 - 1)).get p.side.opp i < 256
  rw [Position.Hands.get_set_len hbl hbw, if_neg (by simp [hne])]
  simpa [Position.hand] using h p.side.opp i

end Shogi.C.Proofs
