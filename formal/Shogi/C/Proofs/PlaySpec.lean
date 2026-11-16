/-
  T8 (legality) groundwork: what `Position.play` does, square by square,
  hand slot by hand slot, and to the king squares — the facts the C
  `make_legal_probe` byte edits are compared against.
-/
import Shogi.C.Proofs.PseudoSpec

namespace Shogi.C.Proofs
open MiniC Shogi Shogi.C

theorem pieceAt_setSq (p : Position) (b : List (Option Piece)) (hb : b.length = 81) (s : Square)
    (v : Option Piece) (x : Square) :
    ({ p with board := Position.setSq b s v } : Position).pieceAt x = if x = s then v else
      ({ p with board := b } : Position).pieceAt x := by
  simp only [Position.pieceAt, Position.setSq]
  by_cases h : x = s
  · subst h; simp [List.getD_eq_getElem?_getD, hb, x.isLt]
  · have : x.val ≠ s.val := fun e => h (Fin.ext e)
    simp [List.getD_eq_getElem?_getD, List.getElem?_set, h, Ne.symm this]

theorem setSq_length (b : List (Option Piece)) (s : Square) (v : Option Piece) :
    (Position.setSq b s v).length = b.length := by simp [Position.setSq]

/-- The moved piece of a board move. -/
def movedPiece (c : Color) (pc : Piece) (pr : Bool) : Piece := ⟨c, if pr then pc.type.promote else pc.type⟩

theorem play_normal_pieceAt (p : Position) (hs : p.board.length = 81) {s d : Square} {pr : Bool} {pc : Piece}
    (hpc : p.pieceAt s = some pc) (x : Square) :
    (p.play (.normal s d pr)).pieceAt x =
      if x = d then some (movedPiece p.side pc pr) else if x = s then none else p.pieceAt x := by
  simp only [Position.play, hpc]
  have h1 := pieceAt_setSq p (Position.setSq p.board s none) (by rw [setSq_length]; exact hs) d
    (some (movedPiece p.side pc pr)) x
  have h2 := pieceAt_setSq p p.board hs s none x
  simp only [Position.pieceAt] at h1 h2 ⊢
  rw [← h2]; exact h1

/-! ### An encoder with explicit fields -/

def enc (pa : Square → Option Piece) (h : Color → Fin 7 → Nat) (sd : Color) (kb kw : UInt8) : List UInt8 :=
  (List.finRange 81).map (fun s => pieceByte (pa s)) ++
  ((List.finRange 7).map (fun i => (h .black i).toUInt8) ++ (List.finRange 7).map (fun i => (h .white i).toUInt8)) ++
  [0] ++ le32 sd.idx ++ List.replicate 12 0 ++ [kb, kw]

theorem encode_enc (p : Position) :
    encode p = enc p.pieceAt p.hand p.side (kingByte p .black) (kingByte p .white) := by
  simp [encode, enc, Gen.off_side, Gen.off_king_square, le32]

theorem enc_length (pa h sd kb kw) : (enc pa h sd kb kw).length = 114 := by
  simp [enc, le32]

/-- One-byte write (what a `uint8_t` store does to a block). -/
def wr1 (blk : List UInt8) (o : Nat) (b : UInt8) : List UInt8 := blk.take o ++ [b] ++ blk.drop (o + 1)

theorem wr1_eq_set (blk : List UInt8) (o : Nat) (b : UInt8) (h : o < blk.length) : wr1 blk o b = blk.set o b := by
  rw [List.set_eq_take_append_cons_drop, if_pos h]; simp [wr1]

theorem enc_set_board (pa h sd kb kw) (x : Square) (v : Option Piece) :
    (enc pa h sd kb kw).set x.val (pieceByte v) = enc (fun y => if y = x then v else pa y) h sd kb kw := by
  unfold enc
  simp only [List.append_assoc]
  rw [List.set_append_left _ _ (by simp)]
  congr 1
  apply List.ext_getElem
  · simp
  · intro i h1 h2
    simp only [List.getElem_set, List.getElem_map, List.getElem_finRange]
    by_cases e : x.val = i
    · subst e; simp
    · rw [if_neg e]
      have : (⟨i, by simpa using h1⟩ : Fin 81) ≠ x := fun h => e (by rw [← h])
      simp [this]

def hupd (h : Color → Fin 7 → Nat) (c : Color) (i : Fin 7) (n : Nat) : Color → Fin 7 → Nat :=
  fun c' i' => if c' = c ∧ i' = i then n else h c' i'

theorem map_finRange_set {α : Type} (f : Fin 7 → α) (i : Fin 7) (v : α) :
    ((List.finRange 7).map f).set i.val v = (List.finRange 7).map (fun j => if j = i then v else f j) := by
  apply List.ext_getElem
  · simp
  · intro k h1 h2
    simp only [List.getElem_set, List.getElem_map, List.getElem_finRange]
    by_cases e : i.val = k
    · subst e; simp
    · rw [if_neg e]
      have : (⟨k, by simpa using h1⟩ : Fin 7) ≠ i := fun h => e (by rw [← h])
      simp [this]

theorem enc_set_hand (pa h sd kb kw) (c : Color) (i : Fin 7) (n : Nat) :
    (enc pa h sd kb kw).set (81 + 7 * c.idx + i.val) n.toUInt8 = enc pa (hupd h c i n) sd kb kw := by
  unfold enc
  simp only [List.append_assoc]
  have hA : ((List.finRange 81).map (fun s => pieceByte (pa s))).length = 81 := by simp
  have hB : ((List.finRange 7).map (fun i => (h .black i).toUInt8)).length = 7 := by simp
  have hb : (fun j => (hupd h c i n .black j).toUInt8) = fun j => if c = .black ∧ j = i then n.toUInt8
      else (h .black j).toUInt8 := by funext j; simp only [hupd]; split <;> simp_all
  have hw : (fun j => (hupd h c i n .white j).toUInt8) = fun j => if c = .white ∧ j = i then n.toUInt8
      else (h .white j).toUInt8 := by funext j; simp only [hupd]; split <;> simp_all
  rw [List.set_append_right _ _ (by rw [hA]; omega), hA, hb, hw]
  congr 1
  cases c
  · rw [show 81 + 7 * Color.black.idx + i.val - 81 = i.val by simp [Color.idx]]
    rw [List.set_append_left _ _ (by rw [hB]; exact i.isLt), map_finRange_set]
    simp
  · rw [show 81 + 7 * Color.white.idx + i.val - 81 = 7 + i.val by simp [Color.idx]; omega]
    rw [List.set_append_right _ _ (by rw [hB]; omega), hB, show 7 + i.val - 7 = i.val by omega]
    rw [List.set_append_left _ _ (by simp), map_finRange_set]
    simp

/-- The 4-byte write of the side field. -/
theorem enc_set_side (pa h sd kb kw) (c : Color) :
    (enc pa h sd kb kw).take 96 ++ encodeLE 4 c.idx ++ (enc pa h sd kb kw).drop (96 + 4) = enc pa h c kb kw := by
  have hc : c.idx < 2 := by cases c <;> decide
  have hs : sd.idx < 2 := by cases sd <;> decide
  let P : List UInt8 := (List.finRange 81).map (fun s => pieceByte (pa s)) ++
      ((List.finRange 7).map (fun i => (h .black i).toUInt8) ++ (List.finRange 7).map (fun i => (h .white i).toUInt8)) ++
      [0]
  have hP : P.length = 96 := by simp [P]
  have e : ∀ x : Color, enc pa h x kb kw = P ++ (le32 x.idx ++ (List.replicate 12 0 ++ [kb, kw])) := by
    intro x; simp [enc, P, List.append_assoc]
  have hl : (le32 sd.idx).length = 4 := by simp [le32]
  rw [e sd, e c, List.take_left' hP, show 96 + 4 = P.length + (le32 sd.idx).length by rw [hP, hl],
    ← List.drop_drop, List.drop_left' rfl, List.drop_left' rfl, le32_small c.idx (by omega), List.append_assoc]

theorem enc_set_king (pa h sd kb kw) (c : Color) (b : UInt8) :
    (enc pa h sd kb kw).set (112 + c.idx) b =
      (match c with | .black => enc pa h sd b kw | .white => enc pa h sd kb b) := by
  cases c <;> simp [enc, Color.idx, List.set_append_right, List.set_append_left, le32]

/-! ### King squares -/

def KingsUnique (p : Position) : Prop :=
  ∀ c x y, p.pieceAt x = some ⟨c, .king⟩ → p.pieceAt y = some ⟨c, .king⟩ → x = y

theorem kingSquare_some {p : Position} {c : Color} {k : Square}
    (h : ∀ x, p.pieceAt x = some ⟨c, .king⟩ ↔ x = k) : p.kingSquare c = some k := by
  unfold Position.kingSquare
  rw [List.find?_eq_some_iff_getElem]
  refine ⟨by simp [(h k).mpr rfl], k.val, by simp, by simp, fun j hj => ?_⟩
  have : (⟨j, by omega⟩ : Square) ≠ k := fun e => by rw [← e] at hj; simp at hj
  simp only [List.getElem_finRange]
  have h2 : p.pieceAt ⟨j, by omega⟩ ≠ some ⟨c, .king⟩ := fun e => this ((h _).mp e)
  simp only [Fin.cast_mk]; simpa using h2

theorem kingSquare_none {p : Position} {c : Color} (h : ∀ x, p.pieceAt x ≠ some ⟨c, .king⟩) :
    p.kingSquare c = none := by
  unfold Position.kingSquare
  rw [List.find?_eq_none]; intro x _; simpa using h x

/-- `kingSquare` depends only on `pieceAt`. -/
theorem kingSquare_congr {p q : Position} (h : ∀ x, p.pieceAt x = q.pieceAt x) (c : Color) :
    p.kingSquare c = q.kingSquare c := by
  unfold Position.kingSquare; congr 1; funext x; rw [h x]

theorem kingByte_congr {p q : Position} (h : ∀ x, p.pieceAt x = q.pieceAt x) (c : Color) :
    kingByte p c = kingByte q c := by
  unfold kingByte; rw [kingSquare_congr h]

theorem kingSquare_iff {p q : Position} {c : Color}
    (h : ∀ x, p.pieceAt x = some ⟨c, .king⟩ ↔ q.pieceAt x = some ⟨c, .king⟩) : p.kingSquare c = q.kingSquare c := by
  unfold Position.kingSquare; congr 1; funext x
  apply Bool.eq_iff_iff.mpr; simp only [beq_iff_eq]; exact h x

theorem promote_king (t : PieceType) : (t.promote = .king ↔ t = .king) := by cases t <;> decide

/-- King square of colour `c'` after a board move `s → d` of `pc` (colour = side). -/
def kingAfter (p : Position) (s d : Square) (pc : Piece) (c' : Color) : Option Square :=
  if pc.type = .king ∧ c' = pc.color then some d else p.kingSquare c'

theorem play_normal_kingSquare (p : Position) (hb : p.board.length = 81) (hK : KingsUnique p) {s d : Square}
    {pr : Bool} {pc : Piece} (hpc : p.pieceAt s = some pc) (hcol : pc.color = p.side)
    (hd : ∀ c', p.pieceAt d ≠ some ⟨c', .king⟩) (c' : Color) :
    (p.play (.normal s d pr)).kingSquare c' = kingAfter p s d pc c' := by
  have hP := play_normal_pieceAt p hb (pr := pr) (d := d) hpc
  unfold kingAfter
  by_cases hk : pc.type = .king ∧ c' = pc.color
  · rw [if_pos hk]
    apply kingSquare_some; intro x
    rw [hP x]
    have hmv : movedPiece p.side pc pr = ⟨c', .king⟩ := by
      simp only [movedPiece, hk.1, ← hcol, hk.2]; cases pr <;> rfl
    by_cases e1 : x = d
    · simp [e1, hmv]
    · rw [if_neg e1]
      by_cases e2 : x = s
      · rw [if_pos e2]; simp only [reduceCtorEq, false_iff]; exact e1
      · rw [if_neg e2]; simp only [e1, iff_false]
        intro hx
        have : pc = ⟨c', .king⟩ := by obtain ⟨a, b⟩ := pc; simp at hk; obtain ⟨h1, h2⟩ := hk; subst h1 h2; rfl
        exact e2 (hK c' x s hx (by rw [hpc, this]))
  · rw [if_neg hk]
    apply kingSquare_iff; intro x
    rw [hP x]
    by_cases e1 : x = d
    · subst e1
      simp only [if_true]
      constructor
      · intro h; simp [movedPiece] at h; obtain ⟨h1, h2⟩ := h
        exact absurd ⟨(by cases pr <;> simp_all [promote_king]), by rw [← h1, hcol]⟩ hk
      · intro h; exact absurd h (hd c')
    · rw [if_neg e1]
      by_cases e2 : x = s
      · rw [if_pos e2, e2, hpc]
        constructor
        · intro h; cases h
        · intro h; cases h; exact absurd ⟨rfl, rfl⟩ hk
      · rw [if_neg e2]

theorem hand_set (p : Position) (hS : p.Shaped) (c : Color) (i : Fin 7) (n : Nat) :
    (fun c' i' => Hands.get (p.hands.set c i n) c' i') = hupd p.hand c i n := by
  obtain ⟨_, hb, hw⟩ := hS
  funext c' i'
  simp only [hupd, Position.hand]
  cases c <;> cases c' <;> simp [Hands.set, Hands.get, List.getD_eq_getElem?_getD, List.getElem?_set, hb, hw] <;>
    by_cases e : i' = i <;> simp [e, Fin.val_ne_of_ne, i'.isLt] <;> (rw [List.getElem_set_ne (fun h => e (Fin.ext h.symm))])

def handsAfter (p : Position) (d : Square) : Color → Fin 7 → Nat :=
  match p.pieceAt d with
  | some q => match q.type.unpromote.handIndex with
    | some i => hupd p.hand p.side i (p.hand p.side i + 1)
    | none => p.hand
  | none => p.hand

def kbOf : Option Square → UInt8
  | some k => k.val.toUInt8
  | none => 255

theorem encode_play_normal (p : Position) (hS : p.Shaped) (hK : KingsUnique p) {s d : Square} {pr : Bool}
    {pc : Piece} (hpc : p.pieceAt s = some pc) (hcol : pc.color = p.side)
    (hd : ∀ c', p.pieceAt d ≠ some ⟨c', .king⟩) :
    encode (p.play (.normal s d pr)) =
      enc (fun y => if y = d then some (movedPiece p.side pc pr) else if y = s then none else p.pieceAt y)
        (handsAfter p d) p.side.opp (kbOf (kingAfter p s d pc .black)) (kbOf (kingAfter p s d pc .white)) := by
  rw [encode_enc]
  have hP : (p.play (.normal s d pr)).pieceAt = fun y =>
      if y = d then some (movedPiece p.side pc pr) else if y = s then none else p.pieceAt y :=
    funext (play_normal_pieceAt p hS.1 hpc)
  have hH : (p.play (.normal s d pr)).hand = handsAfter p d := by
    funext c' i'
    simp only [Position.play, hpc, handsAfter]
    cases hq : p.pieceAt d with
    | none => rfl
    | some q =>
      cases hi : q.type.unpromote.handIndex with
      | none => simp only [hi]; rfl
      | some i =>
        simp only [hi]
        exact congrFun (congrFun (hand_set p hS p.side i _) c') i'
  have hSd : (p.play (.normal s d pr)).side = p.side.opp := rfl
  have hk : ∀ c', kingByte (p.play (.normal s d pr)) c' = kbOf (kingAfter p s d pc c') := by
    intro c'; unfold kingByte; rw [play_normal_kingSquare p hS.1 hK hpc hcol hd c']
    cases kingAfter p s d pc c' <;> rfl
  rw [hP, hH, hSd, hk, hk]

theorem encode_play_drop (p : Position) (hS : p.Shaped) {t : PieceType} {d : Square} {i : Fin 7}
    (hi : t.handIndex = some i) (hd : p.pieceAt d = none) :
    encode (p.play (.drop t d)) =
      enc (fun y => if y = d then some ⟨p.side, t⟩ else p.pieceAt y)
        (hupd p.hand p.side i (p.hand p.side i - 1)) p.side.opp (kingByte p .black) (kingByte p .white) := by
  rw [encode_enc]
  have hP : (p.play (.drop t d)).pieceAt = fun y => if y = d then some ⟨p.side, t⟩ else p.pieceAt y := by
    funext y
    simp only [Position.play, hi]
    exact pieceAt_setSq p p.board hS.1 d _ y
  have hH : (p.play (.drop t d)).hand = hupd p.hand p.side i (p.hand p.side i - 1) := by
    funext c' i'
    simp only [Position.play, hi]
    exact congrFun (congrFun (hand_set p hS p.side i _) c') i'
  have htk : t ≠ .king := by intro h; subst h; simp [PieceType.handIndex] at hi
  have hk : ∀ c', kingByte (p.play (.drop t d)) c' = kingByte p c' := by
    intro c'; unfold kingByte
    rw [kingSquare_iff (q := p) (fun x => by
      rw [hP]; by_cases e : x = d
      · subst e; simp [hd]; intro _; exact htk
      · simp [e])]
  rw [hP, hH, hk, hk]; rfl

end Shogi.C.Proofs
