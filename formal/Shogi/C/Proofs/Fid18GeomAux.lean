import Shogi.C.Proofs.Fid18Guard
namespace Shogi.C.Proofs
open MiniC Shogi Shogi.C Shogi.C.Proofs

theorem piece_code_color (q : Piece) : q.code / 16 % 2 = q.color.idx := by
  obtain ⟨c, ty⟩ := q
  cases c <;> cases ty <;> decide +kernel

theorem piece_code_mod16 (q : Piece) : q.code % 16 = q.type.code := by
  obtain ⟨c, ty⟩ := q
  cases c <;> cases ty <;> decide +kernel

theorem piece_code_lt256 (q : Piece) : q.code < 256 := by
  obtain ⟨c, ty⟩ := q
  cases c <;> cases ty <;> decide +kernel

theorem piece_code_ne_zero (q : Piece) : q.code ≠ 0 := by
  obtain ⟨c, ty⟩ := q
  cases c <;> cases ty <;> decide

set_option maxRecDepth 100000 in
theorem slide_geom_finite : ∀ (f t : Square), f ≠ t →
  ((if (t.row : Int) - f.row < 0 then -((t.row : Int) - f.row) else (t.row : Int) - f.row) =
   (if (t.col : Int) - f.col < 0 then -((t.col : Int) - f.col) else (t.col : Int) - f.col) ∧
   (t.row : Int) - f.row ≠ 0) ∨
  ((t.row : Int) - f.row = 0 ∧ (t.col : Int) - f.col ≠ 0) ∨
  ((t.col : Int) - f.col = 0 ∧ (t.row : Int) - f.row ≠ 0) →
  let dr : Int := (t.row : Int) - f.row
  let dc : Int := (t.col : Int) - f.col
  let rs : Int := if dr > 0 then 1 else if dr < 0 then -1 else 0
  let cs : Int := if dc > 0 then 1 else if dc < 0 then -1 else 0
  let k : Nat := max dr.natAbs dc.natAbs
  let d : Nat := k - 1
  let row : Int := (f.row : Int) + rs
  let col : Int := (f.col : Int) + cs
  (t.row : Int) = row + (d : Int) * rs ∧
  (t.col : Int) = col + (d : Int) * cs ∧
  (∀ i, i ≤ d → 0 ≤ row + (i : Int) * rs ∧ row + (i : Int) * rs < 9 ∧
                  0 ≤ col + (i : Int) * cs ∧ col + (i : Int) * cs < 9) ∧
  (rs ≠ 0 ∨ cs ≠ 0) ∧
  1 ≤ k ∧ k ≤ 8
:= by decide +kernel



def guardExpr : Expr := (.un .lnot ⟨32, true⟩ (.lor (.lor (.land (.cast ⟨32, true⟩ (.var 15)) (.lor (.bin .eq (some ⟨32, false⟩) (.cast ⟨32, false⟩ (.var 4)) (.cast ⟨32, false⟩ (.const (.int ⟨32, true⟩ 6)))) (.bin .eq (some ⟨32, false⟩) (.cast ⟨32, false⟩ (.var 4)) (.cast ⟨32, false⟩ (.const (.int ⟨32, true⟩ 13)))))) (.land (.cast ⟨32, true⟩ (.var 16)) (.lor (.bin .eq (some ⟨32, false⟩) (.cast ⟨32, false⟩ (.var 4)) (.cast ⟨32, false⟩ (.const (.int ⟨32, true⟩ 7)))) (.bin .eq (some ⟨32, false⟩) (.cast ⟨32, false⟩ (.var 4)) (.cast ⟨32, false⟩ (.const (.int ⟨32, true⟩ 14))))))) (.land (.land (.bin .eq (some ⟨32, true⟩) (.var 9) (.const (.int ⟨32, true⟩ 0))) (.bin .gt (some ⟨32, true⟩) (.bin .mul (some ⟨32, true⟩) (.var 6) (.var 12)) (.const (.int ⟨32, true⟩ 0)))) (.bin .eq (some ⟨32, false⟩) (.cast ⟨32, false⟩ (.var 4)) (.cast ⟨32, false⟩ (.const (.int ⟨32, true⟩ 2)))))))

def guardState (ty : Nat) (dr dc fwd : Int) (diag straight : Nat) : State :=
  ⟨(fun i => match i with
      | 4 => some (u32 ty) | 6 => some (i32 dr) | 9 => some (i32 dc)
      | 12 => some (i32 fwd) | 15 => some (u8 diag) | 16 => some (u8 straight)
      | _ => none), (fun _ => none), false⟩

def evalSig (r : Res Val) : Option (IntTy × Nat) := match r with | .ok (.int t n) => some (t,n) | _ => none

def guardSpec (ty : Nat) (dr dc fwd : Int) (diag straight : Nat) : Nat :=
  let v := (decide (diag != 0) && decide (ty = 6 ∨ ty = 13)) ||
           (decide (straight != 0) && decide (ty = 7 ∨ ty = 14)) ||
           (decide (dc = 0) && decide (dr * fwd > 0) && decide (ty = 2))
  if v then 0 else 1


set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem guard_eval_finite : ∀ (ty : Fin 16) (dr' dc' : Fin 17) (fwdb : Fin 2) (diagb : Fin 2) (straightb : Fin 2),
  evalSig (evalExpr Gen.prog 12 (guardState ty.val ((dr'.val:Int)-8) ((dc'.val:Int)-8) (if fwdb.val=0 then 1 else -1) diagb.val straightb.val) guardExpr) =
    some (IntTy.i32, guardSpec ty.val ((dr'.val:Int)-8) ((dc'.val:Int)-8) (if fwdb.val=0 then 1 else -1) diagb.val straightb.val) := by
  intro ty
  cases ty with
  | mk tv htv =>
    have hc : tv = 0 ∨ tv = 1 ∨ tv = 2 ∨ tv = 3 ∨ tv = 4 ∨ tv = 5 ∨ tv = 6 ∨ tv = 7 ∨
              tv = 8 ∨ tv = 9 ∨ tv = 10 ∨ tv = 11 ∨ tv = 12 ∨ tv = 13 ∨ tv = 14 ∨ tv = 15 := by omega
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals
      intro dr' dc' fwdb diagb straightb
      decide +kernel +revert

#eval evalSig (evalExpr Gen.prog 12 (guardState 6 1 1 1 1 1) guardExpr)
#eval guardSpec 6 1 1 1 1 1
#eval evalSig (evalExpr Gen.prog 12 (guardState 0 1 1 1 1 1) guardExpr)
#eval guardSpec 0 1 1 1 1 1

def absI (z : Int) : Int := if z < 0 then -z else z

def set15expr : Expr := .cast ⟨8,false⟩ (.bin .ne (some ⟨32,true⟩)
  (.bin .eq (some ⟨32,true⟩)
    (.cond (.bin .lt (some ⟨32,true⟩) (.var 6) (.const (.int ⟨32,true⟩ 0))) (.un .neg ⟨32,true⟩ (.var 6)) (.var 6))
    (.cond (.bin .lt (some ⟨32,true⟩) (.var 9) (.const (.int ⟨32,true⟩ 0))) (.un .neg ⟨32,true⟩ (.var 9)) (.var 9)))
  (.const (.int ⟨32,true⟩ 0)))

def sTest (dr dc : Int) : State :=
  ⟨fun i => if i = 6 then some (i32 dr) else if i = 9 then some (i32 dc) else none, (fun _ => none), false⟩

set_option maxRecDepth 100000 in
theorem set15_eval_finite : ∀ (dr' dc' : Fin 17),
  evalSig (evalExpr Gen.prog 10 (sTest ((dr'.val : Int) - 8) ((dc'.val : Int) - 8)) set15expr) =
    some (IntTy.u8, if absI ((dr'.val : Int) - 8) = absI ((dc'.val : Int) - 8) then 1 else 0) := by
  decide +kernel


def set16expr : Expr := .cast ⟨8,false⟩ (.bin .ne (some ⟨32,true⟩)
  (.lor (.bin .eq (some ⟨32,true⟩) (.var 6) (.const (.int ⟨32,true⟩ 0)))
        (.bin .eq (some ⟨32,true⟩) (.var 9) (.const (.int ⟨32,true⟩ 0))))
  (.const (.int ⟨32,true⟩ 0)))

set_option maxRecDepth 100000 in
theorem set16_eval_finite : ∀ (dr' dc' : Fin 17),
  evalSig (evalExpr Gen.prog 10 (sTest ((dr'.val : Int) - 8) ((dc'.val : Int) - 8)) set16expr) =
    some (IntTy.u8, if ((dr'.val : Int) - 8 = 0 ∨ (dc'.val : Int) - 8 = 0) then 1 else 0) := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem ray_len_ge_finite : ∀ (f t : Square), f ≠ t →
  ((if (t.row : Int) - f.row < 0 then -((t.row : Int) - f.row) else (t.row : Int) - f.row) =
   (if (t.col : Int) - f.col < 0 then -((t.col : Int) - f.col) else (t.col : Int) - f.col) ∧
   (t.row : Int) - f.row ≠ 0) ∨
  ((t.row : Int) - f.row = 0 ∧ (t.col : Int) - f.col ≠ 0) ∨
  ((t.col : Int) - f.col = 0 ∧ (t.row : Int) - f.row ≠ 0) →
  let dr : Int := (t.row : Int) - f.row
  let dc : Int := (t.col : Int) - f.col
  let rs : Int := if dr > 0 then 1 else if dr < 0 then -1 else 0
  let cs : Int := if dc > 0 then 1 else if dc < 0 then -1 else 0
  let k : Nat := max dr.natAbs dc.natAbs
  let d : Nat := k - 1
  d < (ray f (rs, cs)).length
:= by decide +kernel

theorem slider_loop_exs (p : Position) (f t : Square) (m : Mem) (hm : m posBlock = some (encode p))
    (rs cs : Int) (d : Nat) (r : Fin 8) (hrdir : rdir r.val = (rs, cs))
    (hrow : (t.row : Int) = ((f.row : Int) + rs) + (d : Int) * rs)
    (hcol : (t.col : Int) = ((f.col : Int) + cs) + (d : Int) * cs)
    (hbnd : ∀ i, i ≤ d → 0 ≤ ((f.row : Int) + rs) + (i : Int) * rs ∧
      ((f.row : Int) + rs) + (i : Int) * rs < 9 ∧
      0 ≤ ((f.col : Int) + cs) + (i : Int) * cs ∧
      ((f.col : Int) + cs) + (i : Int) * cs < 9)
    (hstep : rs ≠ 0 ∨ cs ≠ 0) (hrs : -1 ≤ rs ∧ rs ≤ 1) (hcs : -1 ≤ cs ∧ cs ≤ 1)
    (hti : d < (ray f (rs, cs)).length)
    (s : State) (hl0 : s.locals 0 = some (posPtr' posBlock)) (hl2 : s.locals 2 = some (u8 t.val))
    (hl17 : s.locals 17 = some (i32 rs)) (hl18 : s.locals 18 = some (i32 cs))
    (hl19 : s.locals 19 = some (i32 ((f.row : Int) + rs)))
    (hl21 : s.locals 21 = some (i32 ((f.col : Int) + cs)))
    (hsm : s.mem = m) :
    ∃ s', ExS Gen.prog s
      (.seq Gen.shogi_piece_attacks_square_loop0
        (.ret (some (.cast ⟨8,false⟩ (.bin .ne (some ⟨32,true⟩) (.const (.int ⟨32,true⟩ 1)) (.const (.int ⟨32,true⟩ 0)))))))
      (.ret (some (if walkErr p rs cs t d ((f.row : Int) + rs) ((f.col : Int) + cs) then false8 else true8))) s' ∧
      s'.mem = m := by
  have hloop := ray_walk_loop p m hm rs cs t hstep hrs hcs d
    ((f.row : Int) + rs) ((f.col : Int) + cs) s hrow hcol hbnd hl0 hl2 hl17 hl18 hl19 hl21 hsm
  by_cases hw : walkErr p rs cs t d ((f.row : Int) + rs) ((f.col : Int) + cs) = true
  · obtain ⟨s', hs', hm'⟩ := (if_pos hw).mp hloop
    refine ⟨s', ?_, hm'⟩
    simpa [hw] using (ExS.seq_ret hs')
  · obtain ⟨s', hs', hmem, h19, h21⟩ := (if_neg hw).mp hloop
    refine ⟨s', ?_, hmem⟩
    refine ExS.seq hs' ?_
    apply ExS.ret
    apply EvE_of_eval (n := 3)
    simp [evalExpr, evalBin, evalCast, true8, boolVal, IntTy.i32, IntTy.u8, IntTy.toInt,
      isPtr, evalBinInt, binInt, intOf, Res.bind, hw, IntTy.wrap, IntTy.modulus]

theorem guard0_spec {ty : Nat} {dr dc fwd : Int} {diag straight : Nat}
    (h : guardSpec ty dr dc fwd diag straight = 0) :
    (((diag != 0) ∧ (ty = 6 ∨ ty = 13)) ∨
     ((straight != 0) ∧ (ty = 7 ∨ ty = 14))) ∨
    ((dc = 0 ∧ dr * fwd > 0) ∧ ty = 2) := by
  unfold guardSpec at h
  dsimp at h
  split at h
  · rename_i hv
    simpa [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] using hv
  · rename_i hv
    omega
theorem guardSpec_le_one (ty : Nat) (dr dc fwd : Int) (diag straight : Nat) :
    guardSpec ty dr dc fwd diag straight ≤ 1 := by
  unfold guardSpec
  dsimp
  let v := (decide (diag != 0) && decide (ty = 6 ∨ ty = 13)) ||
           (decide (straight != 0) && decide (ty = 7 ∨ ty = 14)) ||
           (decide (dc = 0) && decide (dr * fwd > 0) && decide (ty = 2))
  change (if v then 0 else 1) ≤ 1
  by_cases hv : v <;> simp [hv]

theorem guardSpec_lt (ty : Nat) (dr dc fwd : Int) (diag straight : Nat) :
    guardSpec ty dr dc fwd diag straight < 2147483648 := by
  unfold guardSpec
  dsimp
  split <;> decide

def ptByCode (n : Nat) : PieceType :=
  if n = 1 then .pawn else if n = 2 then .lance else if n = 3 then .knight
  else if n = 4 then .silver else if n = 5 then .gold else if n = 6 then .bishop
  else if n = 7 then .rook else if n = 8 then .king else if n = 9 then .proPawn
  else if n = 10 then .proLance else if n = 11 then .proKnight else if n = 12 then .proSilver
  else if n = 13 then .horse else .dragon


theorem eve_u8_of_sig {s : State} {e : Expr} {N k : Nat}
    (h : evalSig (evalExpr Gen.prog N s e) = some (IntTy.u8, k)) :
    EvE Gen.prog s e (u8 k) := by
  apply EvE_of_eval (n := N)
  cases he : evalExpr Gen.prog N s e with
  | ok v =>
    cases v with
    | int t n =>
      simp [evalSig, he] at h
      rcases h with ⟨rfl, rfl⟩
      rfl
    | ptr b o => simp [evalSig, he] at h
    | null => simp [evalSig, he] at h
    | f64 x => simp [evalSig, he] at h
  | ub => simp [evalSig, he] at h
  | timeout => simp [evalSig, he] at h

theorem eve_i32_of_sig {s : State} {e : Expr} {N k : Nat} (hk : k < 2147483648)
    (h : evalSig (evalExpr Gen.prog N s e) = some (IntTy.i32, k)) :
    EvE Gen.prog s e (i32 (k : Int)) := by
  apply EvE_of_eval (n := N)
  cases he : evalExpr Gen.prog N s e with
  | ok v =>
    cases v with
    | int t n =>
      simp [evalSig, he] at h
      rcases h with ⟨rfl, rfl⟩
      have hmod : ((n : Int) % (4294967296 : Int)).toNat = n := by
        rw [Int.emod_eq_of_lt (a := (n : Int)) (b := (4294967296 : Int)) (by omega) (by omega)]
        simp
      simpa [i32, IntTy.wrap, IntTy.modulus, IntTy.i32] using hmod.symm
    | ptr b o => simp [evalSig, he] at h
    | null => simp [evalSig, he] at h
    | f64 x => simp [evalSig, he] at h
  | ub => simp [evalSig, he] at h
  | timeout => simp [evalSig, he] at h

theorem eve_i32z_of_sig {s : State} {e : Expr} {N : Nat} {z : Int}
    (h : evalSig (evalExpr Gen.prog N s e) = some (IntTy.i32, (z % (4294967296 : Int)).toNat)) :
    EvE Gen.prog s e (i32 z) := by
  apply EvE_of_eval (n := N)
  cases he : evalExpr Gen.prog N s e with
  | ok v =>
    cases v with
    | int t n =>
      simp [evalSig, he] at h
      rcases h with ⟨rfl, rfl⟩
      rfl
    | ptr b o => simp [evalSig, he] at h
    | null => simp [evalSig, he] at h
    | f64 x => simp [evalSig, he] at h
  | ub => simp [evalSig, he] at h
  | timeout => simp [evalSig, he] at h

def signExpr (i : Nat) : Expr := .bin .sub (some ⟨32,true⟩)
  (.bin .gt (some ⟨32,true⟩) (.var i) (.const (.int ⟨32,true⟩ 0)))
  (.bin .lt (some ⟨32,true⟩) (.var i) (.const (.int ⟨32,true⟩ 0)))

def sSign (z : Int) : State :=
  ⟨(fun j => if j = 6 then some (i32 z) else none), (fun _ => none), false⟩

set_option maxRecDepth 100000 in
theorem sign_eval_finite : ∀ z : Fin 17,
    evalSig (evalExpr Gen.prog 8 (sSign ((z.val : Int) - 8)) (signExpr 6)) =
      some (IntTy.i32, ((if ((z.val : Int) - 8) > 0 then (1 : Int)
        else if ((z.val : Int) - 8) < 0 then (-1 : Int) else 0) % (4294967296 : Int)).toNat) := by
  decide +kernel



set_option maxRecDepth 100000 in
theorem ray_at_to_finite : ∀ (f t : Square), f ≠ t →
  let dr : Int := (t.row : Int) - f.row
  let dc : Int := (t.col : Int) - f.col
  let rs : Int := if dr > 0 then 1 else if dr < 0 then -1 else 0
  let cs : Int := if dc > 0 then 1 else if dc < 0 then -1 else 0
  let k : Nat := max dr.natAbs dc.natAbs
  let d : Nat := k - 1
  ((if dr < 0 then -dr else dr) = (if dc < 0 then -dc else dc) ∧ dr ≠ 0) ∨
  (dr = 0 ∧ dc ≠ 0) ∨ (dc = 0 ∧ dr ≠ 0) →
  ∀ r : Fin 8, rdir r.val = (rs, cs) → (ray f (rdir r.val))[d]? = some t
:= by decide +kernel


set_option maxRecDepth 100000 in
theorem ray_at_of_rowcol : ∀ (f t : Square), f ≠ t →
  ∀ r : Fin 8,
  let dr : Int := (t.row : Int) - f.row
  let dc : Int := (t.col : Int) - f.col
  let rs : Int := if dr > 0 then 1 else if dr < 0 then -1 else 0
  let cs : Int := if dc > 0 then 1 else if dc < 0 then -1 else 0
  let k : Nat := max dr.natAbs dc.natAbs
  let d : Nat := k - 1
  rdir r.val = (rs, cs) →
  (t.row : Int) = ((f.row : Int) + rs) + (d : Int) * rs →
  (t.col : Int) = ((f.col : Int) + cs) + (d : Int) * cs →
  ∀ hk : d < (ray f (rdir r.val)).length, (ray f (rdir r.val))[d]'hk = t
:= by decide +kernel


set_option maxRecDepth 100000 in
theorem slide_dir_eq_of_mem : ∀ (f t : Square) (d1 d2 : Fin 3), f ≠ t →
  let dr : Int := (t.row : Int) - f.row
  let dc : Int := (t.col : Int) - f.col
  let rs : Int := if dr > 0 then 1 else if dr < 0 then -1 else 0
  let cs : Int := if dc > 0 then 1 else if dc < 0 then -1 else 0
  t ∈ ray f (((d1.val : Int) - 1), ((d2.val : Int) - 1)) →
  (((d1.val : Int) - 1), ((d2.val : Int) - 1)) = (rs, cs)
:= by decide +kernel


theorem sign_diag {dr dc : Int} (habs : (if dr < 0 then -dr else dr) = (if dc < 0 then -dc else dc))
    (hdr : dr ≠ 0) :
    ((if dr > 0 then 1 else if dr < 0 then -1 else 0),
     (if dc > 0 then 1 else if dc < 0 then -1 else 0)) ∈ diagonals := by
  simp [diagonals]
  omega

theorem sign_ortho {dr dc : Int} (hzero : dr = 0 ∨ dc = 0) (hnz : dr ≠ 0 ∨ dc ≠ 0) :
    ((if dr > 0 then 1 else if dr < 0 then -1 else 0),
     (if dc > 0 then 1 else if dc < 0 then -1 else 0)) ∈ orthogonals := by
  simp [orthogonals]
  omega

theorem sign_lance {dr dc fwd : Int} (hfw : fwd = 1 ∨ fwd = -1)
    (hdc : dc = 0) (hdrfwd : dr * fwd > 0) :
    (if dr > 0 then 1 else if dr < 0 then -1 else 0) = fwd ∧
    (if dc > 0 then 1 else if dc < 0 then -1 else 0) = 0 := by
  rcases hfw with rfl | rfl <;> simp [hdc] <;> omega

theorem sq_val_eq (s : Square) : s.val = s.row * 9 + s.col := by
  have h := Nat.div_add_mod s.val 9
  dsimp [Square.row, Square.col] at *
  omega

set_option maxRecDepth 100000 in
theorem ray_mem_geom_finite : ∀ (f t : Square) (r : Fin 8),
  f ≠ t → t ∈ ray f (rdir r.val) →
  let dr : Int := (t.row : Int) - f.row
  let dc : Int := (t.col : Int) - f.col
  let d := rdir r.val
  (d.1 = 0 → dr = 0) ∧ (d.2 = 0 → dc = 0) ∧
  (d.1 ≠ 0 → d.2 ≠ 0 → (if dr < 0 then -dr else dr) = (if dc < 0 then -dc else dc)) ∧
  (d.1 * dr > 0 ∨ d.1 = 0) ∧ (d.2 * dc > 0 ∨ d.2 = 0)
:= by decide +kernel

theorem ptByCode_code (ty : PieceType) : ptByCode ty.code = ty := by cases ty <;> rfl

theorem slide_dir_in_bounds (c : Color) (ty : PieceType) (d : Int × Int)
    (h : d ∈ slideDirs c.fwd ty) :
    -1 ≤ d.1 ∧ d.1 ≤ 1 ∧ -1 ≤ d.2 ∧ d.2 ≤ 1 := by
  cases c <;> cases ty <;> simp [slideDirs, diagonals, orthogonals, Color.fwd] at h ⊢
  all_goals rcases h with rfl | rfl | rfl | rfl <;> simp [Color.fwd] <;> omega

theorem offset_eq_diff {f t : Square} {a b : Int}
    (h : Square.offset f (a, b) = some t) :
    a = (t.row : Int) - f.row ∧ b = (t.col : Int) - f.col := by
  unfold Square.offset Square.mk? at h
  split at h
  · next hpos =>
      rw [Option.some.injEq] at h
      have hv : ((((f.row : Int) + a) * 9 + ((f.col : Int) + b)).toNat) = t.val := by
        simpa using congrArg Fin.val h
      have hto : ((((f.row : Int) + a) * 9 + ((f.col : Int) + b)).toNat : Int) =
          ((f.row : Int) + a) * 9 + ((f.col : Int) + b) := by
        have hnonneg : 0 ≤ ((f.row : Int) + a) * 9 + ((f.col : Int) + b) := by
          rcases hpos with ⟨hr, _, hc, _⟩
          omega
        omega
      have hvi : (((((f.row : Int) + a) * 9 + ((f.col : Int) + b)).toNat : Int)) = (t.val : Int) := by
        exact_mod_cast hv
      rw [hto] at hvi
      have htval : (t.val : Int) = (t.row : Int) * 9 + (t.col : Int) := by
        have hdm := Nat.div_add_mod t.val 9
        dsimp [Square.row, Square.col]
        omega
      rw [htval] at hvi
      have htcol_bnd : (t.col : Int) < 9 := by
        have := t.isLt
        dsimp [Square.col]
        omega
      have htrow_bnd : (t.row : Int) < 9 := by
        have := t.isLt
        dsimp [Square.row]
        omega
      constructor <;> omega
  · contradiction

end Shogi.C.Proofs
