/-
  T7 layer 2: `step_square_attacked` refines the spec's single-step attacks,
  for every position, target and attacker.

  The C reads the translated probe table; `table_probes` shows its bytes
  decode to the Lean probe lists (symbolically, through the layout of
  `stepAttackProbesBytes`), and `stepAttacked_eq` with `probesAgree_all`
  shows those lists describe exactly the spec's step attacks.
-/
import Shogi.C.Proofs.FindKing
import Shogi.TablesSpec
import Shogi.C.Proofs.Tables

namespace Shogi.C.Proofs
variable {posBlock : Nat}
open MiniC Shogi Shogi.C Shogi.Tables

/-- `step_attack_probe_count[c][t]`, read from the translated table bytes. -/
def cnt (c : Color) (t : Nat) : Nat :=
  (Gen.global_step_attack_probe_count.getD (c.idx * 81 + t) 0).toNat

def pbase (c : Color) (t i : Nat) : Nat := c.idx * 3240 + t * 40 + i * 4

/-- `step_attack_probes[c][t][i]`, read from the translated table bytes. -/
def prbOf (G : List UInt8) (c : Color) (t i : Nat) : Probe :=
  ⟨(G.getD (pbase c t i) 0).toNat,
   (G.getD (pbase c t i + 2) 0).toNat + 256 * (G.getD (pbase c t i + 3) 0).toNat⟩

def prb (c : Color) (t i : Nat) : Probe := prbOf Gen.global_step_attack_probes c t i

theorem getD_flatMap_uniform {α} (f : α → List UInt8) (n : Nat) :
    ∀ (L : List α), (∀ x ∈ L, (f x).length = n) → ∀ (k r : Nat) (hk : k < L.length), r < n →
    (L.flatMap f).getD (k * n + r) 0 = (f L[k]).getD r 0 := by
  intro L
  induction L with
  | nil => intro _ k r hk; simp at hk
  | cons x L ih =>
    intro hf k r hk hr
    have hx := hf x (List.mem_cons_self ..)
    simp only [List.flatMap_cons]
    cases k with
    | zero =>
      simp only [Nat.zero_mul, Nat.zero_add, List.getElem_cons_zero]
      rw [List.getD_eq_getElem?_getD, List.getElem?_append_left (by omega), ← List.getD_eq_getElem?_getD]
    | succ k =>
      simp only [List.getElem_cons_succ]
      rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by rw [hx]; rw [Nat.succ_mul]; omega),
        hx, show (k + 1) * n + r - n = k * n + r by rw [Nat.succ_mul]; omega,
        ← List.getD_eq_getElem?_getD]
      exact ih (fun y hy => hf y (List.mem_cons_of_mem _ hy)) k r (by simp at hk; omega) hr

theorem length_flatMap_uniform {α β} (f : α → List β) (n : Nat) :
    ∀ (L : List α), (∀ x ∈ L, (f x).length = n) → (L.flatMap f).length = L.length * n := by
  intro L
  induction L with
  | nil => intro _; simp
  | cons x L ih =>
    intro hf
    simp only [List.flatMap_cons, List.length_append, List.length_cons,
      hf x (List.mem_cons_self ..), ih (fun y hy => hf y (List.mem_cons_of_mem _ hy))]
    rw [Nat.succ_mul]; omega

theorem probeBytes_length (pr : Probe) : (probeBytes pr).length = 4 := rfl

theorem probes_length_le (c : Color) (t : Fin 81) : (probes c t).length ≤ 10 := by
  unfold probes; exact List.length_take_le _ _

theorem padTo_getElem_lt {α} (n : Nat) (x : α) (l : List α) (i : Nat) (hi : i < l.length) :
    (padTo n x l)[i]'(by simp [padTo]; omega) = l[i] := by
  simp [padTo, List.getElem_append_left hi]

theorem colors_getElem (c : Color) : colors[c.idx]'(by cases c <;> decide) = c := by
  cases c <;> rfl

/-- Byte `r < 4` of probe `i` of `(c, t)` in the Lean table image. -/
theorem probesBytes_at (c : Color) (t : Fin 81) (i r : Nat) (hi : i < (probes c t).length)
    (hr : r < 4) :
    stepAttackProbesBytes.getD (pbase c t i + r) 0 = (probeBytes ((probes c t)[i])).getD r 0 := by
  have hl10 := probes_length_le c t
  unfold stepAttackProbesBytes
  have e : pbase c t i + r = c.idx * 3240 + (t.val * 40 + (i * 4 + r)) := by unfold pbase; omega
  rw [e]
  have h40 : ∀ (c' : Color) (t' : Fin 81),
      ((padTo 10 (⟨0, 0⟩ : Probe) (probes c' t')).flatMap probeBytes).length = 40 := by
    intro c' t'
    rw [length_flatMap_uniform probeBytes 4 _ (fun x _ => rfl)]
    simp [padTo]; have := probes_length_le c' t'; omega
  have h3240 : ∀ c' : Color, ((List.finRange 81).flatMap fun t' =>
      (padTo 10 (⟨0, 0⟩ : Probe) (probes c' t')).flatMap probeBytes).length = 3240 := by
    intro c'
    rw [length_flatMap_uniform _ 40 _ (fun x _ => h40 c' x)]
    simp
  rw [getD_flatMap_uniform _ 3240 colors (fun x _ => h3240 x)
    c.idx (t.val * 40 + (i * 4 + r)) (by cases c <;> decide) (by omega)]
  rw [colors_getElem]
  rw [getD_flatMap_uniform _ 40 (List.finRange 81) (fun x _ => h40 c x) t.val (i * 4 + r)
    (by simp) (by omega)]
  simp only [List.getElem_finRange, Fin.cast_mk, Fin.eta]
  have hpl : (padTo 10 (⟨0, 0⟩ : Probe) (probes c t)).length = 10 := by
    simp [padTo]; omega
  rw [getD_flatMap_uniform probeBytes 4 _ (fun x _ => rfl) i r (by rw [hpl]; omega) hr]
  rw [padTo_getElem_lt 10 _ _ i hi]


theorem cnt_eq (c : Color) (t : Fin 81) : cnt c t = (probes c t).length := by
  unfold cnt
  rw [step_attack_probe_count_refine]
  unfold stepAttackProbeCountBytes
  have hl : ∀ c' : Color, ((List.finRange 81).map fun t' => (probes c' t').length.toUInt8).length = 81 := by
    intro c'; simp
  rw [show c.idx * 81 + t.val = c.idx * 81 + t.val from rfl]
  rw [getD_flatMap_uniform _ 81 colors (fun x _ => hl x) c.idx t.val (by cases c <;> decide) t.isLt]
  rw [colors_getElem]
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by simp)]
  simp only [List.getElem_map, List.getElem_finRange, Fin.cast_mk, Fin.eta, Option.getD_some]
  have := probes_length_le c t
  simp [UInt8.toNat_ofNat]; omega

theorem prbOf_eq (G : List UInt8) (hG : G = stepAttackProbesBytes) (c : Color) (t : Fin 81)
    (i : Nat) (hi : i < (probes c t).length) : prbOf G c t i = (probes c t)[i] := by
  have hb := List.all_eq_true.mp (probes_bounds c t) _ (List.getElem_mem hi)
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hb
  have e0 := probesBytes_at c t i 0 hi (by decide)
  have e2 := probesBytes_at c t i 2 hi (by decide)
  have e3 := probesBytes_at c t i 3 hi (by decide)
  rw [Nat.add_zero, ← hG] at e0
  rw [← hG] at e2 e3
  unfold prbOf
  rw [e0, e2, e3]
  generalize (probes c t)[i] = pr at hb ⊢
  obtain ⟨sq, mk⟩ := pr
  simp only at hb
  simp [probeBytes, le16, UInt8.toNat_ofNat]
  constructor <;> omega

theorem prb_eq (c : Color) (t : Fin 81) (i : Nat) (hi : i < (probes c t).length) :
    prb c t i = (probes c t)[i] :=
  prbOf_eq _ step_attack_probes_refine c t i hi

theorem table_probes (c : Color) (t : Fin 81) :
    (List.range (cnt c t)).map (prb c t) = probes c t := by
  apply List.ext_getElem
  · simp [cnt_eq]
  · intro i h1 h2
    simp only [List.getElem_map, List.getElem_range]
    exact prb_eq c t i h2

/-- A probe entry hits: the square holds a piece of `c` whose type bit is set. -/
def probeHit (p : Position) (c : Color) (pr : Probe) : Bool :=
  if h : pr.square < 81 then
    match p.pieceAt ⟨pr.square, h⟩ with
    | some pc => pc.color == c && maskHas pr.mask pc.type
    | none => false
  else false

/-- Spec: some piece of `c` attacks `t` by a single step. -/
def stepAttacked (p : Position) (t : Square) (c : Color) : Bool :=
  (List.finRange 81).any fun s =>
    match p.pieceAt s with
    | some pc => pc.color == c && ((stepOffsets c.fwd pc.type).filterMap (Square.offset s)).contains t
    | none => false

theorem stepAttacked_eq (p : Position) (t : Square) (c : Color) :
    stepAttacked p t c = (probes c t).any (probeHit p c) := by
  have hag := probesAgree_all c t
  unfold probesAgree at hag
  simp only [List.all_eq_true, beq_iff_eq] at hag
  have hbd := List.all_eq_true.mp (probes_bounds c t)
  apply Bool.eq_iff_iff.mpr
  simp only [stepAttacked, List.any_eq_true, probeHit]
  constructor
  · rintro ⟨s, _, hs⟩
    split at hs
    · rename_i pc hpc
      simp only [Bool.and_eq_true, beq_iff_eq] at hs
      have hmem : pc.type ∈ allTypes := by cases pc.type <;> decide
      have := (hag s (List.mem_finRange s) pc.type hmem) ▸ hs.2
      obtain ⟨pr, hpr, hpr2⟩ := List.any_eq_true.mp this
      simp only [Bool.and_eq_true, beq_iff_eq] at hpr2
      refine ⟨pr, hpr, ?_⟩
      have hlt : pr.square < 81 := by rw [hpr2.1]; exact s.isLt
      rw [dif_pos hlt]
      have : (⟨pr.square, hlt⟩ : Square) = s := Fin.ext hpr2.1
      rw [this, hpc]
      simp [hs.1, hpr2.2]
    · simp at hs
  · rintro ⟨pr, hpr, hh⟩
    have hb := hbd pr hpr
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hb
    rw [dif_pos hb.1] at hh
    split at hh
    · rename_i pc hpc
      simp only [Bool.and_eq_true, beq_iff_eq] at hh
      refine ⟨⟨pr.square, hb.1⟩, List.mem_finRange _, ?_⟩
      rw [hpc]
      simp only [Bool.and_eq_true, beq_iff_eq, hh.1, true_and]
      have hmem : pc.type ∈ allTypes := by cases pc.type <;> decide
      have hany : ((probes c t).any fun pr' => pr'.square == (⟨pr.square, hb.1⟩ : Square).val &&
          maskHas pr'.mask pc.type) = true :=
        List.any_eq_true.mpr ⟨pr, hpr, by simp [hh.2]⟩
      have := (hag ⟨pr.square, hb.1⟩ (List.mem_finRange _) pc.type hmem).symm ▸ hany
      exact this
    · simp at hh

section cond
variable (s : State) (b ab mk o : Nat)

theorem evA (hb : b < 256) (h6 : s.locals 6 = some (.int IntTy.u8 b)) :
    evalExpr Gen.prog 4 s (.bin .ne (some ⟨32, true⟩) (.cast ⟨32, true⟩ (.var 6))
      (.const (.int ⟨32, true⟩ 0))) = .ok (boolVal (decide (b ≠ 0))) := by
  simp [evalExpr, h6, evalCast, evalBin, isPtr, evalBinInt, binInt, intOf, IntTy.toInt, IntTy.wrap,
    IntTy.modulus, IntTy.u8, Res.bind, Nat.mod_eq_of_lt (show b < 4294967296 by omega)]
  have : ¬ (2147483648 ≤ b) := by omega
  simp only [this, ite_false]
  by_cases h : b = 0 <;> simp [h, boolVal]

theorem evB (hb : b < 256) (hab : ab < 256) (h6 : s.locals 6 = some (.int IntTy.u8 b))
    (h3 : s.locals 3 = some (.int IntTy.u8 ab)) :
    evalExpr Gen.prog 5 s (.bin .eq (some ⟨32, false⟩) (.bin .band (some ⟨32, false⟩)
      (.cast ⟨32, false⟩ (.var 6)) (.const (.int ⟨32, false⟩ 16))) (.cast ⟨32, false⟩ (.var 3)))
      = .ok (boolVal (decide (b &&& 16 = ab))) := by
  simp [evalExpr, h6, h3, evalCast, evalBin, isPtr, evalBinInt, binInt, intOf, IntTy.u8, Res.bind,
    IntTy.modulus, Nat.mod_eq_of_lt (show b < 4294967296 by omega),
    Nat.mod_eq_of_lt (show ab < 4294967296 by omega)]

theorem evC (G : Block) (hb : b < 256) (hmk : mk < 65536) (h6 : s.locals 6 = some (.int IntTy.u8 b))
    (h5 : s.locals 5 = some (.ptr 8192 o)) (hG : s.mem 8192 = some G) (hl : o + 4 ≤ G.length)
    (hr : readBytes s.mem 8192 (o + 2) 2 = .ok (encodeLE 2 mk)) :
    evalExpr Gen.prog 6 s (.bin .ne (some ⟨32, true⟩) (.bin .band (some ⟨32, true⟩)
      (.cast ⟨32, true⟩ (.load (.int ⟨16, false⟩) (.field (.var 5) 2)))
      (.bin .shl (some ⟨32, true⟩) (.cast ⟨32, true⟩ (.cast ⟨16, false⟩ (.const (.int ⟨32, false⟩ 1))))
        (.bin .band (some ⟨32, false⟩) (.cast ⟨32, false⟩ (.var 6)) (.const (.int ⟨32, false⟩ 15)))))
      (.const (.int ⟨32, true⟩ 0))) = .ok (boolVal (decide (mk &&& 2 ^ (b &&& 15) ≠ 0))) := by
  have hk : b &&& 15 < 16 := Nat.lt_of_le_of_lt Nat.and_le_right (by decide)
  have hdec : decodeLE (encodeLE 2 mk) = mk := by
    simp [encodeLE, decodeLE]; omega
  generalize hkk : b &&& 15 = k at hk
  have hpow : 2 ^ k ≤ 32768 := by
    have : 2 ^ k ≤ 2 ^ 15 := Nat.pow_le_pow_right (by decide) (by omega)
    simpa using this
  have hand : mk &&& 2 ^ k ≤ mk := Nat.and_le_left
  simp only [evalExpr, h5, h6, Res.bind_eq, Res.bind_ok, ptrAddN, hG, show o + 2 ≤ G.length by omega,
    ite_true, load, Ty.size, IntTy.bytes, show (16:Nat) / 8 = 2 by rfl, hr, hdec]
  simp [evalCast, evalBin, isPtr, evalBinInt, binInt, intOf, IntTy.toInt, IntTy.wrap, IntTy.modulus,
    IntTy.u8, Res.bind, MiniC.guard, arith, IntTy.inRange, IntTy.minVal, IntTy.maxVal,
    Nat.mod_eq_of_lt (show b < 4294967296 by omega), Nat.mod_eq_of_lt (show mk < 4294967296 by omega), hkk]
  have hk32 : (k : Int) < 32 := by omega
  have hcast : ((2 : Int) ^ k) = ((2 ^ k : Nat) : Int) := (Int.natCast_pow 2 k).symm
  have hpz : ((2 : Int) ^ k) ≤ 32768 := by rw [hcast]; omega
  have hpz0 : (0 : Int) ≤ (2 : Int) ^ k := by rw [hcast]; exact Int.natCast_nonneg _
  rw [if_pos hk32]
  simp only
  rw [if_pos ⟨by omega, by omega⟩]
  have hmod : ((2 : Int) ^ k % 4294967296).toNat = 2 ^ k := by
    rw [Int.emod_eq_of_lt hpz0 (by omega), hcast]; rfl
  simp only [hmod, hdec]
  have hlt : mk &&& 2 ^ k < 2147483648 := by omega
  simp [boolVal, show ¬ (2147483648 ≤ mk &&& 2 ^ k) by omega,
    Nat.mod_eq_of_lt (show mk &&& 2 ^ k < 4294967296 by omega)]

end cond

def condVal (b ab mk : Nat) : Bool :=
  decide (b ≠ 0) && decide (b &&& 16 = ab) && decide (mk &&& 2 ^ (b &&& 15) ≠ 0)

theorem truthy_boolVal (x : Bool) : truthy (boolVal x) = .ok x := by cases x <;> rfl

theorem ev_land (s : State) {a b : Expr} {x y : Bool} (ha : EvE Gen.prog s a (boolVal x))
    (hb : EvE Gen.prog s b (boolVal y)) : EvE Gen.prog s (.land a b) (boolVal (x && y)) := by
  cases x
  · simpa using EvE.land_false ha (truthy_boolVal false)
  · simpa using EvE.land_true ha (truthy_boolVal true) hb (truthy_boolVal y)

theorem dec0 (n : Nat) : decide (n = 0) = !(n != 0) := by by_cases h : n = 0 <;> simp [h]

theorem condVal_hit (x : Option Piece) (c : Color) (mk : Nat) :
    condVal (pieceByte x).toNat (16 * c.idx) mk =
      match x with
      | some pc => pc.color == c && maskHas mk pc.type
      | none => false := by
  rcases x with _ | ⟨c', t⟩
  · rfl
  · cases c <;> cases c' <;> cases t <;>
      simp [condVal, pieceByte, Piece.code, PieceType.code, Color.idx, maskHas, Nat.shiftLeft_eq, dec0]

theorem G1_len : Gen.global_step_attack_probes.length = 6480 := by decide +kernel
theorem G2_len : Gen.global_step_attack_probe_count.length = 162 := by decide +kernel

theorem readByte {m : Mem} {b : Nat} {G : Block} (hG : m b = some G) (o : Nat) (ho : o < G.length) :
    readBytes m b o 1 = .ok [G.getD o 0] := by
  simp only [readBytes, hG, show o + 1 ≤ G.length by omega, ite_true]
  congr 1
  rw [List.take_one, List.head?_drop]
  simp [List.getD, ho]

theorem readByte2 {m : Mem} {b : Nat} {G : Block} (hG : m b = some G) (o : Nat) (ho : o + 1 < G.length) :
    readBytes m b o 2 = .ok [G.getD o 0, G.getD (o + 1) 0] := by
  simp only [readBytes, hG, show o + 2 ≤ G.length by omega, ite_true]
  congr 1
  apply List.ext_getElem
  · simp; omega
  · intro n h1 h2
    have : n < 2 := by simpa using h2
    match n, this with
    | 0, _ => simp [List.getD, show o < G.length by omega]
    | 1, _ => simp [List.getD, ho]

section loop
variable (p : Position) (c : Color) (t : Fin 81)

/-- Probe hits from index `i` on. -/
def hitsFrom (i : Nat) : Bool :=
  ((List.range (cnt c t)).drop i).any fun j => probeHit p c (prb c t j)

theorem hitsFrom_step (i : Nat) (hi : i < cnt c t) :
    hitsFrom p c t i = (probeHit p c (prb c t i) || hitsFrom p c t (i + 1)) := by
  unfold hitsFrom
  rw [List.drop_eq_getElem_cons (by simpa using hi)]
  simp

theorem hitsFrom_end : hitsFrom p c t (cnt c t) = false := by
  unfold hitsFrom; rw [List.drop_eq_nil_of_le (by simp)]; rfl

theorem hitsFrom_zero : hitsFrom p c t 0 = stepAttacked p t c := by
  rw [stepAttacked_eq, ← table_probes c t]
  unfold hitsFrom
  simp [List.any_map]; rfl

end loop

section exprs
variable (p : Position) (c : Color) (t : Fin 81) (s : State) (i : Nat)

theorem cnt_le (c : Color) (t : Fin 81) : cnt c t ≤ 10 := by rw [cnt_eq]; exact probes_length_le c t

theorem evCnt (hi : i < 256) (h4 : s.locals 4 = some (.int IntTy.u8 i))
    (h2 : s.locals 2 = some (.int IntTy.u32 c.idx)) (h1 : s.locals 1 = some (.int IntTy.u8 t.val))
    (hG2 : s.mem 8193 = some Gen.global_step_attack_probe_count) :
    evalExpr Gen.prog 6 s (.bin .lt (some ⟨32, true⟩) (.cast ⟨32, true⟩ (.var 4))
      (.cast ⟨32, true⟩ (.load (.int ⟨8, false⟩) (.index (.index (.const (.ptr 8193 0)) (.var 2) 81)
        (.var 1) 1)))) = .ok (boolVal (decide (i < cnt c t))) := by
  have hci : c.idx < 2 := by cases c <;> decide
  have hr := readByte hG2 (c.idx * 81 + t.val) (by rw [G2_len]; omega)
  have hcl := cnt_le c t
  simp only [evalExpr, h4, h2, h1, Res.bind_eq, Res.bind_ok, IntTy.u32, IntTy.u8, Bool.false_eq_true,
    ite_false, Res.bind, ptrAddN, hG2, G2_len, Nat.zero_add, Nat.mul_one]
  simp only [hG2, G2_len, show c.idx * 81 ≤ 162 by omega, show c.idx * 81 + t.val ≤ 162 by omega,
    ite_true, Res.bind,
    load, Ty.size, IntTy.bytes, show (8:Nat) / 8 = 1 by rfl, hr]
  have hc : (Gen.global_step_attack_probe_count[c.idx * 81 + t.val]?.getD 0).toNat = cnt c t := by
    simp [cnt, List.getD_eq_getElem?_getD]
  simp [decodeLE, hc, evalCast, evalBin, isPtr, evalBinInt, binInt, intOf, IntTy.toInt, IntTy.wrap,
    IntTy.modulus, boolVal, Nat.mod_eq_of_lt (show i < 4294967296 by omega),
    Nat.mod_eq_of_lt (show cnt c t < 4294967296 by omega)]
  have a1 : ¬ (2147483648 ≤ i) := by omega
  have a2 : ¬ (2147483648 ≤ cnt c t) := by omega
  simp only [a1, a2, ite_false]
  by_cases h : i < cnt c t
  · simp [h, show (i : Int) < cnt c t by omega]
  · simp [h, show ¬ ((i : Int) < cnt c t) by omega]

theorem evPtr (hi : i < 10) (h4 : s.locals 4 = some (.int IntTy.u8 i))
    (h2 : s.locals 2 = some (.int IntTy.u32 c.idx)) (h1 : s.locals 1 = some (.int IntTy.u8 t.val))
    (hG1 : s.mem 8192 = some Gen.global_step_attack_probes) :
    evalExpr Gen.prog 6 s (.index (.index (.index (.const (.ptr 8192 0)) (.var 2) 3240) (.var 1) 40)
      (.var 4) 4) = .ok (.ptr 8192 (pbase c t i)) := by
  have hci : c.idx < 2 := by cases c <;> decide
  have := t.isLt
  simp only [evalExpr, h4, h2, h1, Res.bind_eq, Res.bind_ok, IntTy.u32, IntTy.u8, Bool.false_eq_true,
    ite_false, Res.bind, ptrAddN, hG1, G1_len, Nat.zero_add]
  simp only [hG1, G1_len, show c.idx * 3240 ≤ 6480 by omega,
    show c.idx * 3240 + t.val * 40 ≤ 6480 by omega,
    show c.idx * 3240 + t.val * 40 + i * 4 ≤ 6480 by omega, ite_true, Res.bind]
  simp [pbase]

end exprs

theorem prb_square_lt (c : Color) (t : Fin 81) (i : Nat) (hi : i < cnt c t) :
    (prb c t i).square < 81 := by
  rw [cnt_eq] at hi
  rw [prb_eq c t i hi]
  have := List.all_eq_true.mp (probes_bounds c t) _ (List.getElem_mem hi)
  simp only [Bool.and_eq_true, decide_eq_true_eq] at this
  exact this.1

theorem prb_mask_lt (c : Color) (t : Fin 81) (i : Nat) (hi : i < cnt c t) :
    (prb c t i).mask < 65536 := by
  rw [cnt_eq] at hi
  rw [prb_eq c t i hi]
  have := List.all_eq_true.mp (probes_bounds c t) _ (List.getElem_mem hi)
  simp only [Bool.and_eq_true, decide_eq_true_eq] at this
  exact this.2

theorem evPiece (p : Position) (c : Color) (t : Fin 81) (s : State) (i : Nat) (hi : i < cnt c t)
    (h0 : s.locals 0 = some (posPtr' posBlock)) (h5 : s.locals 5 = some (.ptr 8192 (pbase c t i)))
    (hm : s.mem posBlock = some (encode p))
    (hG1 : s.mem 8192 = some Gen.global_step_attack_probes) :
    evalExpr Gen.prog 6 s (.load (.int ⟨8, false⟩) (.index (.field (.var 0) 0)
      (.load (.int ⟨8, false⟩) (.field (.var 5) 0)) 1)) = .ok (.int IntTy.u8 (bb p (prb c t i).square)) := by
  have hsq := prb_square_lt c t i hi
  have hcl := cnt_le c t
  have hci : c.idx < 2 := by cases c <;> decide
  have hpb : pbase c t i < 6480 := by unfold pbase; have := t.isLt; omega
  have hr1 := readByte hG1 (pbase c t i) (by rw [G1_len]; exact hpb)
  have hsqb : (Gen.global_step_attack_probes.getD (pbase c t i) 0).toNat = (prb c t i).square := rfl
  have hl := encode_length p
  have hr2 := readBoard hm _ hsq
  have hbb : bb p (prb c t i).square = (pieceByte (p.pieceAt ⟨_, hsq⟩)).toNat := by simp [bb, hsq]
  simp only [evalExpr, h0, h5, Res.bind_eq, Res.bind_ok, posPtr', ptrAddN, hm, hl, hG1, G1_len,
    show pbase c t i + 0 ≤ 6480 by omega, show (0 : Nat) + 0 ≤ 114 by omega, ite_true, Nat.add_zero,
    load, Ty.size, IntTy.bytes, show (8:Nat) / 8 = 1 by rfl, hr1, Res.bind, IntTy.u8,
    Bool.false_eq_true, ite_false, Nat.zero_add, Nat.mul_one]
  simp only [show pbase c t i ≤ 6480 by omega, ite_true, hr1, Res.pure_eq, decodeLE, Nat.mul_zero,
    Nat.add_zero]
  rw [hsqb]
  simp only [show (prb c t i).square ≤ 114 by omega, ite_true, hr2, decodeLE, Nat.mul_zero,
    Nat.add_zero, Res.pure_eq]
  simp only [Bool.false_eq_true, ite_false, hr2, Res.bind, decodeLE, Nat.mul_zero, Nat.add_zero, ← hbb]

theorem mask_bytes (c : Color) (t : Fin 81) (i : Nat) (hi : i < cnt c t) :
    [Gen.global_step_attack_probes.getD (pbase c t i + 2) 0,
     Gen.global_step_attack_probes.getD (pbase c t i + 2 + 1) 0] = encodeLE 2 (prb c t i).mask := by
  have hmk := prb_mask_lt c t i hi
  unfold prb prbOf at *
  simp only at hmk ⊢
  generalize Gen.global_step_attack_probes.getD (pbase c t i + 2) 0 = lo at hmk ⊢
  generalize Gen.global_step_attack_probes.getD (pbase c t i + 3) 0 = hi at hmk ⊢
  have h1 := lo.toNat_lt
  have h2 := hi.toNat_lt
  simp only [encodeLE, List.cons.injEq, and_true]
  constructor <;> apply UInt8.toNat_inj.mp <;> simp [UInt8.toNat_ofNat] <;> omega

theorem step_loop (p : Position) (c : Color) (t : Fin 81) :
    ∀ d i (s : State), i + d = cnt c t →
    s.locals 0 = some (posPtr' posBlock) → s.locals 1 = some (.int IntTy.u8 t.val) →
    s.locals 2 = some (.int IntTy.u32 c.idx) → s.locals 3 = some (.int IntTy.u8 (16 * c.idx)) →
    s.locals 4 = some (.int IntTy.u8 i) →
    s.mem posBlock = some (encode p) → s.mem 8192 = some Gen.global_step_attack_probes →
    s.mem 8193 = some Gen.global_step_attack_probe_count →
    if hitsFrom p c t i then ∃ s', ExS Gen.prog s Gen.step_square_attacked_loop0 (.ret (some true8)) s' ∧ s'.mem = s.mem
    else ∃ s', ExS Gen.prog s Gen.step_square_attacked_loop0 .normal s' ∧ s'.mem = s.mem := by
  intro d
  induction d with
  | zero =>
    intro i s hd h0 h1 h2 h3 h4 hm hG1 hG2
    have hi : i = cnt c t := by omega
    subst hi
    rw [hitsFrom_end]
    simp only [Bool.false_eq_true, ite_false]
    have hcl := cnt_le c t
    refine ⟨s, ?_, rfl⟩
    unfold Gen.step_square_attacked_loop0
    apply ExS.loop_brk
    exact ExS.ite (bc := false) (EvE_of_eval (evCnt c t s _ (by omega) h4 h2 h1 hG2))
      (by simp [truthy_boolVal]) ExS.brk
  | succ d ih =>
    intro i s hd h0 h1 h2 h3 h4 hm hG1 hG2
    have hi : i < cnt c t := by omega
    have hcl := cnt_le c t
    have hci : c.idx < 2 := by cases c <;> decide
    have hcond := EvE_of_eval (evCnt c t s i (by omega) h4 h2 h1 hG2)
    let s5 : State := { s with locals := s.locals.upd 5 (.ptr 8192 (pbase c t i)) }
    have hset5 : ExS Gen.prog s (.set 5 (.index (.index (.index (.const (.ptr 8192 0)) (.var 2) 3240)
        (.var 1) 40) (.var 4) 4)) .normal s5 :=
      ExS.set (EvE_of_eval (evPtr c t s i (by omega) h4 h2 h1 hG1))
    let b := bb p (prb c t i).square
    let s6 : State := { s5 with locals := s5.locals.upd 6 (.int IntTy.u8 b) }
    have hset6 : ExS Gen.prog s5 (.set 6 (.load (.int ⟨8, false⟩) (.index (.field (.var 0) 0)
        (.load (.int ⟨8, false⟩) (.field (.var 5) 0)) 1))) .normal s6 :=
      ExS.set (EvE_of_eval (evPiece p c t s5 i hi (by simp [s5, Locals.upd, h0])
        (by simp [s5, Locals.upd]) hm hG1))
    have hb : b < 256 := bb_lt p _
    have hpb : pbase c t i + 2 + 1 < Gen.global_step_attack_probes.length := by
      rw [G1_len]; unfold pbase; have := t.isLt; omega
    have hrm : readBytes s6.mem 8192 (pbase c t i + 2) 2 = .ok (encodeLE 2 (prb c t i).mask) := by
      rw [readByte2 hG1 _ hpb, mask_bytes c t i hi]
    have hA := EvE_of_eval (evA s6 b hb (by simp [s6, Locals.upd]))
    have hB := EvE_of_eval (evB s6 b (16 * c.idx) hb (by omega) (by simp [s6, Locals.upd])
      (by simp [s6, s5, Locals.upd, h3]))
    have hC := EvE_of_eval (evC s6 b (prb c t i).mask (pbase c t i) Gen.global_step_attack_probes hb
      (prb_mask_lt c t i hi) (by simp [s6, Locals.upd]) (by simp [s6, s5, Locals.upd]) hG1
      (by rw [G1_len]; unfold pbase; have := t.isLt; omega) hrm)
    have hcnd := ev_land s6 (ev_land s6 hA hB) hC
    have hval : (decide (b ≠ 0) && decide (b &&& 16 = 16 * c.idx) &&
        decide ((prb c t i).mask &&& 2 ^ (b &&& 15) ≠ 0)) = probeHit p c (prb c t i) := by
      have hsq := prb_square_lt c t i hi
      have hbb : b = (pieceByte (p.pieceAt ⟨_, hsq⟩)).toNat := by simp [b, bb, hsq]
      have := condVal_hit (p.pieceAt ⟨_, hsq⟩) c (prb c t i).mask
      unfold condVal at this
      rw [hbb, this]
      simp [probeHit, hsq]
    rw [hval] at hcnd
    rw [hitsFrom_step p c t i hi]
    by_cases hh : probeHit p c (prb c t i) = true
    · simp only [hh, Bool.true_or, ite_true]
      refine ⟨s6, ?_, rfl⟩
      unfold Gen.step_square_attacked_loop0
      apply ExS.loop_ret
      refine ExS.ite (bc := true) hcond (by simp [truthy_boolVal, hi]) ?_
      simp only [ite_true]
      refine ExS.seq hset5 (ExS.seq hset6 ?_)
      refine ExS.ite (bc := true) hcnd (by rw [hh]; rfl) ?_
      exact ExS.ret (EvE_of_eval (ev_true8 _))
    · simp only [Bool.not_eq_true] at hh
      simp only [hh, Bool.false_or]
      let s7 : State := { s6 with locals := s6.locals.upd 4 (.int IntTy.u8 (i + 1)) }
      have hbody : ExS Gen.prog s (.ite (.bin .lt (some ⟨32, true⟩) (.cast ⟨32, true⟩ (.var 4))
          (.cast ⟨32, true⟩ (.load (.int ⟨8, false⟩) (.index (.index (.const (.ptr 8193 0)) (.var 2) 81)
          (.var 1) 1)))) (.seq (.set 5 (.index (.index (.index (.const (.ptr 8192 0)) (.var 2) 3240)
          (.var 1) 40) (.var 4) 4)) (.seq (.set 6 (.load (.int ⟨8, false⟩) (.index (.field (.var 0) 0)
          (.load (.int ⟨8, false⟩) (.field (.var 5) 0)) 1))) (.ite (.land (.land (.bin .ne
          (some ⟨32, true⟩) (.cast ⟨32, true⟩ (.var 6)) (.const (.int ⟨32, true⟩ 0))) (.bin .eq
          (some ⟨32, false⟩) (.bin .band (some ⟨32, false⟩) (.cast ⟨32, false⟩ (.var 6))
          (.const (.int ⟨32, false⟩ 16))) (.cast ⟨32, false⟩ (.var 3)))) (.bin .ne (some ⟨32, true⟩)
          (.bin .band (some ⟨32, true⟩) (.cast ⟨32, true⟩ (.load (.int ⟨16, false⟩) (.field (.var 5) 2)))
          (.bin .shl (some ⟨32, true⟩) (.cast ⟨32, true⟩ (.cast ⟨16, false⟩ (.const (.int ⟨32, false⟩ 1))))
          (.bin .band (some ⟨32, false⟩) (.cast ⟨32, false⟩ (.var 6)) (.const (.int ⟨32, false⟩ 15)))))
          (.const (.int ⟨32, true⟩ 0)))) (.ret (some (.cast ⟨8, false⟩ (.bin .ne (some ⟨32, true⟩)
          (.const (.int ⟨32, true⟩ 1)) (.const (.int ⟨32, true⟩ 0)))))) .skip))) .brk) .normal s6 := by
        refine ExS.ite (bc := true) hcond (by simp [truthy_boolVal, hi]) ?_
        simp only [ite_true]
        refine ExS.seq hset5 (ExS.seq hset6 ?_)
        exact ExS.ite (bc := false) hcnd (by rw [hh]; rfl) ExS.skip
      have hstep : ExS Gen.prog s6 (.set 4 (.cast ⟨8, false⟩ (.bin .add (some ⟨32, true⟩)
          (.cast ⟨32, true⟩ (.var 4)) (.const (.int ⟨32, true⟩ 1))))) .normal s7 :=
        ExS.set (EvE_of_eval (ev_succ s6 i (by omega) (by simp [s6, s5, Locals.upd, h4])))
      have ihs := ih (i + 1) s7 (by omega) (by simp [s7, s6, s5, Locals.upd, h0])
        (by simp [s7, s6, s5, Locals.upd, h1]) (by simp [s7, s6, s5, Locals.upd, h2])
        (by simp [s7, s6, s5, Locals.upd, h3]) (by simp [s7, Locals.upd]) hm hG1 hG2
      split at ihs
      · rename_i hhit
        rw [if_pos hhit]
        obtain ⟨s', hs', hmem⟩ := ihs
        exact ⟨s', ExS.loop_next hbody (Or.inl rfl) hstep hs', hmem⟩
      · rename_i hhit
        rw [if_neg hhit]
        obtain ⟨s', hs', hmem⟩ := ihs
        exact ⟨s', ExS.loop_next hbody (Or.inl rfl) hstep hs', hmem⟩

/-- **`step_square_attacked` refines the spec's step attacks.** For every
    position, target square and attacker: no UB, terminates, returns 1 iff
    some piece of `c` attacks `t` by a single step, and writes nothing. -/
theorem step_square_attacked_refines (p : Position) (t : Square) (c : Color) (m : Mem)
    (hm : m posBlock = some (encode p)) (hG1 : m 8192 = some Gen.global_step_attack_probes)
    (hG2 : m 8193 = some Gen.global_step_attack_probe_count) :
    ∃ s', ExS Gen.prog ⟨frameLocals Gen.step_square_attacked.params
        [posPtr' posBlock, .int IntTy.u8 t.val, .int IntTy.u32 c.idx], m, false⟩
      Gen.step_square_attacked.body
      (.ret (some (if stepAttacked p t c then true8 else false8))) s' ∧ s'.mem = m := by
  have hci : c.idx < 2 := by cases c <;> decide
  let L0 := frameLocals Gen.step_square_attacked.params [posPtr' posBlock, .int IntTy.u8 t.val, .int IntTy.u32 c.idx]
  let s0 : State := ⟨L0, m, false⟩
  let s1 : State := { s0 with locals := s0.locals.upd 3 (.int IntTy.u8 (16 * c.idx)) }
  have hset3 : ExS Gen.prog s0 (.set 3 (.cast ⟨8, false⟩ (.bin .shl (some ⟨32, false⟩)
      (.cast ⟨32, false⟩ (.var 2)) (.const (.int ⟨32, true⟩ 4))))) .normal s1 := by
    apply ExS.set
    apply EvE_of_eval (n := 4)
    cases c <;> rfl
  let s2 : State := { s1 with locals := s1.locals.upd 4 (.int IntTy.u8 0) }
  have hset4 : ExS Gen.prog s1 (.set 4 (.cast ⟨8, false⟩ (.const (.int ⟨32, true⟩ 0)))) .normal s2 :=
    ExS.set (EvE_of_eval (n := 3) rfl)
  have hloop := step_loop p c t (cnt c t) 0 s2 (by omega) (by simp [s2, s1, s0, L0, Locals.upd]; rfl)
    (by simp [s2, s1, s0, L0, Locals.upd]; rfl) (by simp [s2, s1, s0, L0, Locals.upd]; rfl)
    (by simp [s2, s1, Locals.upd]) (by simp [s2, Locals.upd]) hm hG1 hG2
  rw [hitsFrom_zero] at hloop
  unfold Gen.step_square_attacked
  simp only
  split
  · rename_i hh
    rw [if_pos hh] at hloop
    obtain ⟨s', hs', hmem⟩ := hloop
    exact ⟨s', ExS.seq hset3 (ExS.seq_ret (ExS.seq hset4 hs')), hmem⟩
  · rename_i hh
    rw [if_neg hh] at hloop
    obtain ⟨s', hs', hmem⟩ := hloop
    exact ⟨s', ExS.seq hset3 (ExS.seq (ExS.seq hset4 hs') (ExS.ret (EvE_of_eval (n := 5) rfl))), hmem⟩

end Shogi.C.Proofs
