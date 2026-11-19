/-
  T8: the whole filtering loop of `generate_legal_mut_internal`: over the
  pseudo-legal moves `Ms`, the C appends exactly those the spec keeps.
-/
import Shogi.C.Proofs.KingsUniq
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

namespace Shogi.C.Proofs
variable {posBlock : Nat}
open MiniC Shogi Shogi.C Shogi.Tables

def keepBytes (p : Position) (fuel : Nat) (Ms : List Move) : List (List UInt8) :=
  Ms.filterMap fun m => if specKeep p fuel m then some (moveBytes p m) else none

def RB : Nat := 1000000100

/-- Budget covering all allocations of one generator call with ≤7200 moves,
    including the nested uchifuzume replies at charge `charge`. -/
def loopBudget (charge : Nat) : Nat := 7200 * 7 + charge + 2000000200

theorem legal_loop {p : Position} {fuel : Nat} {Ms : List Move} {pb cntb Sb mb mo cb co cap : Nat}
    {PB CB : List UInt8} (hS : p.Shaped) (hK : KingsUnique p)
    (hMs : ∀ m ∈ Ms, m ∈ p.pseudoMoves)
    (rem0 n0 : Nat) (hglobal : n0 + 400 * rem0 < 2 ^ 64) (hrembig : recDelta ≤ rem0) (hrem0ub : rem0 ≤ 200 * recDelta)
    (hrec : ∀ m ∈ Ms, Position.isPawnDrop m → (p.play m).inCheck (p.play m).side → RecSpec (posBlock := posBlock) fuel (rem0 - recDelta) (p.play m))
    (hcnt : Ms.length < 2 ^ 64) (hPB : 5 * Ms.length ≤ PB.length)
    (hmv : ∀ j (hj : j < Ms.length), (PB.drop (5 * j)).take 5 = moveBytes p Ms[j])
    (hpb0 : pb ≠ 0) (hS0 : Sb ≠ 0) (hc0 : cntb ≠ 0) (hpm : posBlock ≠ mb) (hpc : posBlock ≠ cb)
    (hpbm : pb ≠ mb ∧ pb ≠ cb) (hSm : Sb ≠ mb ∧ Sb ≠ cb) (hcm : cntb ≠ mb ∧ cntb ≠ cb)
    (htm : ∀ g, 8192 ≤ g → g ≤ 8196 → g ≠ mb ∧ g ≠ cb) :
    ∀ (d i : Nat) (s : State) (L : List (List UInt8)) (n : Nat) (rem : Nat), i + d = Ms.length →
      s.locals 0 = some (posPtr' posBlock) → s.locals 1 = some (.ptr mb mo) → s.locals 2 = some (.int IntTy.u64 cap) →
      s.locals 3 = some (.int IntTy.u8 1) → s.locals 4 = some (.ptr pb 0) → s.locals 5 = some (.ptr cntb 0) →
      s.locals 6 = some (.ptr cb co) → s.locals 7 = some (.int IntTy.u32 p.side.idx) →
      s.locals 8 = some (.ptr Sb 0) → s.locals 9 = some (.int IntTy.u64 i) →
      s.mem posBlock = some (encode p) → s.mem pb = some PB → s.mem Sb = some (ksRec p p.side) →
      s.mem cntb = some CB → readBytes s.mem cntb 0 8 = .ok (encodeLE 8 Ms.length) →
      Buf s.mem mb mo cb co cap L → TablesIn s.mem → Fresh s.mem n → p.inCheck p.side.opp = false →
      ((Ms.drop i).map (recCharge (rem0 - recDelta + 30) p)).sum + 2000000200 ≤ rem → n + rem ≤ n0 + rem0 → s.ro = false →
      ∃ s', ExS Gen.prog s (.loop lpBody lpStep) .normal s' ∧
        Buf s'.mem mb mo cb co cap (L ++ keepBytes p fuel (Ms.drop i)) ∧ s'.mem posBlock = some (encode p) ∧
        s'.locals 6 = s.locals 6 ∧ Frame s.mem s'.mem mb cb ∧
        ∃ f, Fresh s'.mem f ∧ f ≤ n + rem := by
  have hcond : ∀ (s : State) (i : Nat), s.locals 9 = some (.int IntTy.u64 i) → s.locals 5 = some (.ptr cntb 0) →
      readBytes s.mem cntb 0 8 = .ok (encodeLE 8 Ms.length) →
      EvE Gen.prog s lpCond (boolVal (decide (i < Ms.length))) := by
    intro s i h9 h5 hr
    have hl : EvE Gen.prog s (.load (.int ⟨64, false⟩) (.var 5)) (.int ⟨64, false⟩ Ms.length) :=
      EvE.load (EvE.var h5) (by
        simp only [load, Ty.size, IntTy.bytes, show (64 : Nat) / 8 = 8 by rfl, hr]
        simp [Res.bind, pure, decode_encode8 _ hcnt])
    refine EvE.bin (EvE.var h9) hl ?_
    simp [evalBin, isPtr, evalBinInt, binInt, intOf, IntTy.u64, Res.bind]
  intro d
  induction d with
  | zero =>
    intro i s L n rem hd h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 hp hpb hSb hcb hrc hb ht hf hnc hrem hnr hro
    have : i = Ms.length := by omega
    subst this
    refine ⟨s, ExS.loop_brk (ExS.ite (bc := false) (hcond s _ h9 h5 hrc) (by simp [truthy_boolVal]) ExS.brk), ?_, hp, rfl, Frame.refl _ _ _, n, hf, by omega⟩
    simpa [keepBytes] using hb
  | succ d ih =>
    intro i s L n rem hd h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 hp hpb hSb hcb hrc hb ht hf hnc hrem hnr hro
    have hi : i < Ms.length := by omega
    let m := Ms[i]
    have hmi : m ∈ Ms := List.getElem_mem hi
    have h64iter : n + rem0 + 2000000 < 2 ^ 64 := by omega
    have hglobalp : (n + 6) + 401 * (rem0 - recDelta) < 2 ^ 64 := by
      have hle : (n + 6) + 401 * (rem0 - recDelta) ≤
          n0 + 400 * rem0 := by
        unfold recDelta at hrembig hrem0ub ⊢
        omega
      exact Nat.lt_of_le_of_lt hle hglobal
    obtain ⟨o, s1, e1, ho, hb1, hp1, hro1, hl1, hfr1, f, hf1, hfb⟩ := iter_one hS hK (hMs m hmi) fuel rem0 (hrec m hmi)
      h0 h1 h2 h3 h4 h6 h7 h8 h9 hp hpb (by omega) (hmv i hi) hSb hb ht hf hnc h64iter hglobalp hrembig hrem0ub hro hpb0 hS0 hpm hpc
    let s2 : State := { s1 with locals := s1.locals.upd 9 (.int IntTy.u64 (i + 1)) }
    have es : ExS Gen.prog s1 lpStep .normal s2 := by
      apply ExS.set; apply EvE_of_eval (n := 4)
      simp [evalExpr, hl1 9 (by omega), h9, evalCast, evalBin, isPtr, evalBinInt, binInt, intOf, IntTy.u64,
        IntTy.modulus, Res.bind, IntTy.toInt, IntTy.wrap, Nat.mod_eq_of_lt (show i < 2 ^ 64 by omega),
        Nat.mod_eq_of_lt (show i + 1 < 2 ^ 64 by omega)]
    have hl2 : ∀ x, x < 9 → s2.locals x = s.locals x := fun x hx => by
      simp [s2, Locals.upd, show x ≠ 9 by omega]; exact hl1 x (by omega)
    have keepM : ∀ b, s.mem b ≠ none → b ≠ 0 → b ≠ mb → b ≠ cb → s2.mem b = s.mem b := fun b h a c d =>
      hfr1 b a c d h
    have hpb2 : s2.mem pb = some PB := by rw [keepM pb (by rw [hpb]; simp) hpb0 hpbm.1 hpbm.2]; exact hpb
    have hSb2 : s2.mem Sb = some (ksRec p p.side) := by rw [keepM Sb (by rw [hSb]; simp) hS0 hSm.1 hSm.2]; exact hSb
    have hcb2 : s2.mem cntb = some CB := by rw [keepM cntb (by rw [hcb]; simp) hc0 hcm.1 hcm.2]; exact hcb
    have hrc2 : readBytes s2.mem cntb 0 8 = .ok (encodeLE 8 Ms.length) := by
      unfold readBytes at hrc ⊢; rw [hcb2]; rw [hcb] at hrc; exact hrc
    have ht2 : TablesIn s2.mem := by
      have k : ∀ g, 8192 ≤ g → g ≤ 8196 → s.mem g ≠ none → s2.mem g = s.mem g := fun g a b c =>
        keepM g c (by omega) (htm g a b).1 (htm g a b).2
      exact ⟨by rw [k _ (by decide) (by decide) (by rw [ht.g1]; simp)]; exact ht.g1,
        by rw [k _ (by decide) (by decide) (by rw [ht.g2]; simp)]; exact ht.g2,
        by rw [k _ (by decide) (by decide) (by rw [ht.g3]; simp)]; exact ht.g3,
        by rw [k _ (by decide) (by decide) (by rw [ht.g4]; simp)]; exact ht.g4,
        by rw [k _ (by decide) (by decide) (by rw [ht.g5]; simp)]; exact ht.g5⟩
    have hdrop_sum : ((Ms.drop i).map (recCharge (rem0 - recDelta + 30) p)).sum =
        recCharge (rem0 - recDelta + 30) p m + ((Ms.drop (i + 1)).map (recCharge (rem0 - recDelta + 30) p)).sum := by
      rw [List.drop_eq_getElem_cons hi]
      simp only [List.map_cons, List.sum_cons]
      rfl
    have hsub : recCharge (rem0 - recDelta + 30) p m ≤ rem := by
      have hle : recCharge (rem0 - recDelta + 30) p m ≤ ((Ms.drop i).map (recCharge (rem0 - recDelta + 30) p)).sum := by
        rw [hdrop_sum]
        omega
      omega
    have hrem' : ((Ms.drop (i + 1)).map (recCharge (rem0 - recDelta + 30) p)).sum + 2000000200 ≤
        rem - recCharge (rem0 - recDelta + 30) p m := by
      omega
    have hnr' : f + (rem - recCharge (rem0 - recDelta + 30) p m) ≤ n0 + rem0 := by
      have h1 : f + (rem - recCharge (rem0 - recDelta + 30) p m) ≤
          (n + recCharge (rem0 - recDelta + 30) p m) + (rem - recCharge (rem0 - recDelta + 30) p m) :=
        Nat.add_le_add_right hfb _
      have h2 : (n + recCharge (rem0 - recDelta + 30) p m) + (rem - recCharge (rem0 - recDelta + 30) p m) = n + rem := by
        rw [Nat.add_assoc, Nat.add_sub_of_le hsub]
      omega
    obtain ⟨s', e', hb', hp', h6', hfr', f', hf', hfb'⟩ := ih (i + 1) s2 _ f (rem - recCharge (rem0 - recDelta + 30) p m) (by omega)
      (by rw [hl2 0 (by omega)]; exact h0) (by rw [hl2 1 (by omega)]; exact h1) (by rw [hl2 2 (by omega)]; exact h2)
      (by rw [hl2 3 (by omega)]; exact h3) (by rw [hl2 4 (by omega)]; exact h4) (by rw [hl2 5 (by omega)]; exact h5)
      (by rw [hl2 6 (by omega)]; exact h6) (by rw [hl2 7 (by omega)]; exact h7) (by rw [hl2 8 (by omega)]; exact h8)
      (by simp [s2, Locals.upd]) hp1 hpb2 hSb2 hcb2 hrc2 hb1 ht2 hf1 hnc
      hrem' hnr' hro1
    refine ⟨s', ExS.loop_next (ExS.ite (bc := true) (hcond s i h9 h5 hrc) (by simp [truthy_boolVal, hi]) e1) ho es e',
      ?_, hp', by rw [h6', hl2 6 (by omega)], Frame.trans ?_ hfr', f', hf', by
          have h1 : f' ≤ f + (rem - recCharge (rem0 - recDelta + 30) p m) := hfb'
          have h2 : f + (rem - recCharge (rem0 - recDelta + 30) p m) ≤ n + rem := by
            have hh : f + (rem - recCharge (rem0 - recDelta + 30) p m) ≤
                (n + recCharge (rem0 - recDelta + 30) p m) + (rem - recCharge (rem0 - recDelta + 30) p m) :=
              Nat.add_le_add_right hfb _
            rw [Nat.add_assoc, Nat.add_sub_of_le hsub] at hh
            exact hh
          exact Nat.le_trans h1 h2⟩
    · have hdrop : keepBytes p fuel (Ms.drop i) =
        (if specKeep p fuel m then [moveBytes p m] else []) ++ keepBytes p fuel (Ms.drop (i + 1)) := by
        rw [List.drop_eq_getElem_cons hi]; unfold keepBytes; simp only [List.filterMap_cons]
        split <;> simp_all [m]
      rw [hdrop, ← List.append_assoc]; exact hb'
    · intro x a b c d
      exact hfr1 x a b c d


end Shogi.C.Proofs
