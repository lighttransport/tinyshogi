/-
  T8: one full iteration of the legality loop on the probe path, and the
  combined statement: an iteration appends the move exactly when the spec's
  `legalAux` test keeps it.
-/
import Shogi.C.Proofs.LegalProbe

namespace Shogi.C.Proofs
open MiniC Shogi Shogi.C Shogi.Tables

theorem iter_slow {s : State} {p : Position} {m : Move} {pb i n Sb mb mo cb co cap : Nat} {PB : List UInt8}
    {L : List (List UInt8)} (hS : p.Shaped) (hK : KingsUnique p) (hm : m ∈ p.pseudoMoves) (fuel : Nat)
    (hrec : RecSpec (p.play m) (!(Position.legalAux fuel (p.play m)).isEmpty))
    (hl0 : s.locals 0 = some posPtr) (hl1 : s.locals 1 = some (.ptr mb mo)) (hl2 : s.locals 2 = some (.int IntTy.u64 cap))
    (hl3 : s.locals 3 = some (.int IntTy.u8 1))
    (hl4 : s.locals 4 = some (.ptr pb 0)) (hl6 : s.locals 6 = some (.ptr cb co))
    (hl7 : s.locals 7 = some (.int IntTy.u32 p.side.idx))
    (hl8 : s.locals 8 = some (.ptr Sb 0)) (hl9 : s.locals 9 = some (.int IntTy.u64 i))
    (hpos : s.mem posBlock = some (encode p)) (hpb : s.mem pb = some PB) (hi : 5 * i + 5 ≤ PB.length)
    (hmv : (PB.drop (5 * i)).take 5 = moveBytes p m) (hSb : s.mem Sb = some (ksRec p p.side))
    (hbuf : Buf s.mem mb mo cb co cap L) (htab : TablesIn s.mem) (hf : Fresh s.mem n) (h64 : n + 4000000200 < 2 ^ 64)
    (hro : s.ro = false) (hpb0 : pb ≠ 0) (hS0 : Sb ≠ 0) (hpm : posBlock ≠ mb) (hpc : posBlock ≠ cb)
    (hslow : needsProbeC (ksRec p p.side) p m = true ∨ Position.isPawnDrop m = true) :
    ∃ s', ExS Gen.prog s (.seq lp0 (.seq lp1 (.seq lp2 (.seq lp3 (.seq lp4 (.seq lp5 (.seq lp6 (.seq lp7
        (.seq lp8 lp9))))))))) .normal s' ∧
      Buf s'.mem mb mo cb co cap (L ++ (if specKeep p fuel m then [moveBytes p m] else [])) ∧
      s'.mem posBlock = some (encode p) ∧ s'.ro = false ∧ (∀ x, x < 10 → s'.locals x = s.locals x) ∧
      Frame s.mem s'.mem mb cb ∧ ∃ f, Fresh s'.mem f ∧ f ≤ n + 1000000030 := by
  have hnpb : n ≠ pb := fun e => by rw [← e, hf.2.2 n (Nat.le_refl _)] at hpb; cases hpb
  have hnS : n ≠ Sb := fun e => by rw [← e, hf.2.2 n (Nat.le_refl _)] at hSb; cases hSb
  have hnp' : n ≠ posBlock := fun e => by rw [← e, hf.2.2 n (Nat.le_refl _)] at hpos; cases hpos
  have hnb := hbuf.ne_fresh hf
  have e0 := lp0_spec hl4 hl9 hpb hi hmv hf (by omega) hro hpb0
  let m1 := ((s.mem.upd 0 (encodeLE 8 (n + 1))).upd n (List.replicate 5 0)).write n 0 (moveBytes p m)
  let s1 : State := { s with mem := m1, locals := s.locals.upd 10 (.ptr n 0) }
  have hm1o : ∀ x, x ≠ 0 → x ≠ n → m1 x = s.mem x := fun x a b => by
    simp only [m1]; rw [Mem.write_ne b, Mem.upd_ne b, Mem.upd_ne a]
  have hMl : (moveBytes p m).length = 5 := by cases m <;> rfl
  have hm1n : m1 n = some (moveBytes p m) := by
    simp only [m1]; rw [write_some Mem.upd_eq]; simp [wrb, hMl]
  have hP0 : posBlock ≠ 0 := by decide
  obtain ⟨s2, e1, hm2, hro2, l11, hl2'⟩ := np_spec (s := s1) hm (by simp [s1, Locals.upd]; exact hl0)
    (by simp [s1, Locals.upd]; exact hl8) (by show m1 Sb = _; rw [hm1o Sb hS0 (Ne.symm hnS)]; exact hSb)
    (by simp [s1, Locals.upd]) hm1n (by show m1 posBlock = _; rw [hm1o _ hP0 (Ne.symm hnp')]; exact hpos)
  have e2 := pd_spec (s := s2) (p := p) (m := m) (n := n) (by rw [hl2' 10 (by omega)]; simp [s1, Locals.upd])
    (by rw [hm2]; exact hm1n)
  let s3 : State := { s2 with locals := s2.locals.upd 17 (u8 (if Position.isPawnDrop m then 1 else 0)) }
  have hl3' : ∀ x, x < 10 → s3.locals x = s.locals x := fun x hx => by
    simp [s3, Locals.upd, show x ≠ 17 by omega]; rw [hl2' x (by omega)]; simp [s1, Locals.upd, show x ≠ 10 by omega]
  have hm3 : s3.mem = m1 := hm2
  have hbuf3 : Buf s3.mem mb mo cb co cap L := by
    rw [hm3]; exact hbuf.frame (hm1o mb hbuf.mb0 (Ne.symm hnb.1)) (hm1o cb hbuf.cb0 (Ne.symm hnb.2))
  have hf3 : Fresh s3.mem (n + 1) := by rw [hm3]; exact (hf.after_alloc _).write hf.2.1
  have htab3 : TablesIn s3.mem := by
    rw [hm3]
    have k : ∀ g, g ≠ 0 → s.mem g ≠ none → m1 g = s.mem g := fun g a b =>
      hm1o g a (fun e => b (by rw [e]; exact hf.2.2 _ (Nat.le_refl _)))
    exact ⟨by rw [k _ (by decide) (by rw [htab.g1]; simp)]; exact htab.g1,
      by rw [k _ (by decide) (by rw [htab.g2]; simp)]; exact htab.g2,
      by rw [k _ (by decide) (by rw [htab.g3]; simp)]; exact htab.g3,
      by rw [k _ (by decide) (by rw [htab.g4]; simp)]; exact htab.g4,
      by rw [k _ (by decide) (by rw [htab.g5]; simp)]; exact htab.g5⟩
  have hI : PInv s3 p mb mo cb co cap n L :=
    ⟨by rw [hl3' 0 (by omega)]; exact hl0, by rw [hl3' 1 (by omega)]; exact hl1, by rw [hl3' 2 (by omega)]; exact hl2,
     by rw [hl3' 6 (by omega)]; exact hl6, by rw [hl3' 7 (by omega)]; exact hl7,
     by simp [s3, Locals.upd]; rw [hl2' 10 (by omega)]; simp [s1, Locals.upd],
     by rw [hm3, hm1o _ hP0 (Ne.symm hnp')]; exact hpos, hbuf3, htab3,
     by show s2.ro = false; rw [hro2]; exact hro⟩
  have hn3 : s3.mem n = some (moveBytes p m) := by rw [hm3]; exact hm1n
  have l3 : s3.locals 3 = some (.int IntTy.u8 1) := by rw [hl3' 3 (by omega)]; exact hl3
  have l11' : s3.locals 11 = some (u8 (if needsProbeC (ksRec p p.side) p m then 1 else 0)) := by
    simp [s3, Locals.upd]; exact l11
  have l17 : s3.locals 17 = some (u8 (if Position.isPawnDrop m then 1 else 0)) := by simp [s3, Locals.upd]
  have hpre : ∀ {o t}, ExS Gen.prog s3 (.seq lp3 (.seq lp4 (.seq lp5 (.seq lp6 (.seq lp7 (.seq lp8 lp9)))))) o t →
      ExS Gen.prog s (.seq lp0 (.seq lp1 (.seq lp2 (.seq lp3 (.seq lp4 (.seq lp5 (.seq lp6 (.seq lp7
        (.seq lp8 lp9))))))))) o t :=
    fun h => ExS.seq e0 (ExS.seq (by rw [lp1_eq]; exact e1) (ExS.seq (by rw [lp2_eq]; exact e2) h))
  have hfr3 : ∀ x, x ≠ 0 → s.mem x ≠ none → s3.mem x = s.mem x := fun x a b => by
    rw [hm3]; exact hm1o x a (fun e => b (by rw [e]; exact hf.2.2 _ (Nat.le_refl _)))
  have fin : ∀ s' : State, s'.ro = false → (∀ x, x < 10 → s'.locals x = s3.locals x) →
      (∀ x, x ≠ 0 → x ≠ mb → x ≠ cb → s3.mem x ≠ none → s'.mem x = s3.mem x) →
      s'.ro = false ∧ (∀ x, x < 10 → s'.locals x = s.locals x) ∧ Frame s.mem s'.mem mb cb := by
    intro s' r l f
    refine ⟨r, fun x hx => by rw [l x hx, hl3' x hx], fun x a b c d => ?_⟩
    rw [f x a b c (by rw [hfr3 x a d]; exact d), hfr3 x a d]
  cases hpd : Position.isPawnDrop m
  · -- not a pawn drop: the probe path
    have hnp : needsProbeC (ksRec p p.side) p m = true := by rcases hslow with h | h; exact h; rw [hpd] at h; cases h
    obtain ⟨s', e', hb', hp', hr', hl', hf', hfr'⟩ := probe_path p hS hK m hm hpd hI hn3 hf3 (by omega) hf.2.1 l3
      (by rw [l11', hnp]; rfl) (by rw [l17, hpd]; rfl) (Ne.symm hnb.1 |>.symm |> fun h => by
        intro e; exact hnb.1 (by rw [e])) (by intro e; exact hnb.2 (by rw [e])) (by decide) hpm hpc
    obtain ⟨f1, f2, f3⟩ := fin s' hr' hl' hf'
    obtain ⟨ff, hff, hffb⟩ := hfr'
    refine ⟨s', hpre e', ?_, hp', f1, f2, f3, ff, hff, by omega⟩
    have hk : specKeep p fuel m = !(p.play m).inCheck p.side := by simp [specKeep, hpd]
    rw [hk]; cases h : (p.play m).inCheck p.side <;> simp [h] at hb' ⊢ <;> exact hb'
  · -- a pawn drop: the probe path with the uchifuzume recursion
    obtain ⟨s', e', hb', hp', hr', hl', hf', hfr'⟩ := probe_path_drop p hS hK m hm hpd _ hrec hI hn3 hf3 (by omega) hf.2.1 l3
      l11' (by rw [l17, hpd]; rfl) (by intro e; exact hnb.1 (by rw [e])) (by intro e; exact hnb.2 (by rw [e])) rfl hpm hpc
    obtain ⟨f1, f2, f3⟩ := fin s' hr' hl' hf'
    refine ⟨s', hpre e', ?_, hp', f1, f2, f3, by obtain ⟨f, hf1, hf2⟩ := hfr'; exact ⟨f, hf1, by omega⟩⟩
    have hk : specKeep p fuel m = (!(p.play m).inCheck p.side &&
        !((p.play m).inCheck (p.play m).side && !!(Position.legalAux fuel (p.play m)).isEmpty)) := by
      simp [specKeep, hpd]
    rw [hk]; exact hb'

/-- **One iteration of the C legality loop keeps a pseudo-legal move exactly
    when the spec's `legalAux (fuel + 1)` test does** (given the recursive
    reply count for checking pawn drops), and leaves the position unchanged. -/
theorem iter_one {s : State} {p : Position} {m : Move} {pb i n Sb mb mo cb co cap : Nat} {PB : List UInt8}
    {L : List (List UInt8)} (hS : p.Shaped) (hK : KingsUnique p) (hm : m ∈ p.pseudoMoves) (fuel : Nat)
    (hrec : RecSpec (p.play m) (!(Position.legalAux fuel (p.play m)).isEmpty))
    (hl0 : s.locals 0 = some posPtr) (hl1 : s.locals 1 = some (.ptr mb mo)) (hl2 : s.locals 2 = some (.int IntTy.u64 cap))
    (hl3 : s.locals 3 = some (.int IntTy.u8 1))
    (hl4 : s.locals 4 = some (.ptr pb 0)) (hl6 : s.locals 6 = some (.ptr cb co))
    (hl7 : s.locals 7 = some (.int IntTy.u32 p.side.idx))
    (hl8 : s.locals 8 = some (.ptr Sb 0)) (hl9 : s.locals 9 = some (.int IntTy.u64 i))
    (hpos : s.mem posBlock = some (encode p)) (hpb : s.mem pb = some PB) (hi : 5 * i + 5 ≤ PB.length)
    (hmv : (PB.drop (5 * i)).take 5 = moveBytes p m) (hSb : s.mem Sb = some (ksRec p p.side))
    (hbuf : Buf s.mem mb mo cb co cap L) (htab : TablesIn s.mem) (hf : Fresh s.mem n) (h64 : n + 4000000200 < 2 ^ 64)
    (hro : s.ro = false) (hpb0 : pb ≠ 0) (hS0 : Sb ≠ 0) (hpm : posBlock ≠ mb) (hpc : posBlock ≠ cb) :
    ∃ o s', ExS Gen.prog s (.seq lp0 (.seq lp1 (.seq lp2 (.seq lp3 (.seq lp4 (.seq lp5 (.seq lp6 (.seq lp7
        (.seq lp8 lp9))))))))) o s' ∧ (o = .normal ∨ o = .cont) ∧
      Buf s'.mem mb mo cb co cap (L ++ (if specKeep p fuel m then [moveBytes p m] else [])) ∧
      s'.mem posBlock = some (encode p) ∧ s'.ro = false ∧ (∀ x, x < 10 → s'.locals x = s.locals x) ∧
      Frame s.mem s'.mem mb cb ∧ ∃ f, Fresh s'.mem f ∧ f ≤ n + 1000000030 := by
  by_cases hfast : needsProbeC (ksRec p p.side) p m = false ∧ Position.isPawnDrop m = false
  · obtain ⟨s', e', hb', hf2, hl2, hfr, hro'⟩ := iter_fast (.seq lp4 (.seq lp5 (.seq lp6 (.seq lp7 (.seq lp8 lp9))))) hm hl0 hl1 hl2
      hl4 hl6 hl8 hl9 hpos hpb hi hmv hSb hbuf hf (by omega) hro hpb0 hS0 hfast.1 hfast.2
    have hk : specKeep p fuel m = true := by
      have := cKeep_eq p hS hK fuel m hm
      unfold cKeep at this
      rw [if_pos (by simp [hfast.1, hfast.2])] at this
      exact this.symm
    exact ⟨.cont, s', e', Or.inr rfl, by rw [hk]; simpa using hb', hfr.pos hpm hpc hpos, hro', hl2, hfr,
      _, hf2, by omega⟩
  · have hslow : needsProbeC (ksRec p p.side) p m = true ∨ Position.isPawnDrop m = true := by
      cases h1 : needsProbeC (ksRec p p.side) p m <;> cases h2 : Position.isPawnDrop m <;> simp_all
    obtain ⟨s', e', hb', hp', hx⟩ := iter_slow hS hK hm fuel hrec hl0 hl1 hl2 hl3 hl4 hl6 hl7 hl8 hl9 hpos hpb hi hmv hSb
      hbuf htab hf h64 hro hpb0 hS0 hpm hpc hslow
    exact ⟨.normal, s', e', Or.inl rfl, hb', hp', hx⟩

end Shogi.C.Proofs
