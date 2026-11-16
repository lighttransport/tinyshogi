/-
  T8: the whole of `generate_legal_mut_internal(position, moves, capacity, 1)`.
-/
import Shogi.C.Proofs.GenPseudo
import Shogi.MoveCount

namespace Shogi.C.Proofs
open MiniC Shogi Shogi.C

theorem Buf.of_eq {m m' : Mem} {mb mo cb co cap : Nat} {L : List (List UInt8)} (h : Buf m mb mo cb co cap L)
    (h1 : m' mb = m mb) (h2 : m' cb = m cb) : Buf m' mb mo cb co cap L :=
  ⟨by rw [h2]; exact h.cnt, by rw [h1]; exact h.buf, h.len, h.ne, h.mb0, h.cb0, h.cap64⟩

theorem readBytes_of_eq {m m' : Mem} {b : Nat} (h : m' b = m b) (o k : Nat) :
    readBytes m' b o k = readBytes m b o k := by
  unfold readBytes; rw [h]

/-- **`generate_legal_mut_internal` with uchifuzume enforcement.** From a
    call with an output array of `cap` moves, the function returns, and there
    is a reordering `Ms` of the spec's pseudo-legal moves such that the
    output holds the spec-kept moves of `Ms` (capped at `cap`) and the
    returned value is their count.  Assumes the uchifuzume reply spec
    `RecSpec` for the checking pawn drops only (the C recurses exactly there)
    and at most 7200 pseudo moves. -/
theorem generate_legal_main {p : Position} {fuel : Nat} {m : Mem} {n mb mo cap : Nat} {blk : Block}
    (hS : p.Shaped) (hK : KingsUnique p) (hw : ∀ i, p.hand p.side i < 256)
    (hrec : ∀ mv ∈ p.pseudoMoves, Position.isPawnDrop mv →
      (p.play mv).inCheck (p.play mv).side → RecSpec fuel (p.play mv))
    (hm : m posBlock = some (encode p)) (ht : TablesIn m) (hf : Fresh m n)
    (h64 : n + 8000 * RB + 5000000000 < 2 ^ 64)
    (hmb : m mb = some blk) (hlen : mo + 5 * cap ≤ blk.length) (hmb0 : mb ≠ 0) (hcap : cap < 2 ^ 64)
    (hpm : posBlock ≠ mb) (hmbt : mb < 8192 ∨ 8196 < mb) :
    ∃ Ms : List Move, Ms.Perm p.pseudoMoves ∧ ∃ s' cb, ExS Gen.prog
      ⟨frameLocals Gen.generate_legal_mut_internal.params [posPtr, .ptr mb mo, .int IntTy.u64 cap, .int IntTy.u8 1],
        m, false⟩ Gen.generate_legal_mut_internal.body
      (.ret (some (.int ⟨64, false⟩ (min (keepBytes p fuel Ms).length cap)))) s' ∧
      Buf s'.mem mb mo cb 0 cap (keepBytes p fuel Ms) ∧ s'.mem posBlock = some (encode p) ∧
      Frame m s'.mem mb cb := by
  obtain ⟨Ms, hperm, hpc⟩ := pseudoC_moves p hw
  refine ⟨Ms, hperm, ?_⟩
  have hMl : Ms.length ≤ 7200 := by rw [hperm.length_eq]; exact pseudoMoves_le_7200 p
  let s0 : State := ⟨frameLocals Gen.generate_legal_mut_internal.params
    [posPtr, .ptr mb mo, .int IntTy.u64 cap, .int IntTy.u8 1], m, false⟩
  have hn0 := hf.2.1
  have hnt : 8196 < n := hf.lt (by rw [ht.g5]; simp)
  have hpn : posBlock < n := hf.lt (by rw [hm]; simp)
  have hmbn : mb < n := hf.lt (by rw [hmb]; simp)
  -- prologue
  obtain ⟨sa, sb, ea, eb, hbP, hfP, l4, l5, lP, roP, frP⟩ := legal_prologue (s := s0) hf (by unfold RB at h64; omega) rfl
  have hmP : sb.mem posBlock = some (encode p) := by rw [frP _ (by decide) (by omega) (by omega)]; exact hm
  have l0 : sb.locals 0 = some posPtr := by rw [lP 0 (by decide) (by decide)]; rfl
  -- pseudo generation
  obtain ⟨sc, n1, ec, lc, roc, hbc, hfc, hn1, frc⟩ := legal_call_pseudo (p := p) l0 l4 l5 hbP hfP
    (by unfold RB at h64; omega) hmP (by omega) (by omega) (by rw [roP])
  rw [hpc] at hbc
  obtain ⟨hrc, PB, hPB, hPBl, hmv⟩ := buf_bridge hbc hMl
  have hn1n : n + 1 < n1 := hfc.lt (by obtain ⟨c, hc, _⟩ := hbc.cnt; rw [hc]; simp)
  have hmc : sc.mem mb = some blk := by
    rw [frc mb hmb0 (by omega) (by omega) (by rw [frP _ hmb0 (by omega) (by omega)]; show m mb ≠ none; rw [hmb]; simp),
      frP _ hmb0 (by omega) (by omega)]; exact hmb
  have hmcP : sc.mem posBlock = some (encode p) := by
    rw [frc _ (by decide) (by omega) (by omega) (by rw [hmP]; simp)]; exact hmP
  have htc : TablesIn sc.mem := (ht.of_eq fun g a b => frP g (by omega) (by omega) (by omega)).of_frame frc
    (Or.inr (by omega)) (Or.inr (by omega))
  -- count = 0
  obtain ⟨sd, ed, hbO, hfd, l6, ld, rod, frd⟩ := legal_count_init (s := sc) hfc (by unfold RB at h64; omega)
    (by rw [roc, roP]) hmc hlen hmb0 hcap
  have kd : ∀ b, b ≠ 0 → b ≠ n1 → sd.mem b = sc.mem b := frd
  -- mover and king safety
  obtain ⟨se, sf, ee, ef, hSb, l7, l8, lf, rof, frf, hff⟩ := legal_safety (s := sd) (p := p) (n := n1 + 1)
    (by rw [ld 0 (by decide), lc, l0]) (by rw [kd _ (by decide) (by omega)]; exact hmcP)
    (htc.of_eq fun g a b => kd g (by omega) (by omega)) hfd (by unfold RB at h64; omega) (by rw [rod, roc, roP])
  have kf : ∀ b, b ≠ 0 → b ≠ n1 → b ≠ n1 + 1 → b ≠ n1 + 2 → sf.mem b = sc.mem b := fun b a c d e => by
    rw [frf b a d e, kd b a c]
  let sg : State := { sf with locals := sf.locals.upd 9 (.int IntTy.u64 0) }
  have eg := legal_index_init sf
  have lg : ∀ x, x < 9 → sg.locals x = sf.locals x := fun x hx => by simp [sg, Locals.upd, show x ≠ 9 by omega]
  have lf' : ∀ x, x < 4 → sf.locals x = s0.locals x := fun x hx => by
    rw [lf x (by omega) (by omega), ld x (by omega), lc, lP x (by omega) (by omega)]
  obtain ⟨CB, hCB, _⟩ := hbc.cnt
  have hMs : ∀ mv ∈ Ms, mv ∈ p.pseudoMoves := fun mv h => hperm.subset h
  have hn1b : n1 ≤ n + 2 + 40000 := hn1
  obtain ⟨s', el, hb', hp', h6', hfrl, f', hf', _⟩ := legal_loop (fuel := fuel) (pb := n) (cntb := n + 1) (Sb := n1 + 1) (mb := mb)
    (mo := mo) (cb := n1) (co := 0) (cap := cap) (PB := PB) (CB := CB) hS hK hMs
    (fun mv h => hrec mv (hMs mv h)) (by omega) hPBl hmv hn0 (by omega) (by omega) (by omega) (by omega)
    ⟨by omega, by omega⟩ ⟨by omega, by omega⟩ ⟨by omega, by omega⟩
    (fun g a b => ⟨by omega, by omega⟩)
    Ms.length 0 sg [] (n1 + 3) (by omega)
    (by rw [lg 0 (by decide), lf' 0 (by decide)]; rfl) (by rw [lg 1 (by decide), lf' 1 (by decide)]; rfl)
    (by rw [lg 2 (by decide), lf' 2 (by decide)]; rfl) (by rw [lg 3 (by decide), lf' 3 (by decide)]; rfl)
    (by rw [lg 4 (by decide), lf 4 (by decide) (by decide), ld 4 (by decide), lc]; exact l4)
    (by rw [lg 5 (by decide), lf 5 (by decide) (by decide), ld 5 (by decide), lc]; exact l5)
    (by rw [lg 6 (by decide), lf 6 (by decide) (by decide)]; exact l6)
    (by rw [lg 7 (by decide)]; exact l7) (by rw [lg 8 (by decide)]; exact l8) (by simp [sg, Locals.upd])
    (by show sf.mem _ = _; rw [kf _ (by decide) (by omega) (by omega) (by omega)]; exact hmcP)
    (by show sf.mem _ = _; rw [kf _ hn0 (by omega) (by omega) (by omega)]; exact hPB)
    hSb
    (by show sf.mem _ = _; rw [kf _ (by omega) (by omega) (by omega) (by omega)]; exact hCB)
    (by show readBytes sf.mem _ _ _ = _; rw [readBytes_of_eq (kf _ (by omega) (by omega) (by omega) (by omega))]
        exact hrc)
    (hbO.of_eq (frf mb hmb0 (by omega) (by omega)) (frf n1 (by omega) (by omega) (by omega)))
    (htc.of_eq fun g a b => kf g (by omega) (by omega) (by omega) (by omega)) hff
    (by unfold RB at h64 ⊢; omega) (by show sf.ro = _; rw [rof, rod, roc, roP])
  simp only [List.nil_append, List.drop_zero] at hb'
  have ev := legal_return (s := s') (h6' ▸ (by rw [lg 6 (by decide), lf 6 (by decide) (by decide)]; exact l6)) hb'
  refine ⟨s', n1, ExS.seq ea (ExS.seq eb (ExS.seq ec (ExS.seq ed (ExS.seq ee (ExS.seq ef
    (ExS.seq (ExS.seq eg (by rw [lp_loop_eq]; exact el)) (ExS.ret ev))))))), hb', hp', ?_⟩
  intro x hx0 hxmb hxcb hxm
  have hxlt : x < n := by
    rcases Nat.lt_or_ge x n with h | h
    · exact h
    · exact absurd (hf.2.2 x h) hxm
  have hxn : x ≠ n := by omega
  have hxn1 : x ≠ n + 1 := by omega
  have hxn1' : x ≠ n1 := by omega
  have hsbx : sb.mem x = m x := frP x hx0 hxn hxn1
  have hsbm : sb.mem x ≠ none := by rw [hsbx]; exact hxm
  have hscx : sc.mem x = sb.mem x := frc x hx0 hxn hxn1 hsbm
  have hsfx : sf.mem x = sc.mem x := kf x hx0 hxn1' (by omega) (by omega)
  have hsfm : sf.mem x ≠ none := by rw [hsfx, hscx, hsbx]; exact hxm
  calc s'.mem x = sf.mem x := hfrl x hx0 hxmb hxcb hsfm
    _ = sc.mem x := hsfx
    _ = sb.mem x := hscx
    _ = m x := hsbx

/-- **C legal moves = spec legal moves (up to order).** With an output
    array of at least 7200 moves, `generate_legal_mut_internal` writes the
    bytes of a reordering of `legalAux (fuel + 1) p` and returns its length. -/
theorem generate_legal_refines {p : Position} {fuel : Nat} {m : Mem} {n mb mo cap : Nat} {blk : Block}
    (hS : p.Shaped) (hK : KingsUnique p) (hw : ∀ i, p.hand p.side i < 256)
    (hcap600 : 7200 ≤ cap)
    (hrec : ∀ mv ∈ p.pseudoMoves, Position.isPawnDrop mv →
      (p.play mv).inCheck (p.play mv).side → RecSpec fuel (p.play mv))
    (hm : m posBlock = some (encode p)) (ht : TablesIn m) (hf : Fresh m n)
    (h64 : n + 8000 * RB + 5000000000 < 2 ^ 64)
    (hmb : m mb = some blk) (hlen : mo + 5 * cap ≤ blk.length) (hmb0 : mb ≠ 0) (hcap : cap < 2 ^ 64)
    (hpm : posBlock ≠ mb) (hmbt : mb < 8192 ∨ 8196 < mb) :
    ∃ K : List (List UInt8), K.Perm ((Position.legalAux (fuel + 1) p).map (moveBytes p)) ∧ ∃ s' cb, ExS Gen.prog
      ⟨frameLocals Gen.generate_legal_mut_internal.params [posPtr, .ptr mb mo, .int IntTy.u64 cap, .int IntTy.u8 1],
        m, false⟩ Gen.generate_legal_mut_internal.body (.ret (some (.int ⟨64, false⟩ K.length))) s' ∧
      Buf s'.mem mb mo cb 0 cap K ∧ s'.mem posBlock = some (encode p) := by
  obtain ⟨Ms, hperm, s', cb, e, hb, hp, _⟩ :=
    generate_legal_main (fuel := fuel) hS hK hw hrec hm ht hf h64 hmb hlen hmb0 hcap hpm hmbt
  have hk : (keepBytes p fuel Ms).length ≤ cap := by
    have : (keepBytes p fuel Ms).length ≤ Ms.length := List.length_filterMap_le _ _
    have := hperm.length_eq
    have := pseudoMoves_le_7200 p
    omega
  refine ⟨keepBytes p fuel Ms, keepBytes_perm p fuel hperm, s', cb, ?_, hb, hp⟩
  rwa [Nat.min_eq_left hk] at e

end Shogi.C.Proofs
