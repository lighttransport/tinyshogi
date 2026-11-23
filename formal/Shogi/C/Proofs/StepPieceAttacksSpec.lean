import Shogi.C.Proofs.StepPieceAttacks
set_option maxHeartbeats 50000000
set_option linter.unusedSimpArgs false
namespace Shogi.C.Proofs
open MiniC Shogi Shogi.C

def rTrue : Stmt := .ret (some (.cast ⟨8, false⟩ (.bin .ne (some ⟨32, true⟩) (.const (.int ⟨32, true⟩ 1)) (.const (.int ⟨32, true⟩ 0)))))
def rFinal : Stmt := .ret (some (.cast ⟨8, false⟩ (.bin .ne (some ⟨32, true⟩) (.const (.int ⟨32, true⟩ 0)) (.const (.int ⟨32, true⟩ 0)))))

-- generated-body projections for exact composition
def g0 : Stmt := Gen.step_piece_attacks.body
def gcond1 : Expr := match g0 with | .seq (.ite c _ _) _ => c | _ => .const .null
def g1 : Stmt := match g0 with | .seq _ r => r | _ => .skip
def gcond2 : Expr := match g1 with | .seq (.ite c _ _) _ => c | _ => .const .null
def g2 : Stmt := match g1 with | .seq _ r => r | _ => .skip
def gcond3 : Expr := match g2 with | .seq (.ite c _ _) _ => c | _ => .const .null
def g3 : Stmt := match g2 with | .seq _ r => r | _ => .skip
def gcond4 : Expr := match g3 with | .seq (.ite c _ _) _ => c | _ => .const .null
def g4 : Stmt := match g3 with | .seq _ r => r | _ => .skip
def gcond5 : Expr := match g4 with | .seq (.ite c _ _) _ => c | _ => .const .null
def g5 : Stmt := match g4 with | .seq _ r => r | _ => .skip
def gcond6 : Expr := match g5 with | .seq (.ite c _ _) _ => c | _ => .const .null
def g6 : Stmt := match g5 with | .seq _ r => r | _ => .skip
def gcond7 : Expr := match g6 with | .seq (.ite c _ _) _ => c | _ => .const .null
def g7 : Stmt := match g6 with | .seq _ r => r | _ => .skip

theorem gc1 : gcond1 = c1 := by rfl
theorem gc2 : gcond2 = c2 := by rfl
theorem gc3 : gcond3 = c3 := by rfl
theorem gc4 : gcond4 = c4 := by rfl
theorem gc5 : gcond5 = c5 := by rfl
theorem gc6 : gcond6 = c6 := by rfl
theorem gc7 : gcond7 = c7 := by rfl

theorem g0_eq : g0 = .seq (.ite gcond1 rTrue .skip) g1 := by rfl
theorem g1_eq : g1 = .seq (.ite gcond2 rTrue .skip) g2 := by rfl
theorem g2_eq : g2 = .seq (.ite gcond3 rTrue .skip) g3 := by rfl
theorem g3_eq : g3 = .seq (.ite gcond4 rTrue .skip) g4 := by rfl
theorem g4_eq : g4 = .seq (.ite gcond5 rTrue .skip) g5 := by rfl
theorem g5_eq : g5 = .seq (.ite gcond6 rTrue .skip) g6 := by rfl
theorem g6_eq : g6 = .seq (.ite gcond7 rTrue .skip) g7 := by rfl
theorem g7_eq : g7 = rFinal := by rfl


theorem eval_ret_true (s : State) :
    EvE Gen.prog s (.cast ⟨8, false⟩ (.bin .ne (some ⟨32, true⟩)
      (.const (.int ⟨32, true⟩ 1)) (.const (.int ⟨32, true⟩ 0)))) (fid15_u8bool true) := by
  exact EvE_of_eval (n := 10) rfl

theorem step_once {s : State} {c : Expr} {vc : Val} {bc : Bool}
    (hc : EvE Gen.prog s c vc) (hbc : truthy vc = .ok bc)
    (ret : Stmt) (hret : ExS Gen.prog s ret (.ret (some (fid15_u8bool true))) s)
    (rest : Stmt) (hrest : ∃ v : Val, ExS Gen.prog s rest (.ret (some v)) s) :
    ∃ v : Val, ExS Gen.prog s (.seq (.ite c ret .skip) rest) (.ret (some v)) s := by
  cases bc
  · obtain ⟨v, hv⟩ := hrest
    exact ⟨v, ExS.seq (ExS.ite hc hbc ExS.skip) hv⟩
  · exact ⟨fid15_u8bool true, ExS.seq_ret (ExS.ite hc hbc hret)⟩

theorem fid15_body (code : Nat) (m : Mem) (hcode : code < 128) (dr dc fwd : Int)
    (hdr : -2147483648 ≤ dr ∧ dr < 2147483648) (hdc : -2147483648 ≤ dc ∧ dc < 2147483648)
    (hfwd : fwd = 1 ∨ fwd = -1)
    (hsdr : -8 ≤ dr ∧ dr ≤ 8) (hsdc : -8 ≤ dc ∧ dc ≤ 8) :
    ∃ v, ExS Gen.prog (s15s m code dr dc fwd) Gen.step_piece_attacks.body
      (.ret (some v)) (s15s m code dr dc fwd) := by
  let s := s15s m code dr dc fwd
  have he1 : EvE Gen.prog s gcond1 (boolVal (sp1 code dr dc fwd)) := by
    rw [gc1]; exact fid15_ev_c1 code m hcode dr dc fwd hdr hdc hfwd hsdr hsdc
  have he2 : EvE Gen.prog s gcond2 (boolVal (sp2 code dr dc fwd)) := by
    rw [gc2]; exact fid15_ev_c2 code m hcode dr dc fwd hdr hdc hfwd hsdr hsdc
  have he3 : EvE Gen.prog s gcond3 (boolVal (sp3 code dr dc fwd)) := by
    rw [gc3]; exact fid15_ev_c3 code m hcode dr dc fwd hdr hdc hfwd hsdr hsdc
  have he4 : EvE Gen.prog s gcond4 (boolVal (sp4 code dr dc fwd)) := by
    rw [gc4]; exact fid15_ev_c4 code m hcode dr dc fwd hdr hdc hfwd hsdr hsdc
  have he5 : EvE Gen.prog s gcond5 (boolVal (sp5 code dr dc fwd)) := by
    rw [gc5]; exact fid15_ev_c5 code m hcode dr dc fwd hdr hdc hfwd hsdr hsdc
  have he6 : EvE Gen.prog s gcond6 (boolVal (sp6 code dr dc fwd)) := by
    rw [gc6]; exact fid15_ev_c6 code m hcode dr dc fwd hdr hdc hfwd hsdr hsdc
  have he7 : EvE Gen.prog s gcond7 (boolVal (sp7 code dr dc fwd)) := by
    rw [gc7]; exact fid15_ev_c7 code m hcode dr dc fwd hdr hdc hfwd hsdr hsdc
  have htrue : ExS Gen.prog s rTrue (.ret (some (fid15_u8bool true))) s := by
    apply ExS.ret
    exact eval_ret_true s
  have hfin : ∃ v, ExS Gen.prog s g7 (.ret (some v)) s := by
    refine ⟨fid15_u8bool false, ?_⟩
    rw [g7_eq]
    exact ExS.ret (EvE_of_eval (n := 10) rfl)

  have hs7 : ∃ v, ExS Gen.prog s (.seq (.ite gcond7 rTrue .skip) g7) (.ret (some v)) s := by
    have hbc : truthy (boolVal (sp7 code dr dc fwd)) = .ok (sp7 code dr dc fwd) := by
      cases sp7 code dr dc fwd <;> rfl
    exact step_once he7 hbc rTrue htrue g7 hfin
  have hs6 : ∃ v, ExS Gen.prog s g6 (.ret (some v)) s := by
    rw [g6_eq]; exact hs7
  have hs6' : ∃ v, ExS Gen.prog s (.seq (.ite gcond6 rTrue .skip) g6) (.ret (some v)) s := by
    have hbc : truthy (boolVal (sp6 code dr dc fwd)) = .ok (sp6 code dr dc fwd) := by
      cases sp6 code dr dc fwd <;> rfl
    exact step_once he6 hbc rTrue htrue g6 hs6
  have hs5 : ∃ v, ExS Gen.prog s g5 (.ret (some v)) s := by
    rw [g5_eq]; exact hs6'
  have hs5' : ∃ v, ExS Gen.prog s (.seq (.ite gcond5 rTrue .skip) g5) (.ret (some v)) s := by
    have hbc : truthy (boolVal (sp5 code dr dc fwd)) = .ok (sp5 code dr dc fwd) := by
      cases sp5 code dr dc fwd <;> rfl
    exact step_once he5 hbc rTrue htrue g5 hs5
  have hs4 : ∃ v, ExS Gen.prog s g4 (.ret (some v)) s := by
    rw [g4_eq]; exact hs5'
  have hs4' : ∃ v, ExS Gen.prog s (.seq (.ite gcond4 rTrue .skip) g4) (.ret (some v)) s := by
    have hbc : truthy (boolVal (sp4 code dr dc fwd)) = .ok (sp4 code dr dc fwd) := by
      cases sp4 code dr dc fwd <;> rfl
    exact step_once he4 hbc rTrue htrue g4 hs4
  have hs3 : ∃ v, ExS Gen.prog s g3 (.ret (some v)) s := by
    rw [g3_eq]; exact hs4'
  have hs3' : ∃ v, ExS Gen.prog s (.seq (.ite gcond3 rTrue .skip) g3) (.ret (some v)) s := by
    have hbc : truthy (boolVal (sp3 code dr dc fwd)) = .ok (sp3 code dr dc fwd) := by
      cases sp3 code dr dc fwd <;> rfl
    exact step_once he3 hbc rTrue htrue g3 hs3
  have hs2 : ∃ v, ExS Gen.prog s g2 (.ret (some v)) s := by
    rw [g2_eq]; exact hs3'
  have hs2' : ∃ v, ExS Gen.prog s (.seq (.ite gcond2 rTrue .skip) g2) (.ret (some v)) s := by
    have hbc : truthy (boolVal (sp2 code dr dc fwd)) = .ok (sp2 code dr dc fwd) := by
      cases sp2 code dr dc fwd <;> rfl
    exact step_once he2 hbc rTrue htrue g2 hs2
  have hs1 : ∃ v, ExS Gen.prog s g1 (.ret (some v)) s := by
    rw [g1_eq]; exact hs2'
  have hs1' : ∃ v, ExS Gen.prog s (.seq (.ite gcond1 rTrue .skip) g1) (.ret (some v)) s := by
    have hbc : truthy (boolVal (sp1 code dr dc fwd)) = .ok (sp1 code dr dc fwd) := by
      cases sp1 code dr dc fwd <;> rfl
    exact step_once he1 hbc rTrue htrue g1 hs1
  change ∃ v, ExS Gen.prog s g0 (.ret (some v)) s
  rw [g0_eq]
  exact hs1'

theorem ofCode_eq_code {code : Nat} {t : PieceType} (hcode : code < 128)
    (h : PieceType.ofCode code = some t) : code = t.code := by
  have hc : code = 0 ∨ code = 1 ∨ code = 2 ∨ code = 3 ∨ code = 4 ∨ code = 5 ∨ code = 6 ∨ code = 7 ∨ code = 8 ∨ code = 9 ∨ code = 10 ∨ code = 11 ∨ code = 12 ∨ code = 13 ∨ code = 14 ∨ code = 15 ∨ code = 16 ∨ code = 17 ∨ code = 18 ∨ code = 19 ∨ code = 20 ∨ code = 21 ∨ code = 22 ∨ code = 23 ∨ code = 24 ∨ code = 25 ∨ code = 26 ∨ code = 27 ∨ code = 28 ∨ code = 29 ∨ code = 30 ∨ code = 31 ∨ code = 32 ∨ code = 33 ∨ code = 34 ∨ code = 35 ∨ code = 36 ∨ code = 37 ∨ code = 38 ∨ code = 39 ∨ code = 40 ∨ code = 41 ∨ code = 42 ∨ code = 43 ∨ code = 44 ∨ code = 45 ∨ code = 46 ∨ code = 47 ∨ code = 48 ∨ code = 49 ∨ code = 50 ∨ code = 51 ∨ code = 52 ∨ code = 53 ∨ code = 54 ∨ code = 55 ∨ code = 56 ∨ code = 57 ∨ code = 58 ∨ code = 59 ∨ code = 60 ∨ code = 61 ∨ code = 62 ∨ code = 63 ∨ code = 64 ∨ code = 65 ∨ code = 66 ∨ code = 67 ∨ code = 68 ∨ code = 69 ∨ code = 70 ∨ code = 71 ∨ code = 72 ∨ code = 73 ∨ code = 74 ∨ code = 75 ∨ code = 76 ∨ code = 77 ∨ code = 78 ∨ code = 79 ∨ code = 80 ∨ code = 81 ∨ code = 82 ∨ code = 83 ∨ code = 84 ∨ code = 85 ∨ code = 86 ∨ code = 87 ∨ code = 88 ∨ code = 89 ∨ code = 90 ∨ code = 91 ∨ code = 92 ∨ code = 93 ∨ code = 94 ∨ code = 95 ∨ code = 96 ∨ code = 97 ∨ code = 98 ∨ code = 99 ∨ code = 100 ∨ code = 101 ∨ code = 102 ∨ code = 103 ∨ code = 104 ∨ code = 105 ∨ code = 106 ∨ code = 107 ∨ code = 108 ∨ code = 109 ∨ code = 110 ∨ code = 111 ∨ code = 112 ∨ code = 113 ∨ code = 114 ∨ code = 115 ∨ code = 116 ∨ code = 117 ∨ code = 118 ∨ code = 119 ∨ code = 120 ∨ code = 121 ∨ code = 122 ∨ code = 123 ∨ code = 124 ∨ code = 125 ∨ code = 126 ∨ code = 127 := by omega
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals cases t <;> simp [PieceType.ofCode, PieceType.code] at h ⊢

theorem cformula_spec (code : Nat) (hcode : code < 128) (dr dc fwd : Int)
    (hfwd : fwd = 1 ∨ fwd = -1)
    (hsdr : -8 ≤ dr ∧ dr ≤ 8) (hsdc : -8 ≤ dc ∧ dc ≤ 8) :
    (cformula code dr dc fwd = true) ↔
      ∃ t : PieceType, PieceType.ofCode code = some t ∧ (dr, dc) ∈ stepOffsets fwd t := by
  rcases h : PieceType.ofCode code with _ | t
  · constructor
    · intro hcf
      have h1 : code ≠ 1 := by intro he; subst code; simp [PieceType.ofCode] at h
      have h3 : code ≠ 3 := by intro he; subst code; simp [PieceType.ofCode] at h
      have h4 : code ≠ 4 := by intro he; subst code; simp [PieceType.ofCode] at h
      have h5 : code ≠ 5 := by intro he; subst code; simp [PieceType.ofCode] at h
      have h9 : code ≠ 9 := by intro he; subst code; simp [PieceType.ofCode] at h
      have h10 : code ≠ 10 := by intro he; subst code; simp [PieceType.ofCode] at h
      have h11 : code ≠ 11 := by intro he; subst code; simp [PieceType.ofCode] at h
      have h12 : code ≠ 12 := by intro he; subst code; simp [PieceType.ofCode] at h
      have h8 : code ≠ 8 := by intro he; subst code; simp [PieceType.ofCode] at h
      have h13 : code ≠ 13 := by intro he; subst code; simp [PieceType.ofCode] at h
      have h14 : code ≠ 14 := by intro he; subst code; simp [PieceType.ofCode] at h
      have hnot : code ≠ 1 ∧ code ≠ 3 ∧ code ≠ 4 ∧ code ≠ 5 ∧ code ≠ 9 ∧ code ≠ 10 ∧ code ≠ 11 ∧ code ≠ 12 ∧ code ≠ 8 ∧ code ≠ 13 ∧ code ≠ 14 := by
        exact ⟨h1, h3, h4, h5, h9, h10, h11, h12, h8, h13, h14⟩
      simp [cformula, sp1, sp2, sp3, sp4, sp5, sp6, sp7, hnot] at hcf
    · rintro ⟨_, h', _⟩
      cases h'
  · have hc := ofCode_eq_code hcode h
    subst code
    cases t <;> simp [PieceType.code, cformula, sp1, sp2, sp3, sp4, sp5, sp6, sp7, stepOffsets] <;>
      rcases hfwd with rfl | rfl <;> omega


theorem step_once2 {s : State} {c : Expr} {vc : Val} {bc rb : Bool}
    (hc : EvE Gen.prog s c vc) (hbc : truthy vc = .ok bc)
    (hret : ExS Gen.prog s rTrue (.ret (some (fid15_u8bool true))) s)
    (rest : Stmt)
    (hrest : ∃ v, ExS Gen.prog s rest (.ret (some v)) s ∧ v = fid15_u8bool rb) :
    ∃ v, ExS Gen.prog s (.seq (.ite c rTrue .skip) rest) (.ret (some v)) s ∧ v = fid15_u8bool (bc || rb) := by
  cases bc
  · obtain ⟨v, hv, hve⟩ := hrest
    exact ⟨v, ExS.seq (ExS.ite hc hbc ExS.skip) hv, by simpa using hve⟩
  · exact ⟨fid15_u8bool true, ExS.seq_ret (ExS.ite hc hbc hret), rfl⟩

theorem fid15_body_eq (code : Nat) (m : Mem) (hcode : code < 128) (dr dc fwd : Int)
    (hdr : -2147483648 ≤ dr ∧ dr < 2147483648) (hdc : -2147483648 ≤ dc ∧ dc < 2147483648)
    (hfwd : fwd = 1 ∨ fwd = -1)
    (hsdr : -8 ≤ dr ∧ dr ≤ 8) (hsdc : -8 ≤ dc ∧ dc ≤ 8) :
    ∃ v, ExS Gen.prog (s15s m code dr dc fwd) Gen.step_piece_attacks.body
      (.ret (some v)) (s15s m code dr dc fwd) ∧ v = fid15_u8bool (cformula code dr dc fwd) := by
  let s := s15s m code dr dc fwd
  have he1 : EvE Gen.prog s gcond1 (boolVal (sp1 code dr dc fwd)) := by rw [gc1]; exact fid15_ev_c1 code m hcode dr dc fwd hdr hdc hfwd hsdr hsdc
  have he2 : EvE Gen.prog s gcond2 (boolVal (sp2 code dr dc fwd)) := by rw [gc2]; exact fid15_ev_c2 code m hcode dr dc fwd hdr hdc hfwd hsdr hsdc
  have he3 : EvE Gen.prog s gcond3 (boolVal (sp3 code dr dc fwd)) := by rw [gc3]; exact fid15_ev_c3 code m hcode dr dc fwd hdr hdc hfwd hsdr hsdc
  have he4 : EvE Gen.prog s gcond4 (boolVal (sp4 code dr dc fwd)) := by rw [gc4]; exact fid15_ev_c4 code m hcode dr dc fwd hdr hdc hfwd hsdr hsdc
  have he5 : EvE Gen.prog s gcond5 (boolVal (sp5 code dr dc fwd)) := by rw [gc5]; exact fid15_ev_c5 code m hcode dr dc fwd hdr hdc hfwd hsdr hsdc
  have he6 : EvE Gen.prog s gcond6 (boolVal (sp6 code dr dc fwd)) := by rw [gc6]; exact fid15_ev_c6 code m hcode dr dc fwd hdr hdc hfwd hsdr hsdc
  have he7 : EvE Gen.prog s gcond7 (boolVal (sp7 code dr dc fwd)) := by rw [gc7]; exact fid15_ev_c7 code m hcode dr dc fwd hdr hdc hfwd hsdr hsdc
  have htrue : ExS Gen.prog s rTrue (.ret (some (fid15_u8bool true))) s := by
    apply ExS.ret; exact eval_ret_true s
  have hfin : ∃ v, ExS Gen.prog s g7 (.ret (some v)) s ∧ v = fid15_u8bool false := by
    refine ⟨fid15_u8bool false, ?_, rfl⟩
    rw [g7_eq]
    exact ExS.ret (EvE_of_eval (n := 10) rfl)

  have hs7 : ∃ v, ExS Gen.prog s (.seq (.ite gcond7 rTrue .skip) g7) (.ret (some v)) s ∧
      v = fid15_u8bool (sp7 code dr dc fwd || false) := by
    have hbc : truthy (boolVal (sp7 code dr dc fwd)) = .ok (sp7 code dr dc fwd) := by cases sp7 code dr dc fwd <;> rfl
    exact step_once2 he7 hbc htrue g7 hfin
  have hs6 : ∃ v, ExS Gen.prog s g6 (.ret (some v)) s ∧ v = fid15_u8bool (sp7 code dr dc fwd || false) := by
    rw [g6_eq]; exact hs7
  have hs6' : ∃ v, ExS Gen.prog s (.seq (.ite gcond6 rTrue .skip) g6) (.ret (some v)) s ∧
      v = fid15_u8bool (sp6 code dr dc fwd || (sp7 code dr dc fwd || false)) := by
    have hbc : truthy (boolVal (sp6 code dr dc fwd)) = .ok (sp6 code dr dc fwd) := by cases sp6 code dr dc fwd <;> rfl
    exact step_once2 he6 hbc htrue g6 hs6
  have hs5 : ∃ v, ExS Gen.prog s g5 (.ret (some v)) s ∧ v = fid15_u8bool (sp6 code dr dc fwd || (sp7 code dr dc fwd || false)) := by
    rw [g5_eq]; exact hs6'
  have hs5' : ∃ v, ExS Gen.prog s (.seq (.ite gcond5 rTrue .skip) g5) (.ret (some v)) s ∧
      v = fid15_u8bool (sp5 code dr dc fwd || (sp6 code dr dc fwd || (sp7 code dr dc fwd || false))) := by
    have hbc : truthy (boolVal (sp5 code dr dc fwd)) = .ok (sp5 code dr dc fwd) := by cases sp5 code dr dc fwd <;> rfl
    exact step_once2 he5 hbc htrue g5 hs5
  have hs4 : ∃ v, ExS Gen.prog s g4 (.ret (some v)) s ∧ v = fid15_u8bool (sp5 code dr dc fwd || (sp6 code dr dc fwd || (sp7 code dr dc fwd || false))) := by
    rw [g4_eq]; exact hs5'
  have hs4' : ∃ v, ExS Gen.prog s (.seq (.ite gcond4 rTrue .skip) g4) (.ret (some v)) s ∧
      v = fid15_u8bool (sp4 code dr dc fwd || (sp5 code dr dc fwd || (sp6 code dr dc fwd || (sp7 code dr dc fwd || false)))) := by
    have hbc : truthy (boolVal (sp4 code dr dc fwd)) = .ok (sp4 code dr dc fwd) := by cases sp4 code dr dc fwd <;> rfl
    exact step_once2 he4 hbc htrue g4 hs4
  have hs3 : ∃ v, ExS Gen.prog s g3 (.ret (some v)) s ∧ v = fid15_u8bool (sp4 code dr dc fwd || (sp5 code dr dc fwd || (sp6 code dr dc fwd || (sp7 code dr dc fwd || false)))) := by
    rw [g3_eq]; exact hs4'
  have hs3' : ∃ v, ExS Gen.prog s (.seq (.ite gcond3 rTrue .skip) g3) (.ret (some v)) s ∧
      v = fid15_u8bool (sp3 code dr dc fwd || (sp4 code dr dc fwd || (sp5 code dr dc fwd || (sp6 code dr dc fwd || (sp7 code dr dc fwd || false))))) := by
    have hbc : truthy (boolVal (sp3 code dr dc fwd)) = .ok (sp3 code dr dc fwd) := by cases sp3 code dr dc fwd <;> rfl
    exact step_once2 he3 hbc htrue g3 hs3
  have hs2 : ∃ v, ExS Gen.prog s g2 (.ret (some v)) s ∧ v = fid15_u8bool (sp3 code dr dc fwd || (sp4 code dr dc fwd || (sp5 code dr dc fwd || (sp6 code dr dc fwd || (sp7 code dr dc fwd || false))))) := by
    rw [g2_eq]; exact hs3'
  have hs2' : ∃ v, ExS Gen.prog s (.seq (.ite gcond2 rTrue .skip) g2) (.ret (some v)) s ∧
      v = fid15_u8bool (sp2 code dr dc fwd || (sp3 code dr dc fwd || (sp4 code dr dc fwd || (sp5 code dr dc fwd || (sp6 code dr dc fwd || (sp7 code dr dc fwd || false)))))) := by
    have hbc : truthy (boolVal (sp2 code dr dc fwd)) = .ok (sp2 code dr dc fwd) := by cases sp2 code dr dc fwd <;> rfl
    exact step_once2 he2 hbc htrue g2 hs2
  have hs1 : ∃ v, ExS Gen.prog s g1 (.ret (some v)) s ∧ v = fid15_u8bool (sp2 code dr dc fwd || (sp3 code dr dc fwd || (sp4 code dr dc fwd || (sp5 code dr dc fwd || (sp6 code dr dc fwd || (sp7 code dr dc fwd || false)))))) := by
    rw [g1_eq]; exact hs2'
  have hs1' : ∃ v, ExS Gen.prog s (.seq (.ite gcond1 rTrue .skip) g1) (.ret (some v)) s ∧
      v = fid15_u8bool (sp1 code dr dc fwd || (sp2 code dr dc fwd || (sp3 code dr dc fwd || (sp4 code dr dc fwd || (sp5 code dr dc fwd || (sp6 code dr dc fwd || (sp7 code dr dc fwd || false))))))) := by
    have hbc : truthy (boolVal (sp1 code dr dc fwd)) = .ok (sp1 code dr dc fwd) := by cases sp1 code dr dc fwd <;> rfl
    exact step_once2 he1 hbc htrue g1 hs1
  change ∃ v, ExS Gen.prog s g0 (.ret (some v)) s ∧ v = fid15_u8bool (cformula code dr dc fwd)
  rw [g0_eq]
  simpa only [cformula, Bool.or_false, Bool.or_assoc] using hs1'


theorem step_piece_attacks_spec (code : Nat) (m : Mem) (hcode : code < 128)
    (dr dc fwd : Int) (hdr : -2147483648 ≤ dr ∧ dr < 2147483648)
    (hdc : -2147483648 ≤ dc ∧ dc < 2147483648) (hfwd : fwd = 1 ∨ fwd = -1)
    (hsdr : -8 ≤ dr ∧ dr ≤ 8) (hsdc : -8 ≤ dc ∧ dc ≤ 8) :
    ∃ sf v, ExS Gen.prog
      (s15s m code dr dc fwd)
      Gen.step_piece_attacks.body (.ret (some v)) sf ∧
      (v = fid15_u8bool true ↔ ∃ t : PieceType, PieceType.ofCode code = some t ∧
        (dr, dc) ∈ stepOffsets fwd t) := by
  obtain ⟨v, hexs, hv⟩ := fid15_body_eq code m hcode dr dc fwd hdr hdc hfwd hsdr hsdc
  refine ⟨?_, v, ?_, ?_⟩
  · exact (s15s m code dr dc fwd)
  · simpa [s15s, frameLocals, Gen.step_piece_attacks] using hexs
  · rw [hv, fid15_u8bool]
    constructor
    · intro h
      have hc : cformula code dr dc fwd = true := by
        by_cases hcf : cformula code dr dc fwd = true
        · exact hcf
        · cases hcf' : cformula code dr dc fwd <;> simp [hcf', fid15_u8bool] at h ⊢
      exact (cformula_spec code hcode dr dc fwd hfwd hsdr hsdc).1 hc
    · intro h
      have hc := (cformula_spec code hcode dr dc fwd hfwd hsdr hsdc).2 h
      simp [fid15_u8bool, hc]

end Shogi.C.Proofs
