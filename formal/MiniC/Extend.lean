/-
  Extension invariance of the MiniC semantics (tinyshogi addition).

  If every live block of a memory `m` is a prefix of the corresponding block
  of `m'`, then any successful run on `m` also succeeds on `m'` with the same
  outcome, return value and locals. This lets the generator refinements,
  proved for the 114-byte `encode p` prefix, be lifted to a full
  41088-byte `ShogiPosition` block whose first 114 bytes agree.

  Only the success-lifting direction holds: a read that stops at the end of a
  short block may succeed once bytes are appended. The translated rules core
  uses no `strlen`/`memcmp`, so those two primitives are not needed here.
-/
import MiniC.Logic
import MiniC.Fuel

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

namespace MiniC

/-- `m' extends m`: each block of `m` is a prefix of the matching block of
    `m'`. Blocks absent from `m` are absent from `m'` too (so `alloc` hands
    out the same fresh block number). -/
def MemExt (m m' : Mem) : Prop :=
  ∀ b, (m b = none ∧ m' b = none) ∨ ∃ (B T : Block), m b = some B ∧ m' b = some (B ++ T)

/-- Related states: identical locals and read-only flag, extended memory. -/
def StateExt (s s' : State) : Prop :=
  s.locals = s'.locals ∧ s.ro = s'.ro ∧ MemExt s.mem s'.mem

namespace MemExt

theorem of_some {m m' b B} (h : MemExt m m') (hb : m b = some B) :
    ∃ T, m' b = some (B ++ T) := by
  rcases h b with hnone | hex
  · cases hnone.1.symm.trans hb
  · rcases hex with ⟨B', T, hb', hb''⟩
    have hBB : B' = B := Option.some.inj (hb'.symm.trans hb)
    subst hBB
    exact ⟨T, hb''⟩

theorem of_none {m m' b} (h : MemExt m m') (hb : m b = none) : m' b = none := by
  rcases h b with hnone | hex
  · exact hnone.2
  · rcases hex with ⟨B, T, hb', _⟩
    cases hb'.symm.trans hb

theorem refl (m : Mem) : MemExt m m := by
  intro b
  cases hmb : m b with
  | none => left; exact ⟨rfl, rfl⟩
  | some B => right; exact ⟨B, [], rfl, by simp⟩

end MemExt

theorem readBytes_ext {m m' b o n} (h : MemExt m m') {bs : List UInt8}
    (hk : readBytes m b o n = .ok bs) : readBytes m' b o n = .ok bs := by
  cases hmb : m b with
  | none => simp [readBytes, hmb] at hk
  | some B =>
      obtain ⟨T, hmb'⟩ := MemExt.of_some h hmb
      simp only [readBytes, hmb, hmb'] at hk ⊢
      split at hk
      · rename_i hle
        have hle' : o + n ≤ (B ++ T).length := by simp; omega
        rw [if_pos hle']
        rw [List.drop_append_of_le_length (show o ≤ B.length by omega)]
        rw [List.take_append_of_le_length (show n ≤ (B.drop o).length by simp; omega)]
        simpa using hk
      · simp at hk

theorem writeBytes_ext {m m' b o bs} (h : MemExt m m') {m1}
    (hk : writeBytes m b o bs = .ok m1) :
    ∃ m1', writeBytes m' b o bs = .ok m1' ∧ MemExt m1 m1' := by
  cases hmb : m b with
  | none => simp [writeBytes, hmb] at hk
  | some B =>
      obtain ⟨T, hmb'⟩ := MemExt.of_some h hmb
      simp only [writeBytes, hmb, hmb'] at hk ⊢
      split at hk
      · rename_i hle
        have hle' : o + bs.length ≤ (B ++ T).length := by simp; omega
        rw [if_pos hle']
        rw [List.take_append_of_le_length (show o ≤ B.length by omega)]
        rw [List.drop_append_of_le_length (show o + bs.length ≤ B.length by omega)]
        let B1 := B.take o ++ bs ++ B.drop (o + bs.length)
        have hm1 : m1 = m.upd b B1 := by simpa [B1] using hk.symm
        subst m1
        refine ⟨m'.upd b (B1 ++ T), by simp [B1, List.append_assoc], ?_⟩
        intro x
        by_cases hx : x = b
        · subst x
          right
          refine ⟨B1, T, ?_, by simp [Mem.upd]⟩
          simp [Mem.upd, hmb, hmb', B1, List.append_assoc]
        · simpa [Mem.upd, hx] using h x
      · simp at hk

theorem load_ext {m m' ty p} (h : MemExt m m') {v} (hk : load m ty p = .ok v) :
    load m' ty p = .ok v := by
  cases p with
  | ptr b o =>
      simp only [load] at hk ⊢
      cases hb : readBytes m b o ty.size with
      | ok bs =>
          have hb' := readBytes_ext h hb
          cases ty <;> simp [hb, hb'] at hk ⊢ <;> exact hk
      | ub => simp [hb] at hk
      | timeout => simp [hb] at hk
  | _ => simp [load] at hk

theorem store_ext {m m' ty p v} (h : MemExt m m') {m1}
    (hk : store m ty p v = .ok m1) :
    ∃ m1', store m' ty p v = .ok m1' ∧ MemExt m1 m1' := by
  cases p with
  | ptr b o =>
      cases ty with
      | int t =>
          cases v with
          | int t' n =>
              by_cases ht : t = t'
              · subst t'
                simp only [store, if_true] at hk ⊢
                exact writeBytes_ext h hk
              · simp [store, ht] at hk
          | _ => simp [store] at hk
      | f64 =>
          cases v with
          | f64 n => simpa [store] using writeBytes_ext h hk
          | _ => simp [store] at hk
      | ptr =>
          cases v with
          | ptr b' o' => simpa [store] using writeBytes_ext h hk
          | int t' n' => simpa [store, ptrPack] using writeBytes_ext h hk
          | f64 n' => simpa [store, ptrPack] using writeBytes_ext h hk
          | null => simpa [store, ptrPack] using writeBytes_ext h hk
  | _ => simp [store] at hk

theorem ptrAddN_ext {m m' p k} (h : MemExt m m') {q} (hk : ptrAddN m p k = .ok q) :
    ptrAddN m' p k = .ok q := by
  cases p with
  | ptr b o =>
      cases hmb : m b with
      | none => simp [ptrAddN, hmb] at hk
      | some B =>
          obtain ⟨T, hmb'⟩ := MemExt.of_some h hmb
          simp only [ptrAddN, hmb, hmb'] at hk ⊢
          split at hk
          · rename_i hle
            rw [if_pos (show o + k ≤ (B ++ T).length by simp; omega)]
            simpa using hk
          · simp at hk
  | _ => simp [ptrAddN] at hk

theorem ptrAdd_ext {m m' p d} (h : MemExt m m') {q} (hk : ptrAdd m p d = .ok q) :
    ptrAdd m' p d = .ok q := by
  cases p with
  | ptr b o =>
      cases hmb : m b with
      | none => simp [ptrAdd, hmb] at hk
      | some B =>
          obtain ⟨T, hmb'⟩ := MemExt.of_some h hmb
          simp only [ptrAdd, hmb, hmb'] at hk ⊢
          split at hk
          · rename_i hle
            rcases hle with ⟨hlo, hhi⟩
            have hle' : (o : Int) + d ≤ ((B ++ T).length : Int) := by
              have hlen : (B ++ T).length = B.length + T.length := by simp
              omega
            rw [if_pos ⟨hlo, hle'⟩]
            simpa using hk
          · simp at hk
  | _ => simp [ptrAdd] at hk


theorem commonPrefix_append (A TA B TB : Block) {oa ob n : Nat}
    (hA : oa + n ≤ A.length) (hB : ob + n ≤ B.length) :
    commonPrefix (A ++ TA) oa (B ++ TB) ob n = commonPrefix A oa B ob n := by
  induction n generalizing oa ob with
  | zero => rfl
  | succ n ih =>
      have hoa : oa < A.length := by omega
      have hob : ob < B.length := by omega
      simp only [commonPrefix]
      rw [List.getElem?_append_left hoa, List.getElem?_append_left hob]
      cases ha : A[oa]? with
      | none => simp [ha]
      | some x =>
          cases hb : B[ob]? with
          | none => simp [hb]
          | some y =>
              by_cases hxy : x = y
              · simp [hxy, ih (oa := oa + 1) (ob := ob + 1) (by omega) (by omega)]
              · simp [hxy]

theorem memcmpAt_ext {m m' pa pb n} (h : MemExt m m') {v}
    (hk : memcmpAt m pa pb n = .ok v) : memcmpAt m' pa pb n = .ok v := by
  cases pa with
  | ptr ba oa =>
    cases pb with
    | ptr bb ob =>
      cases hma : m ba with
      | none => simp [memcmpAt, hma] at hk
      | some A =>
        obtain ⟨TA, hma'⟩ := MemExt.of_some h hma
        cases hmb : m bb with
        | none => simp [memcmpAt, hmb] at hk
        | some B =>
          obtain ⟨TB, hmb'⟩ := MemExt.of_some h hmb
          simp only [memcmpAt, hma, hmb, hma', hmb'] at hk ⊢
          split at hk
          · rename_i hle
            have hA : oa + n ≤ A.length := by omega
            have hB : ob + n ≤ B.length := by omega
            rw [if_pos (show oa + n ≤ (A ++ TA).length ∧ ob + n ≤ (B ++ TB).length by simp; omega)]
            rw [commonPrefix_append A TA B TB hA hB]
            split at hk
            · rename_i hklt
              simp only [hklt, ↓reduceDIte]
              have hidxA : oa + commonPrefix A oa B ob n < A.length := by omega
              have hidxB : ob + commonPrefix A oa B ob n < B.length := by omega
              rw [List.getElem?_append_left hidxA, List.getElem?_append_left hidxB]
              simpa using hk
            · rename_i hkge
              simp only [hkge, ↓reduceDIte]
              simpa using hk
          · simp at hk
    | _ => simp [memcmpAt] at hk
  | _ => simp [memcmpAt] at hk

theorem strlenFrom_ext (B T : Block) (o : Nat) {e : Nat} (hk : strlenFrom B o = some e) :
    strlenFrom (B ++ T) o = some e := by
  generalize hm : B.length - o = m
  revert B o
  induction m using Nat.strongRecOn with
  | ind m ih =>
      intro B o hk hm
      by_cases ho : o < B.length
      · rw [strlenFrom.eq_1] at hk
        rw [dif_pos ho] at hk
        rw [strlenFrom.eq_1]
        have ho' : o < (B ++ T).length := by simp; omega
        rw [dif_pos ho']
        by_cases hz : B[o] = 0
        · rw [if_pos hz] at hk
          have hz' : (B ++ T)[o] = 0 := by simpa [List.getElem_append_left ho] using hz
          rw [if_pos hz']
          exact hk
        · rw [if_neg hz] at hk
          have hz' : (B ++ T)[o] ≠ 0 := by simpa [List.getElem_append_left ho] using hz
          rw [if_neg hz']
          exact ih (B.length - (o + 1)) (by omega) B (o + 1) hk rfl
      · rw [strlenFrom.eq_1] at hk
        rw [dif_neg ho] at hk
        cases hk

theorem strlenAt_ext {m m' p} (h : MemExt m m') {v} (hk : strlenAt m p = .ok v) :
    strlenAt m' p = .ok v := by
  cases p with
  | ptr b o =>
      cases hmb : m b with
      | none => simp [strlenAt, hmb] at hk
      | some B =>
          obtain ⟨T, hmb'⟩ := MemExt.of_some h hmb
          simp only [strlenAt, hmb, hmb'] at hk ⊢
          cases hs : strlenFrom B o with
          | none => simp [hs] at hk
          | some e =>
              have hs' := strlenFrom_ext B T o hs
              simp [hs, hs'] at hk ⊢
              exact hk
  | _ => simp [strlenAt] at hk


section
variable (p : Prog)

theorem ext_step : ∀ n : Nat,
    (∀ s s' e v, StateExt s s' → evalExpr p n s e = .ok v → evalExpr p n s' e = .ok v) ∧
    (∀ s s' es vs, StateExt s s' → evalArgs p n s es = .ok vs → evalArgs p n s' es = .ok vs) ∧
    (∀ s s' st o s1, StateExt s s' → execStmt p n s st = .ok (o, s1) →
      ∃ s1', execStmt p n s' st = .ok (o, s1') ∧ StateExt s1 s1') := by
  intro n
  induction n with
  | zero =>
      refine ⟨?_, ?_, ?_⟩ <;> intro <;> simp [evalExpr, evalArgs, execStmt] at *
  | succ n ih =>
      obtain ⟨ihe, iha, ihs⟩ := ih
      refine ⟨?expr, ?args, ?stmt⟩
      · intro s s' e v hrel hk
        cases e with
        | const => simpa [evalExpr] using hk
        | var i =>
            simp [evalExpr] at hk ⊢
            simpa [← hrel.1] using hk
        | load ty a =>
            cases ha : evalExpr p n s a with
            | ok pa =>
                have ha' := ihe s s' a pa hrel ha
                simp [evalExpr, ha] at hk
                have hl := load_ext hrel.2.2 hk
                simp [evalExpr, ha', hl]
            | ub => simp [evalExpr, ha] at hk
            | timeout => simp [evalExpr, ha] at hk
        | index base idx elem =>
            cases hb : evalExpr p n s base with
            | ok pb =>
              cases hi : evalExpr p n s idx with
              | ok vi =>
                have hb' := ihe s s' base pb hrel hb
                have hi' := ihe s s' idx vi hrel hi
                simp [evalExpr, hb, hi] at hk
                cases vi with
                | int t m =>
                    simp at hk
                    have hq : (if t.signed then ptrAdd s'.mem pb (t.toInt m * (elem : Int))
                               else ptrAddN s'.mem pb (m * elem)) = .ok v := by
                      by_cases hts : t.signed
                      · have hq0 := ptrAdd_ext hrel.2.2 (by simpa [hts] using hk)
                        simpa [hts] using hq0
                      · have hq0 := ptrAddN_ext hrel.2.2 (by simpa [hts] using hk)
                        simpa [hts] using hq0
                    simp [evalExpr, hb', hi', hq]
                | _ => simp at hk
              | ub => simp [evalExpr, hb, hi] at hk
              | timeout => simp [evalExpr, hb, hi] at hk
            | ub => simp [evalExpr, hb] at hk
            | timeout => simp [evalExpr, hb] at hk
        | field base off =>
            cases hb : evalExpr p n s base with
            | ok pb =>
              have hb' := ihe s s' base pb hrel hb
              simp [evalExpr, hb] at hk
              have hq := ptrAddN_ext hrel.2.2 hk
              simp [evalExpr, hb', hq]
            | ub => simp [evalExpr, hb] at hk
            | timeout => simp [evalExpr, hb] at hk
        | bin op t a b =>
            cases ha : evalExpr p n s a with
            | ok va =>
              cases hb : evalExpr p n s b with
              | ok vb =>
                have ha' := ihe s s' a va hrel ha
                have hb' := ihe s s' b vb hrel hb
                simp [evalExpr, ha, hb] at hk
                simpa [evalExpr, ha', hb'] using hk
              | ub => simp [evalExpr, ha, hb] at hk
              | timeout => simp [evalExpr, ha, hb] at hk
            | ub => simp [evalExpr, ha] at hk
            | timeout => simp [evalExpr, ha] at hk
        | un op t a =>
            cases ha : evalExpr p n s a with
            | ok va =>
                have ha' := ihe s s' a va hrel ha
                simp [evalExpr, ha] at hk
                simpa [evalExpr, ha'] using hk
            | ub => simp [evalExpr, ha] at hk
            | timeout => simp [evalExpr, ha] at hk
        | cast t a =>
            cases ha : evalExpr p n s a with
            | ok va =>
                have ha' := ihe s s' a va hrel ha
                simp [evalExpr, ha] at hk
                simpa [evalExpr, ha'] using hk
            | ub => simp [evalExpr, ha] at hk
            | timeout => simp [evalExpr, ha] at hk
        | land a b =>
            cases ha : evalExpr p n s a with
            | ok va =>
                have ha' := ihe s s' a va hrel ha
                cases hta : truthy va with
                | ok ba =>
                    cases ba with
                    | false =>
                        simp [evalExpr, ha, hta] at hk
                        simpa [evalExpr, ha', hta] using hk
                    | true =>
                        cases hb : evalExpr p n s b with
                        | ok vb =>
                            have hb' := ihe s s' b vb hrel hb
                            cases htb : truthy vb with
                            | ok bb =>
                                simp [evalExpr, ha, hta, hb, htb] at hk
                                simpa [evalExpr, ha', hta, hb', htb] using hk
                            | ub => simp [evalExpr, ha, hta, hb, htb] at hk
                            | timeout => simp [evalExpr, ha, hta, hb, htb] at hk
                        | ub => simp [evalExpr, ha, hta, hb] at hk
                        | timeout => simp [evalExpr, ha, hta, hb] at hk
                | ub => simp [evalExpr, ha, hta] at hk
                | timeout => simp [evalExpr, ha, hta] at hk
            | ub => simp [evalExpr, ha] at hk
            | timeout => simp [evalExpr, ha] at hk
        | lor a b =>
            cases ha : evalExpr p n s a with
            | ok va =>
                have ha' := ihe s s' a va hrel ha
                cases hta : truthy va with
                | ok ba =>
                    cases ba with
                    | true =>
                        simp [evalExpr, ha, hta] at hk
                        simpa [evalExpr, ha', hta] using hk
                    | false =>
                        cases hb : evalExpr p n s b with
                        | ok vb =>
                            have hb' := ihe s s' b vb hrel hb
                            cases htb : truthy vb with
                            | ok bb =>
                                simp [evalExpr, ha, hta, hb, htb] at hk
                                simpa [evalExpr, ha', hta, hb', htb] using hk
                            | ub => simp [evalExpr, ha, hta, hb, htb] at hk
                            | timeout => simp [evalExpr, ha, hta, hb, htb] at hk
                        | ub => simp [evalExpr, ha, hta, hb] at hk
                        | timeout => simp [evalExpr, ha, hta, hb] at hk
                | ub => simp [evalExpr, ha, hta] at hk
                | timeout => simp [evalExpr, ha, hta] at hk
            | ub => simp [evalExpr, ha] at hk
            | timeout => simp [evalExpr, ha] at hk
        | cond c a b =>
            cases hc : evalExpr p n s c with
            | ok vc =>
                have hc' := ihe s s' c vc hrel hc
                cases hbc : truthy vc with
                | ok bc =>
                    cases bc with
                    | false =>
                        simp [evalExpr, hc, hbc] at hk
                        have h' := ihe s s' b v hrel hk
                        simpa [evalExpr, hc', hbc] using h'
                    | true =>
                        simp [evalExpr, hc, hbc] at hk
                        have h' := ihe s s' a v hrel hk
                        simpa [evalExpr, hc', hbc] using h'
                | ub => simp [evalExpr, hc, hbc] at hk
                | timeout => simp [evalExpr, hc, hbc] at hk
            | ub => simp [evalExpr, hc] at hk
            | timeout => simp [evalExpr, hc] at hk
        | call f args =>
            cases ha : evalArgs p n s args with
            | ok vs =>
                have ha' := iha s s' args vs hrel ha
                cases hf : p f with
                | none => simp [evalExpr, ha, hf] at hk
                | some fn =>
                    have hlen : fn.params.length = vs.length := by
                      by_cases h : fn.params.length = vs.length
                      · exact h
                      · simp [evalExpr, ha, hf, h] at hk
                    have hr : StateExt ⟨frameLocals fn.params vs, s.mem, true⟩
                        ⟨frameLocals fn.params vs, s'.mem, true⟩ := ⟨rfl, rfl, hrel.2.2⟩
                    cases hb : execStmt p n ⟨frameLocals fn.params vs, s.mem, true⟩ fn.body with
                    | ok rval =>
                        rcases rval with ⟨o, bs1⟩
                        obtain ⟨bs1', hb', hbr⟩ := ihs _ _ _ o bs1 hr hb
                        cases o with
                        | ret rv =>
                            cases rv with
                            | none => simp [evalExpr, ha, hf, hlen, hb] at hk
                            | some v0 =>
                                have hkv : v0 = v := by
                                  simpa [evalExpr, ha, hf, hlen, hb] using hk
                                subst v
                                simp [evalExpr, ha', hf, hlen, hb']
                        | normal => simp [evalExpr, ha, hf, hlen, hb] at hk
                        | brk => simp [evalExpr, ha, hf, hlen, hb] at hk
                        | cont => simp [evalExpr, ha, hf, hlen, hb] at hk
                    | ub => simp [evalExpr, ha, hf, hlen, hb] at hk
                    | timeout => simp [evalExpr, ha, hf, hlen, hb] at hk
            | ub => simp [evalExpr, ha] at hk
            | timeout => simp [evalExpr, ha] at hk
        | memcmp pa pb pn =>
            cases hpa : evalExpr p n s pa with
            | ok va =>
              cases hpb : evalExpr p n s pb with
              | ok vb =>
                cases hpn : evalExpr p n s pn with
                | ok vn =>
                  have hpa' := ihe s s' pa va hrel hpa
                  have hpb' := ihe s s' pb vb hrel hpb
                  have hpn' := ihe s s' pn vn hrel hpn
                  cases vn with
                  | int t k =>
                      simp [evalExpr, hpa, hpb, hpn] at hk
                      have hq := memcmpAt_ext hrel.2.2 hk
                      simpa [evalExpr, hpa', hpb', hpn'] using hq
                  | _ => simp [evalExpr, hpa, hpb, hpn] at hk
                | ub => simp [evalExpr, hpa, hpb, hpn] at hk
                | timeout => simp [evalExpr, hpa, hpb, hpn] at hk
              | ub => simp [evalExpr, hpa, hpb] at hk
              | timeout => simp [evalExpr, hpa, hpb] at hk
            | ub => simp [evalExpr, hpa] at hk
            | timeout => simp [evalExpr, hpa] at hk
        | strlen pa =>
            cases hpa : evalExpr p n s pa with
            | ok va =>
                have hpa' := ihe s s' pa va hrel hpa
                simp [evalExpr, hpa] at hk
                have hq := strlenAt_ext hrel.2.2 hk
                simpa [evalExpr, hpa'] using hq
            | ub => simp [evalExpr, hpa] at hk
            | timeout => simp [evalExpr, hpa] at hk
      · intro s s' es vs hrel hk
        cases es with
        | nil => simpa [evalArgs] using hk
        | cons e es =>
            simp only [evalArgs] at hk ⊢
            cases he : evalExpr p n s e with
            | ok v =>
                have he' := ihe s s' e v hrel he
                cases hes : evalArgs p n s es with
                | ok vs0 =>
                    have hes' := iha s s' es vs0 hrel hes
                    simp [he, hes, he', hes'] at hk ⊢
                    exact hk
                | ub => simp [he, hes] at hk
                | timeout => simp [he, hes] at hk
            | ub => simp [he] at hk
            | timeout => simp [he] at hk
      · intro s s' st o s1 hrel hk
        cases st with
        | skip =>
            simp [execStmt] at hk
            rcases hk with ⟨rfl, rfl⟩
            exact ⟨s', by simp [execStmt], hrel⟩
        | set i e =>
            cases he : evalExpr p n s e with
            | ok v =>
                have he' := ihe s s' e v hrel he
                simp [execStmt, he] at hk
                rcases hk with ⟨rfl, rfl⟩
                refine ⟨{ s' with locals := s'.locals.upd i v }, ?_, ?_⟩
                · simp [execStmt, he']
                · exact ⟨by rw [← hrel.1], hrel.2.1, hrel.2.2⟩
            | ub => simp [execStmt, he] at hk
            | timeout => simp [execStmt, he] at hk
        | store ty a e =>
            cases ha : evalExpr p n s a with
            | ok pa =>
              cases he : evalExpr p n s e with
              | ok v =>
                have ha' := ihe s s' a pa hrel ha
                have he' := ihe s s' e v hrel he
                cases hsr : s.ro with
                | true => simp [execStmt, guard, ha, he, hsr] at hk
                | false =>
                    have hsr' : s'.ro = false := by rw [← hrel.2.1]; exact hsr
                    simp [execStmt, guard, ha, he, hsr] at hk
                    cases hs : store s.mem ty pa v with
                    | ok m1 =>
                        obtain ⟨m1', hst', hm1⟩ := store_ext hrel.2.2 hs
                        simp [hs] at hk
                        rcases hk with ⟨rfl, rfl⟩
                        refine ⟨{ locals := s'.locals, mem := m1', ro := false }, ?_, ?_⟩
                        · simp [execStmt, guard, ha', he', hst', hsr']
                        · exact ⟨by rw [← hrel.1], rfl, hm1⟩
                    | ub => simp [hs] at hk
                    | timeout => simp [hs] at hk
              | ub => simp [execStmt, guard, ha, he] at hk
              | timeout => simp [execStmt, guard, ha, he] at hk
            | ub => simp [execStmt, guard, ha] at hk
            | timeout => simp [execStmt, guard, ha] at hk
        | eval e =>
            cases he : evalExpr p n s e with
            | ok v =>
                have he' := ihe s s' e v hrel he
                simp [execStmt, he] at hk
                rcases hk with ⟨rfl, rfl⟩
                exact ⟨s', by simp [execStmt, he'], hrel⟩
            | ub => simp [execStmt, he] at hk
            | timeout => simp [execStmt, he] at hk
        | call dst f args =>
            cases ha : evalArgs p n s args with
            | ok vs =>
                have ha' := iha s s' args vs hrel ha
                cases hf : p f with
                | none => simp [execStmt, guard, ha, hf] at hk
                | some fn =>
                    have hlen : fn.params.length = vs.length := by
                      by_cases h : fn.params.length = vs.length
                      · exact h
                      · simp [execStmt, guard, ha, hf, h] at hk
                    have hcr : StateExt ⟨frameLocals fn.params vs, s.mem, s.ro⟩
                        ⟨frameLocals fn.params vs, s'.mem, s'.ro⟩ := ⟨rfl, hrel.2.1, hrel.2.2⟩
                    cases hc : execStmt p n ⟨frameLocals fn.params vs, s.mem, s.ro⟩ fn.body with
                    | ok rval =>
                        rcases rval with ⟨co, cs1⟩
                        obtain ⟨cs1', hc', hcr'⟩ := ihs _ _ _ co cs1 hcr hc
                        cases co with
                        | ret rv =>
                            cases dst with
                            | none =>
                                simp [execStmt, guard, ha, hf, hlen, hc] at hk
                                rcases hk with ⟨rfl, rfl⟩
                                refine ⟨{ locals := s'.locals, mem := cs1'.mem, ro := s'.ro }, ?_, ?_⟩
                                · simp [execStmt, guard, ha', hf, hlen, hc']
                                · exact ⟨by rw [← hrel.1], hrel.2.1, hcr'.2.2⟩
                            | some d =>
                                cases rv with
                                | none => simp [execStmt, guard, ha, hf, hlen, hc] at hk
                                | some v =>
                                    simp [execStmt, guard, ha, hf, hlen, hc] at hk
                                    rcases hk with ⟨rfl, rfl⟩
                                    refine ⟨{ locals := s'.locals.upd d v, mem := cs1'.mem, ro := s'.ro }, ?_, ?_⟩
                                    · simp [execStmt, guard, ha', hf, hlen, hc']
                                    · exact ⟨by rw [← hrel.1], hrel.2.1, hcr'.2.2⟩
                        | normal =>
                            cases dst with
                            | none =>
                                simp [execStmt, guard, ha, hf, hlen, hc] at hk
                                rcases hk with ⟨rfl, rfl⟩
                                refine ⟨{ locals := s'.locals, mem := cs1'.mem, ro := s'.ro }, ?_, ?_⟩
                                · simp [execStmt, guard, ha', hf, hlen, hc']
                                · exact ⟨by rw [← hrel.1], hrel.2.1, hcr'.2.2⟩
                            | some d => simp [execStmt, guard, ha, hf, hlen, hc] at hk
                        | brk => simp [execStmt, guard, ha, hf, hlen, hc] at hk
                        | cont => simp [execStmt, guard, ha, hf, hlen, hc] at hk
                    | ub => simp [execStmt, guard, ha, hf, hlen, hc] at hk
                    | timeout => simp [execStmt, guard, ha, hf, hlen, hc] at hk
            | ub => simp [execStmt, guard, ha] at hk
            | timeout => simp [execStmt, guard, ha] at hk
        | seq a b =>
            cases ha : execStmt p n s a with
            | ok rval =>
                rcases rval with ⟨ao, as1⟩
                obtain ⟨as1', ha', har⟩ := ihs s s' a ao as1 hrel ha
                cases ao with
                | normal =>
                    simp [execStmt, guard, ha] at hk
                    obtain ⟨s1', hb', hbr⟩ := ihs as1 as1' b o s1 har hk
                    refine ⟨s1', ?_, hbr⟩
                    simp [execStmt, guard, ha, ha', hb']
                | ret v =>
                    simp [execStmt, guard, ha] at hk
                    rcases hk with ⟨rfl, rfl⟩
                    exact ⟨as1', by simp [execStmt, guard, ha, ha'], har⟩
                | brk =>
                    simp [execStmt, guard, ha] at hk
                    rcases hk with ⟨rfl, rfl⟩
                    exact ⟨as1', by simp [execStmt, guard, ha, ha'], har⟩
                | cont =>
                    simp [execStmt, guard, ha] at hk
                    rcases hk with ⟨rfl, rfl⟩
                    exact ⟨as1', by simp [execStmt, guard, ha, ha'], har⟩
            | ub => simp [execStmt, guard, ha] at hk
            | timeout => simp [execStmt, guard, ha] at hk
        | ite c a b =>
            cases hc : evalExpr p n s c with
            | ok vc =>
                have hc' := ihe s s' c vc hrel hc
                cases hbc : truthy vc with
                | ok bc =>
                    cases bc with
                    | false =>
                        simp [execStmt, guard, hc, hbc] at hk
                        obtain ⟨s1', h', hr⟩ := ihs s s' b o s1 hrel hk
                        refine ⟨s1', ?_, hr⟩
                        simpa [execStmt, guard, hc', hbc] using h'
                    | true =>
                        simp [execStmt, guard, hc, hbc] at hk
                        obtain ⟨s1', h', hr⟩ := ihs s s' a o s1 hrel hk
                        refine ⟨s1', ?_, hr⟩
                        simpa [execStmt, guard, hc', hbc] using h'
                | ub => simp [execStmt, guard, hc, hbc] at hk
                | timeout => simp [execStmt, guard, hc, hbc] at hk
            | ub => simp [execStmt, guard, hc] at hk
            | timeout => simp [execStmt, guard, hc] at hk
        | loop body step =>
            cases hb : execStmt p n s body with
            | ok rval =>
                rcases rval with ⟨bo, bs1⟩
                obtain ⟨bs1', hb', hbr⟩ := ihs s s' body bo bs1 hrel hb
                cases bo with
                | brk =>
                    simp [execStmt, guard, hb] at hk
                    rcases hk with ⟨rfl, rfl⟩
                    exact ⟨bs1', by simp [execStmt, guard, hb, hb'], hbr⟩
                | ret v =>
                    simp [execStmt, guard, hb] at hk
                    rcases hk with ⟨rfl, rfl⟩
                    exact ⟨bs1', by simp [execStmt, guard, hb, hb'], hbr⟩
                | normal | cont =>
                    cases hs : execStmt p n bs1 step with
                    | ok rval2 =>
                        rcases rval2 with ⟨so, ss1⟩
                        obtain ⟨ss1', hs', hsr⟩ := ihs bs1 bs1' step so ss1 hbr hs
                        cases so with
                        | normal =>
                            simp [execStmt, guard, hb, hs] at hk
                            obtain ⟨s1', hl', hlr⟩ := ihs ss1 ss1' (.loop body step) o s1 hsr hk
                            refine ⟨s1', ?_, hlr⟩
                            simp [execStmt, guard, hb, hb', hs, hs', hl']
                        | ret v => simp [execStmt, guard, hb, hs] at hk
                        | brk => simp [execStmt, guard, hb, hs] at hk
                        | cont => simp [execStmt, guard, hb, hs] at hk
                    | ub => simp [execStmt, guard, hb, hs] at hk
                    | timeout => simp [execStmt, guard, hb, hs] at hk
            | ub => simp [execStmt, guard, hb] at hk
            | timeout => simp [execStmt, guard, hb] at hk
        | brk =>
            simp [execStmt] at hk
            rcases hk with ⟨rfl, rfl⟩
            exact ⟨s', by simp [execStmt], hrel⟩
        | cont =>
            simp [execStmt] at hk
            rcases hk with ⟨rfl, rfl⟩
            exact ⟨s', by simp [execStmt], hrel⟩
        | ret e =>
            cases e with
            | none =>
                simp [execStmt] at hk
                rcases hk with ⟨rfl, rfl⟩
                exact ⟨s', by simp [execStmt], hrel⟩
            | some ex =>
                cases he : evalExpr p n s ex with
                | ok v =>
                    have he' := ihe s s' ex v hrel he
                    simp [execStmt, he] at hk
                    rcases hk with ⟨rfl, rfl⟩
                    exact ⟨s', by simp [execStmt, he'], hrel⟩
                | ub => simp [execStmt, he] at hk
                | timeout => simp [execStmt, he] at hk
        | alloc i size =>
            cases hc : readBytes s.mem 0 0 8 with
            | ok c =>
                have hc' := readBytes_ext hrel.2.2 hc
                by_cases hok : decodeLE c ≠ 0 ∧ s.mem (decodeLE c) = none
                · have hok' : decodeLE c ≠ 0 ∧ s'.mem (decodeLE c) = none :=
                    ⟨hok.1, MemExt.of_none hrel.2.2 hok.2⟩
                  simp [execStmt, guard, hc, hok] at hk
                  cases hw : writeBytes s.mem 0 0 (encodeLE 8 (decodeLE c + 1)) with
                  | ok m1 =>
                      obtain ⟨m1', hw', hm1⟩ := writeBytes_ext hrel.2.2 hw
                      let b := decodeLE c
                      let m2 := m1.upd b (List.replicate size 0)
                      let m2' := m1'.upd b (List.replicate size 0)
                      have hm2 : MemExt m2 m2' := by
                        intro x
                        by_cases hx : x = b
                        · subst x
                          right
                          refine ⟨List.replicate size 0, [], ?_, ?_⟩
                          · simp [m2, Mem.upd, hok.2]
                          · simp [m2', Mem.upd, hok'.2]
                        · simpa [m2, m2', Mem.upd, hx] using hm1 x
                      simp [hw] at hk
                      rcases hk with ⟨rfl, rfl⟩
                      refine ⟨{ locals := s'.locals.upd i (.ptr (decodeLE c) 0), mem := m2', ro := s'.ro }, ?_, ?_⟩
                      · simp [execStmt, guard, hc', hok', hw', m2, m2', b]
                      · exact ⟨by rw [← hrel.1], hrel.2.1, hm2⟩
                  | ub => simp [hw] at hk
                  | timeout => simp [hw] at hk
                · simp [execStmt, guard, hc, hok] at hk
            | ub => simp [execStmt, guard, hc] at hk
            | timeout => simp [execStmt, guard, hc] at hk
        | memcpy d src cnt =>
            cases hd : evalExpr p n s d with
            | ok vd =>
              cases hsrc : evalExpr p n s src with
              | ok vsrc =>
                cases hn : evalExpr p n s cnt with
                | ok vn =>
                  have hd' := ihe s s' d vd hrel hd
                  have hsrc' := ihe s s' src vsrc hrel hsrc
                  have hn' := ihe s s' cnt vn hrel hn
                  cases hsr : s.ro with
                  | true => simp [execStmt, guard, hd, hsrc, hn, hsr] at hk
                  | false =>
                      have hsr' : s'.ro = false := by rw [← hrel.2.1]; exact hsr
                      cases vd with
                      | ptr bd od =>
                        cases vsrc with
                        | ptr bs os =>
                          cases vn with
                          | int _ k =>
                              by_cases hov : (¬ bd = bs ∨ od + k ≤ os) ∨ os + k ≤ od
                              · simp [execStmt, guard, hd, hsrc, hn, hsr, hov] at hk
                                cases hr : readBytes s.mem bs os k with
                                | ok bytes =>
                                    have hr' := readBytes_ext hrel.2.2 hr
                                    simp [hr] at hk
                                    cases hw : writeBytes s.mem bd od bytes with
                                    | ok m1 =>
                                        obtain ⟨m1', hw', hm1⟩ := writeBytes_ext hrel.2.2 hw
                                        simp [hw] at hk
                                        rcases hk with ⟨rfl, rfl⟩
                                        refine ⟨{ locals := s'.locals, mem := m1', ro := false }, ?_, ?_⟩
                                        · simp [execStmt, guard, hd', hsrc', hn', hsr', hov, hr', hw']
                                        · exact ⟨by rw [← hrel.1], rfl, hm1⟩
                                    | ub => simp [hw] at hk
                                    | timeout => simp [hw] at hk
                                | ub => simp [hr] at hk
                                | timeout => simp [hr] at hk
                              · simp [execStmt, guard, hd, hsrc, hn, hsr, hov] at hk
                          | _ => simp [execStmt, guard, hd, hsrc, hn, hsr] at hk
                        | _ => simp [execStmt, guard, hd, hsrc, hn, hsr] at hk
                      | _ => simp [execStmt, guard, hd, hsrc, hn, hsr] at hk
                | ub => simp [execStmt, guard, hd, hsrc, hn] at hk
                | timeout => simp [execStmt, guard, hd, hsrc, hn] at hk
              | ub => simp [execStmt, guard, hd, hsrc] at hk
              | timeout => simp [execStmt, guard, hd, hsrc] at hk
            | ub => simp [execStmt, guard, hd] at hk
            | timeout => simp [execStmt, guard, hd] at hk
        | memset d cval cnt =>
            cases hd : evalExpr p n s d with
            | ok vd =>
              cases hcval : evalExpr p n s cval with
              | ok vc =>
                cases hcnt : evalExpr p n s cnt with
                | ok vn =>
                  have hd' := ihe s s' d vd hrel hd
                  have hcval' := ihe s s' cval vc hrel hcval
                  have hcnt' := ihe s s' cnt vn hrel hcnt
                  cases hsr : s.ro with
                  | true => simp [execStmt, guard, hd, hcval, hcnt, hsr] at hk
                  | false =>
                      have hsr' : s'.ro = false := by rw [← hrel.2.1]; exact hsr
                      cases vd with
                      | ptr bd od =>
                        cases vc with
                        | int _ x =>
                          cases vn with
                          | int _ k =>
                              simp [execStmt, guard, hd, hcval, hcnt, hsr] at hk
                              cases hw : writeBytes s.mem bd od (List.replicate k (x % 256).toUInt8) with
                              | ok m1 =>
                                  obtain ⟨m1', hw', hm1⟩ := writeBytes_ext hrel.2.2 hw
                                  simp [hw] at hk
                                  rcases hk with ⟨rfl, rfl⟩
                                  refine ⟨{ locals := s'.locals, mem := m1', ro := false }, ?_, ?_⟩
                                  · simp [execStmt, guard, hd', hcval', hcnt', hsr', hw']
                                  · exact ⟨by rw [← hrel.1], rfl, hm1⟩
                              | ub => simp [hw] at hk
                              | timeout => simp [hw] at hk
                          | _ => simp [execStmt, guard, hd, hcval, hcnt, hsr] at hk
                        | _ => simp [execStmt, guard, hd, hcval, hcnt, hsr] at hk
                      | _ => simp [execStmt, guard, hd, hcval, hcnt, hsr] at hk
                | ub => simp [execStmt, guard, hd, hcval, hcnt] at hk
                | timeout => simp [execStmt, guard, hd, hcval, hcnt] at hk
              | ub => simp [execStmt, guard, hd, hcval] at hk
              | timeout => simp [execStmt, guard, hd, hcval] at hk
            | ub => simp [execStmt, guard, hd] at hk
            | timeout => simp [execStmt, guard, hd] at hk


/-- Lift the relational `ExS` judgement from a memory to any extension of it.
    The witness state is chosen at fuel `K`; fuel monotonicity then shows the
    same state is produced at every larger fuel. -/
theorem ExS_ext {p : Prog} {s s' : State} {st : Stmt} {o : Outcome} {s1 : State}
    (hrel : StateExt s s') (h : ExS p s st o s1) :
    ∃ s1', ExS p s' st o s1' ∧ StateExt s1 s1' := by
  obtain ⟨K, hK⟩ := h
  have hK0 := hK K (Nat.le_refl K)
  obtain ⟨s1', hK0', hrel1⟩ := (ext_step p K).2.2 s s' st o s1 hrel hK0
  refine ⟨s1', ⟨K, ?_⟩, hrel1⟩
  intro n hn
  have hne : execStmt p K s' st ≠ .timeout := by
    rw [hK0']
    intro e
    cases e
  rw [execStmt_mono p hne n hn]
  exact hK0'


/-- Memory-level form: identical locals and read-only flag. -/
theorem ExS_mem_ext {p : Prog} {m m' : Mem} {loc : Locals} {ro : Bool}
    {st : Stmt} {o : Outcome} {s1 : State}
    (hm : MemExt m m') (h : ExS p ⟨loc, m, ro⟩ st o s1) :
    ∃ s1', ExS p ⟨loc, m', ro⟩ st o s1' ∧ StateExt s1 s1' :=
  ExS_ext (s := ⟨loc, m, ro⟩) (s' := ⟨loc, m', ro⟩) ⟨rfl, rfl, hm⟩ h

end
end MiniC
