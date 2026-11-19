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

end MiniC
