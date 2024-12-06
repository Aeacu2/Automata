import Mathlib.Tactic
import Mathlib.Data.List.Basic
import Batteries.Data.List.Basic
import Mathlib.Data.Nat.Digits
import Automata.DFA
import Automata.NFA
import Automata.Pumping
import Automata.Input
import Automata.LeadingZeroes

import Automata.Collapse



-- Auxilliary theorems for recover
theorem finLt (m : Fin (n+1)) (b : ℕ) : b < m.val → b < n := by omega

theorem finPred (m : Fin n) (a : Fin n) (h : a > m): a.val - 1 < n - 1 := by omega

-- Auxilliary function for project
def recover_value (m : Fin (n + 1)) (x: Fin (b+2)) (f: Fin n → Fin (b+2)) :
 (Fin (n + 1) → Fin (b+2)) :=
    fun i => if h1: i.val < m.val then f ⟨i.val, finLt m i.val h1⟩
      else if h2: i.val > m.val then f ⟨i.val - 1, finPred m i h2⟩ else x

def project (m : Fin (n+1)) (dfa : DFA (Fin (n+1) → Fin (b+2)) state) [DecidableEq state] :
  NFA (Fin n → Fin (b+2)) state := {
  transition :=
  fun a q => ⟨(List.map (fun (x : Fin (b+2)) => dfa.transition (recover_value m x a) q)
    (FinEnum.toList (Fin (b+2)))).dedup, by apply List.nodup_dedup⟩
  start := ⟨[dfa.start], List.nodup_singleton dfa.start⟩
  output := dfa.output
}

theorem project_accept [DecidableEq state](dfa : DFA (Fin (n + 1) → Fin (b+2)) state) (m : Fin (n + 1)) (l : List (Fin n → Fin (b+2))) : dfa.eval (l.map (recover_value m x)) → (project m dfa).eval l := by
  sorry

theorem project_acceptZero [DecidableEq state] (dfa : DFA (Fin (n + 1) → Fin (b+2)) state) (h: DFA.acceptZero dfa) (m : Fin (n + 1)) : NFA.acceptZero (project m dfa) := by
  simp only [DFA.acceptZero, NFA.acceptZero] at *
  intro x hx z
  simp only [project, NFA.eval, NFA.transFrom, recover_value]
  sorry

theorem DFAO.bounded_out [Fintype state] (dfao : DFAO (Fin n → Fin (b+2)) state out) (x : List (Fin n → Fin (b+2))) (o: out)(h: ∀ (x : List (Fin n → Fin (b+2))), dfao.eval x = o → (∀ m, dfao.eval (padZeroes m x) = o)) : ∀ k, dfao.eval (padZeroes k x) = o → dfao.eval (padZeroes (Fintype.card state) x) = o := by
  rintro k hkxo
  by_cases hkstate : k ≤ Fintype.card state
  . have: Fintype.card state = (Fintype.card state - k) + k := by omega
    rw[this, ← padZeroes_add (Fintype.card state - k) k x]
    apply h
    exact hkxo

  simp only [not_le] at hkstate
  -- Question: How to get this kind of descent argument work in lean?
  . induction' hk : k - Fintype.card state using Nat.strong_induction_on  with d ih generalizing k
    have hkxlen : Fintype.card state ≤ (padZeroes k x).length := by
      simp only [padZeroes_length]
      omega

    obtain ⟨a, b', c, hkxabc, hablen, hne, hy⟩ := dfao.pumping_lemma_eval hkxo hkxlen
    have haco : dfao.eval (a ++ c) = o := by
      apply hy
      simp only [Language.mem_mul, exists_exists_and_exists_and_eq_and, List.append_assoc]
      use a, (by exact rfl), [], (by exact Language.nil_mem_kstar {b'}), c, (by exact rfl)
      simp only [List.nil_append]
    -- have hblen : 0 < b'.length := by
    --   exact List.length_pos_of_ne_nil hne

    have habzero : ∀ i, ∀ (hi: i < a.length + b'.length),  (a ++ b')[i]' (by rw[List.length_append]; exact hi) = fun _ => 0 := by
      intro i hi
      rw[← List.getElem_append_left (a++b') c]
      trans (padZeroes k x)[i]
      congr 1
      . exact hkxabc.symm
      . apply padZeroes_zero k
        omega
      simp only [List.append_assoc, List.length_append]
      . omega

    have hazero : ∀ i, ∀ (hi: i < a.length),  a[i]' (by omega) = fun _ => 0 := by
      intro i hi
      rw[← List.getElem_append_left a b']
      apply habzero i
      . omega
    have hbzero : ∀ i, ∀ (hi: i < b'.length),  b'[i]' (by omega) = fun _ => 0 := by
      intro i hi
      -- rw[← List.getElem_append_right' a b'] Why?
      have : (a ++ b')[a.length + i]'(by rw[List.length_append]; omega) = b'[i] := by
        rw[List.getElem_append_right']
        simp only [add_tsub_cancel_left]
        omega
      rw[← this]
      apply habzero (a.length + i)
      omega
    have har: a = List.replicate a.length (fun _ => 0) := by
      apply List.ext_getElem
      . simp
      . intro n_1 h₁ h₂
        simp only [List.getElem_replicate]
        exact hazero n_1 h₁
    have hbr: b' = List.replicate b'.length (fun _ => 0) := by
      apply List.ext_getElem
      . simp
      . intro n_1 h₁ h₂
        simp only [List.getElem_replicate]
        exact hbzero n_1 h₁
    have habk : a.length + b'.length < k := by omega
    have hk : (List.replicate k (fun _ => 0)) = (List.replicate (a.length + b'.length) (fun _ => 0)) ++ (List.replicate (k - a.length - b'.length) (fun _ : Fin n => (0 : Fin (b + 2)))) := by
      simp[List.append_replicate_replicate]
      omega
    have hcx : c = padZeroes (k - a.length - b'.length) x := by
      rw[har, hbr] at hkxabc
      rw[List.append_assoc, ← padZeroes, ← padZeroes, padZeroes_add] at hkxabc
      simp only [padZeroes] at hkxabc
      have : c = padZeroes (k - (a.length + b'.length)) x := by
        apply List.eq_diff_of_replicate_append_eq
        . exact hkxabc.symm
        . omega
      rw[this]
      convert rfl using 2
      omega
    have hac : a ++ c = padZeroes (k - b'.length) x := by
      rw[hcx, har]
      simp only [padZeroes, List.length_replicate]
      rw[← List.append_assoc]
      simp only [List.length_replicate, List.append_replicate_replicate,
        List.append_cancel_right_eq, List.replicate_inj, AddLeftCancelMonoid.add_eq_zero,
        List.length_eq_zero, or_true, and_true]
      omega

    by_cases hkb : k - b'.length ≤ Fintype.card state
    . have : Fintype.card state = (Fintype.card state - (k - b'.length)) + (k - b'.length) := by omega
      rw[this, ← padZeroes_add (Fintype.card state - (k - b'.length)) (k - b'.length) x, ← hac]
      apply h (a ++ c)
      . exact haco
    . simp only [not_le] at hkb
      have hblen : 0 < b'.length := by
        exact List.length_pos_of_ne_nil hne

      specialize ih (k - b'.length - Fintype.card state) (by omega) (k - b'.length)
      apply ih
      . rw[← hac]
        exact haco
      . exact hkb
      . rfl

theorem DFA.bounded_accept [Fintype state] (dfa : DFA (Fin n → Fin (b+2)) state) (x : List (Fin n → Fin (b+2)))(h: dfa.acceptZero): ∀ z, (∃ k, z = padZeroes k x) ∧ dfa.eval z → dfa.eval (padZeroes (Fintype.card state) x) := by
  have := DFAO.bounded_out dfa x true
  intro z a
  simp_all only [implies_true, true_implies, DFA.acceptZero]
  obtain ⟨left, right⟩ := a
  obtain ⟨w, h_1⟩ := left
  subst h_1
  apply this
  · exact right

theorem NFA.bounded_accept [Fintype state] [DecidableEq state] (nfa : NFA (Fin n → Fin (b+2)) state) (x : List (Fin n → Fin (b+2)))(h: nfa.acceptZero): ∀ z, (∃ k, z = padZeroes k x) ∧ nfa.eval z → nfa.eval (padZeroes (Fintype.card (ListND state)) x) := by
  simp only [NFA.acceptZero, ← NFA.toDFA_eval] at *
  have := DFA.bounded_accept (nfa.toDFA) x h
  intro z a
  simp_all only [and_imp, forall_exists_index]
  obtain ⟨left, right⟩ := a
  obtain ⟨w, h_1⟩ := left
  subst h_1
  apply this
  · rfl
  · exact right

theorem project_correct [Fintype state] [DecidableEq state] (l : List ℕ) (m : Fin (l.length + 1)) (dfa : DFA (Fin (l.length +1) → Fin (b+2)) state) (h: dfa.acceptZero):
  ∃ (x : ℕ), dfa.eval (inputToBase (b+2) (by norm_num) (l.insertNth m x) (by sorry)) ↔ (project m dfa).eval (padZeroes (Fintype.card (ListND state)) (inputToBase (b+2) (by omega) l (by sorry))):= by
  sorry
