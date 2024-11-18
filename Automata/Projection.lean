import Mathlib.Tactic
import Mathlib.Data.List.Basic
import Mathlib.Data.Nat.Digits
import Automata.DFA
import Automata.NFA
import Automata.Input
import Automata.Addition
import Automata.Replicate


-- Auxilliary theorems for recover
theorem finLt (m : Fin (n+1)) (b : ℕ) : b < m.val → b < n := by omega

theorem finPred (m : Fin n) (a : Fin n) (h : a > m): a.val - 1 < n - 1 := by omega

-- Auxilliary function for project
def recover (m : Fin (n + 1)) (x: Fin (b+2)):
  (Fin n → Fin (b+2)) → (Fin (n + 1) → Fin (b+2)) :=
    fun i => fun j => if h1: j.val < m.val then i ⟨j.val, finLt m j.val h1⟩
      else if h2: j.val > m.val then i ⟨j.val - 1, finPred m j h2⟩ else x

def project (m : Fin (n+1)) (dfa : DFA (Fin (n+1) → Fin (b+2)) state) [DecidableEq state] :
  NFA (Fin n → Fin (b+2)) state := {
  transition :=
  fun a q => ⟨(List.map (fun (x : Fin (b+2)) => dfa.transition (recover m x a) q)
    (FinEnum.toList (Fin (b+2)))).dedup, by apply List.nodup_dedup⟩
  start := ⟨[dfa.start], List.nodup_singleton dfa.start⟩
  output := dfa.output
}

#eval [(fun _ => 0 : Fin 2 → Fin (0 + 2)), fun _ => 1]
-- Problem: exists x, 1 + 1 = x?
#eval (project 2 (addBase 2)).eval [fun _ => 1]
-- Fix:
#eval (project 2 (addBase 2)).eval [fun _ => 0, fun _ => 1]

#eval (project 2 (addBase 2)).eval (inputToBase 2 (by omega) [100000, 10000])

def padZeroes (m : ℕ) (x : List (Fin n → Fin (b+2))) : List (Fin n → Fin (b+2)) :=
  List.replicate m (fun _ => 0) ++ x

theorem padZeroes_add (a b : ℕ) (x : List (Fin n → Fin (k+2))) : padZeroes a (padZeroes b x) = padZeroes (a + b) x := by
  simp only [padZeroes]
  rw[← List.append_assoc, List.replicate_append_add]

theorem padZeroes_length (m : ℕ) (x : List (Fin n → Fin (b+2))) : (padZeroes m x).length = m + x.length := by
  simp only [padZeroes]
  rw[List.replicate_append_length]

theorem padZeroes_zero (m i: ℕ) (x : List (Fin n → Fin (b+2))) (h : i < m) : (padZeroes m x)[i]'(by simp only [padZeroes, List.length_append, List.length_replicate]; omega) = fun _ => 0 := by
  simp only [padZeroes]
  rwa[List.getElem_of_replicate_append_left]

theorem padZeroes_diff (a b: ℕ) (x y : List (Fin n → Fin (k+2))) (hab : a ≤ b) (h: (padZeroes a x) = (padZeroes b y)) : x = padZeroes (b - a) y := by
  simp only [padZeroes] at *
  apply List.eq_diff_of_replicate_append_eq
  . exact h
  . exact hab

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

theorem DFA.bounded_accept [Fintype state] (dfa : DFA (Fin n → Fin (b+2)) state) (x : List (Fin n → Fin (b+2)))(h: ∀ (x : List (Fin n → Fin (b+2))), dfa.eval x→ (∀ m, dfa.eval (padZeroes m x))): ∀ z, (∃ k, z = padZeroes k x) ∧ dfa.eval z → dfa.eval (padZeroes (Fintype.card state) x) := by
  have := DFAO.bounded_out dfa x true
  intro z a
  simp_all only [implies_true, true_implies]
  obtain ⟨left, right⟩ := a
  obtain ⟨w, h_1⟩ := left
  subst h_1
  apply this
  · exact right

theorem NFA.bounded_accept [Fintype state] [DecidableEq state] (nfa : NFA (Fin n → Fin (b+2)) state) (x : List (Fin n → Fin (b+2)))(h: ∀ (x : List (Fin n → Fin (b+2))), nfa.eval x→ (∀ m, nfa.eval (padZeroes m x))): ∀ z, (∃ k, z = padZeroes k x) ∧ nfa.eval z → nfa.eval (padZeroes (Fintype.card (ListND state)) x) := by
  simp only [← NFA.toDFA_eval] at *
  have := DFA.bounded_accept (nfa.toDFA) x h
  intro z a
  simp_all only [and_imp, forall_exists_index]
  obtain ⟨left, right⟩ := a
  obtain ⟨w, h_1⟩ := left
  subst h_1
  apply this
  · rfl
  · exact right



-- Old version
-- theorem DFAO.bounded_out [Fintype state] (dfao : DFAO (Fin n → Fin (b+2)) state out) (x : List (Fin n → Fin (b+2))) (o: out)(h: ∀ (x : List (Fin n → Fin (b+2))), dfao.eval x = o → (∀ y, (∃ m, y = padZeroes m x) →  dfao.eval y = o)) : ∀ z, (∃ k, z = (padZeroes k x)) ∧ dfao.eval z = o → dfao.eval (padZeroes (Fintype.card state) x) = o := by
--   simp only [padZeroes]
--   rintro z ⟨⟨k, hz⟩, hzo⟩
--   by_cases hkstate : k ≤ Fintype.card state
--   . apply h z
--     . exact hzo
--     . use Fintype.card state - k
--       rw[hz]
--       simp only [padZeroes]
--       rw[← List.append_assoc, ← List.replicate_add]
--       subst hzo hz
--       simp only [List.append_cancel_right_eq, List.replicate_inj, or_true, and_true]
--       omega

--   simp only [not_le] at hkstate
--   -- Question: How to get this kind of descent argument work in lean?
--   . induction' hk : k - Fintype.card state using Nat.strong_induction_on  with d ih generalizing k z
--     have hzlen : Fintype.card state ≤ z.length := by
--       rw[hz]
--       simp only [List.length_append, List.length_replicate]
--       omega

--     obtain ⟨a, b', c, hzabc, hablen, hne, hy⟩ := dfao.pumping_lemma_eval hzo hzlen
--     have haco : dfao.eval (a ++ c) = o := by
--       apply hy
--       simp only [Language.mem_mul, exists_exists_and_exists_and_eq_and, List.append_assoc]
--       use a, (by exact rfl), [], (by exact Language.nil_mem_kstar {b'}), c, (by exact rfl)
--       simp only [List.nil_append]
--     -- have hblen : 0 < b'.length := by
--     --   exact List.length_pos_of_ne_nil hne

--     have habzero' : ∀ i, ∀ (hi: i < a.length + b'.length),  z[i]'(by omega) = fun _ => 0 := by
--       intro i hi
--       have hik : i < k := by
--         omega
--       simp only [hz]
--       rw[List.getElem_append_left, List.getElem_replicate]
--       rwa[List.length_replicate]
--     have habzero : ∀ i, ∀ (hi: i < a.length + b'.length),  (a ++ b')[i]' (by rw[List.length_append]; exact hi) = fun _ => 0 := by
--       intro i hi
--       rw[← List.getElem_append_left (a++b') c]
--       trans z[i]
--       . congr; exact hzabc.symm
--       specialize habzero' i hi
--       convert habzero'
--       simp only [List.append_assoc, List.length_append]
--       . omega

--     have hazero : ∀ i, ∀ (hi: i < a.length),  a[i]' (by omega) = fun _ => 0 := by
--       intro i hi
--       rw[← List.getElem_append_left a b']
--       apply habzero i
--       . omega
--     have hbzero : ∀ i, ∀ (hi: i < b'.length),  b'[i]' (by omega) = fun _ => 0 := by
--       intro i hi
--       -- rw[← List.getElem_append_right' a b'] Why?
--       have : (a ++ b')[a.length + i]'(by rw[List.length_append]; omega) = b'[i] := by
--         rw[List.getElem_append_right']
--         simp only [add_tsub_cancel_left]
--         omega
--       rw[← this]
--       apply habzero (a.length + i)
--       omega
--     have har: a = List.replicate a.length (fun _ => 0) := by
--       apply List.ext_getElem
--       . simp
--       . intro n_1 h₁ h₂
--         simp only [List.getElem_replicate]
--         exact hazero n_1 h₁
--     have hbr: b' = List.replicate b'.length (fun _ => 0) := by
--       apply List.ext_getElem
--       . simp
--       . intro n_1 h₁ h₂
--         simp only [List.getElem_replicate]
--         exact hbzero n_1 h₁
--     have habk : a.length + b'.length < k := by omega
--     have hk : (List.replicate k (fun _ => 0)) = (List.replicate (a.length + b'.length) (fun _ => 0)) ++ (List.replicate (k - a.length - b'.length) (fun _ : Fin n => (0 : Fin (b + 2)))) := by
--       simp[List.append_replicate_replicate]
--       omega
--     have hcx : c = (List.replicate (k - a.length - b'.length) (fun _ => 0)) ++ x := by
--       rw[har, hbr] at hzabc
--       rw[hzabc] at hz
--       simp only [List.append_replicate_replicate] at hz
--       -- AHhhh! NO!
--       rw[hk] at hz
--       rw[List.append_assoc] at hz
--       exact List.append_cancel_left hz

--     have hac : a ++ c = List.replicate (k - b'.length) (fun _ => 0) ++ x := by
--       rw[hcx, har]
--       rw[← List.append_assoc]
--       simp only [List.length_replicate, List.append_replicate_replicate,
--         List.append_cancel_right_eq, List.replicate_inj, AddLeftCancelMonoid.add_eq_zero,
--         List.length_eq_zero, or_true, and_true]
--       omega
--     by_cases hkb : k - b'.length ≤ Fintype.card state
--     . apply h (a ++ c)
--       . exact haco
--       . -- subst/rw hac !!!
--         use Fintype.card state - (k - b'.length)
--         simp only [hac, padZeroes]
--         rw[← List.append_assoc]
--         simp only [List.append_replicate_replicate, List.append_cancel_right_eq, List.replicate_inj,
--           or_true, and_true]
--         omega
--     . simp only [not_le] at hkb
--       have hblen : 0 < b'.length := by
--         exact List.length_pos_of_ne_nil hne

--       specialize ih (k - b'.length - Fintype.card state) (by omega) (a ++ c) (haco) (k - b'.length) hac hkb rfl

--       exact ih

-- theorem DFA.bounded_accept [Fintype state] (dfa : DFA (Fin n → Fin (b+2)) state) (x : List (Fin n → Fin (b+2)))(h: ∀ (x : List (Fin n → Fin (b+2))), dfa.eval x→ (∀ y, (∃ m, y = padZeroes m x) →  dfa.eval y)) : ∀ z, (∃ k, z = padZeroes k x) ∧ dfa.eval z → dfa.eval (padZeroes (Fintype.card state) x) := by
--   have := DFAO.bounded_out dfa x true
--   intro z a
--   simp_all only [forall_exists_index, and_imp]
--   obtain ⟨left, right⟩ := a
--   obtain ⟨w, h_1⟩ := left
--   subst h_1
--   apply this
--   · intro x_1 a y x_2 h_1
--     subst h_1
--     apply h
--     · simp_all only
--     · rfl
--   · rfl
--   · exact right

-- theorem NFA.bounded_accept [Fintype state] [DecidableEq state] (nfa : NFA (Fin n → Fin (b+2)) state) (x : List (Fin n → Fin (b+2)))(h: ∀ (x : List (Fin n → Fin (b+2))), nfa.eval x→ (∀ y, (∃ m, y = padZeroes m x) →  nfa.eval y)) : ∀ z, (∃ k, z = padZeroes k x) ∧ nfa.eval z → nfa.eval (padZeroes (Fintype.card (ListND state)) x) := by
--   simp only [← NFA.toDFA_eval] at *
--   have := DFA.bounded_accept (nfa.toDFA) x h
--   intro z a
--   simp_all only [forall_exists_index, and_imp]
--   obtain ⟨left, right⟩ := a
--   obtain ⟨w, h_1⟩ := left
--   subst h_1
--   apply this
--   · rfl
--   · exact right
