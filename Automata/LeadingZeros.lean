import Mathlib.Tactic
import Automata.DFA
import Automata.NFA
import Automata.Boolean
import Automata.Input
import Automata.Replicate
import Automata.Pumping
import Automata.Equality

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

def DFA.respectZero (dfa : DFA (Fin n → Fin (b+2)) state) : Prop := ∀ (x : List (Fin n → Fin (b+2))), ∀ m, dfa.eval x ↔ dfa.eval (padZeroes m x)

def NFA.respectZero [DecidableEq state] (nfa : NFA (Fin n → Fin (b+2)) state) : Prop := ∀ (x : List (Fin n → Fin (b+2))), ∀ m, nfa.eval x ↔ nfa.eval (padZeroes m x)

theorem equality_respectZero : (eqBase (b + 2) l m n).respectZero := by
  rw[DFA.respectZero]
  intro x c
  constructor
  intro h
  rw[padZeroes]
  rw[DFAO.eval, DFAO.evalFrom, DFAO.transFrom_of_append]
  nth_rw 1 [eqBase]
  simp only [Fin.isValue, beq_iff_eq]
  suffices: (DFAO.transFrom (eqBase (b + 2) l m n) (List.replicate c fun _ ↦ 0) (eqBase (b + 2) l m n).start) = 0
  . rw[this]
    simp[DFAO.eval, DFAO.evalFrom] at h
    nth_rw 1 3 [eqBase] at h
    simp only [Fin.isValue, beq_iff_eq] at h
    exact h
  nth_rw 2 [eqBase]
  simp only [Fin.isValue]
  apply eqBase_transFrom_zero 0 (List.replicate c fun _ ↦ 0) |>.mpr
  constructor
  . rfl
  . intro f a
    simp_all only [List.mem_replicate, ne_eq, Fin.val_zero]
  . intro h
    contrapose h; simp_all only [Bool.not_eq_true]
    rw[padZeroes]
    rw[DFAO.eval, DFAO.evalFrom, DFAO.transFrom_of_append]
    nth_rw 1 [eqBase]
    simp only [Fin.isValue, beq_iff_eq]
    suffices: (DFAO.transFrom (eqBase (b + 2) l m n) (List.replicate c fun _ ↦ 0) (eqBase (b + 2) l m n).start) = 0
    . rw[this]
      simp[DFAO.eval, DFAO.evalFrom] at h
      nth_rw 1 3 [eqBase] at h
      simp only [Fin.isValue, beq_iff_eq] at h
      exact h
    nth_rw 2 [eqBase]
    simp only [Fin.isValue]
    apply eqBase_transFrom_zero 0 (List.replicate c fun _ ↦ 0) |>.mpr
    simp_all only [Fin.isValue, List.mem_replicate, ne_eq, Fin.val_zero, and_imp, implies_true, and_self]

def DFA.acceptZero (dfa : DFA (Fin n → Fin (b+2)) state) : Prop := ∀ (x : List (Fin n → Fin (b+2))), (dfa.eval x → ∀ m, dfa.eval (padZeroes m x))

def NFA.acceptZero [DecidableEq state] (nfa : NFA (Fin n → Fin (b+2)) state) : Prop := ∀ (x : List (Fin n → Fin (b+2))), (nfa.eval x → ∀ m, nfa.eval (padZeroes m x))

theorem DFA.acceptZero_of_respectZero (dfa : DFA (Fin n → Fin (b+2)) state) (h: dfa.respectZero) : dfa.acceptZero := by
  rw[DFA.acceptZero]
  rw[DFA.respectZero] at h
  intro x hxo m
  specialize h x m
  exact h.mp hxo

theorem NFA.acceptZero_of_respectZero [DecidableEq state] (nfa : NFA (Fin n → Fin (b+2)) state) (h: nfa.respectZero) : nfa.acceptZero := by
  rw[NFA.acceptZero]
  rw[NFA.respectZero] at h
  intro x hxo m
  specialize h x m
  exact h.mp hxo

-- Bounded acceptance theorems: If a DFA/NFA accepts some representation of a input, then there is a bound on the number of leading zeros needed for acceptance
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



-- Legacy

-- theorem equality_acceptZero : (eqBase (b + 2) l m n).acceptZero := by
--   rw[DFA.acceptZero]
--   intro x h c
--   rw[padZeroes]
--   rw[DFAO.eval, DFAO.evalFrom, DFAO.transFrom_of_append]
--   nth_rw 1 [eqBase]
--   simp only [Fin.isValue, beq_iff_eq]
--   suffices: (DFAO.transFrom (eqBase (b + 2) l m n) (List.replicate c fun _ ↦ 0) (eqBase (b + 2) l m n).start) = 0
--   . rw[this]
--     simp[DFAO.eval, DFAO.evalFrom] at h
--     nth_rw 1 3 [eqBase] at h
--     simp only [Fin.isValue, beq_iff_eq] at h
--     exact h
--   nth_rw 2 [eqBase]
--   simp only [Fin.isValue]
--   apply eqBase_transFrom_zero 0 (List.replicate c fun _ ↦ 0) |>.mpr
--   constructor
--   . rfl
--   . intro f a
--     simp_all only [List.mem_replicate, ne_eq, Fin.val_zero]
