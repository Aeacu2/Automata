import Mathlib.Tactic
import Automata.DFA
import Automata.NFA
import Automata.Boolean
import Automata.Replicate
import Automata.Pumping

def padZeros (m : ℕ) (x : List (Fin n → Fin (b+2))) : List (Fin n → Fin (b+2)) :=
  List.replicate m (fun _ => 0) ++ x

def padZeros_succ (m : ℕ) (x : List (Fin n → Fin (b+2))) : padZeros (m + 1) x = (fun _ => 0) :: padZeros m x := by
  simp only [padZeros, List.replicate, List.cons_append]

theorem padZeros_add (a b : ℕ) (x : List (Fin n → Fin (k+2))) : padZeros a (padZeros b x) = padZeros (a + b) x := by
  simp only [padZeros]
  rw[← List.append_assoc, List.replicate_append_add]

theorem padZeros_length (m : ℕ) (x : List (Fin n → Fin (b+2))) : (padZeros m x).length = m + x.length := by
  simp only [padZeros]
  rw[List.replicate_append_length]

theorem padZeros_zero (m i: ℕ) (x : List (Fin n → Fin (b+2))) (h : i < m) : (padZeros m x)[i]'(by simp only [padZeros, List.length_append, List.length_replicate]; omega) = fun _ => 0 := by
  simp only [padZeros]
  rwa[List.getElem_of_replicate_append_left]

theorem padZeros_diff (a b: ℕ) (x y : List (Fin n → Fin (k+2))) (hab : a ≤ b) (h: (padZeros a x) = (padZeros b y)) : x = padZeros (b - a) y := by
  simp only [padZeros] at *
  apply List.eq_diff_of_replicate_append_eq
  . exact h
  . exact hab

def DFA.respectZero (dfa : DFA (Fin n → Fin (b+2)) state) : Prop := ∀ (x : List (Fin n → Fin (b+2))), ∀ m, dfa.eval x ↔ dfa.eval (padZeros m x)

def NFA.respectZero [DecidableEq state] (nfa : NFA (Fin n → Fin (b+2)) state) : Prop := ∀ (x : List (Fin n → Fin (b+2))), ∀ m, nfa.eval x ↔ nfa.eval (padZeros m x)

theorem DFA.negate_respectZero (dfa : DFA (Fin n → Fin (b+2)) state) (h: dfa.respectZero) : dfa.negate.respectZero := by
  rw[DFA.respectZero] at *
  intro x m
  specialize h x m
  simp_all only [Bool.coe_iff_coe, negate_eval, Bool.not_eq_true']

theorem DFA.union_respectZero (dfa1 : DFA (Fin n → Fin (b+2)) state1) (dfa2 : DFA (Fin n → Fin (b+2)) state2) (h1: dfa1.respectZero) (h2: dfa2.respectZero) : (dfa1.union dfa2).respectZero := by
  rw[DFA.respectZero] at *
  intro x m
  specialize h1 x m
  specialize h2 x m
  simp_all only [Bool.coe_iff_coe, union_eval, Bool.or_eq_true]

theorem DFA.intersection_respectZero (dfa1 : DFA (Fin n → Fin (b+2)) state1) (dfa2 : DFA (Fin n → Fin (b+2)) state2) (h1: dfa1.respectZero) (h2: dfa2.respectZero) : (dfa1.intersection dfa2).respectZero := by
  rw[DFA.respectZero] at *
  intro x m
  specialize h1 x m
  specialize h2 x m
  simp_all only [Bool.coe_iff_coe, intersection_eval, Bool.and_eq_true]

-- theorem equality_respectZero : (eqBase (b + 2) l m n).respectZero := by
--   rw[DFA.respectZero]
--   intro x c
--   constructor
--   intro h
--   rw[padZeros]
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
--   . intro h
--     contrapose h; simp_all only [Bool.not_eq_true]
--     rw[padZeros]
--     rw[DFAO.eval, DFAO.evalFrom, DFAO.transFrom_of_append]
--     nth_rw 1 [eqBase]
--     simp only [Fin.isValue, beq_iff_eq]
--     suffices: (DFAO.transFrom (eqBase (b + 2) l m n) (List.replicate c fun _ ↦ 0) (eqBase (b + 2) l m n).start) = 0
--     . rw[this]
--       simp[DFAO.eval, DFAO.evalFrom] at h
--       nth_rw 1 3 [eqBase] at h
--       simp only [Fin.isValue, beq_iff_eq] at h
--       exact h
--     nth_rw 2 [eqBase]
--     simp only [Fin.isValue]
--     apply eqBase_transFrom_zero 0 (List.replicate c fun _ ↦ 0) |>.mpr
--     simp_all only [Fin.isValue, List.mem_replicate, ne_eq, Fin.val_zero, and_imp, implies_true, and_self]

def DFA.acceptZero (dfa : DFA (Fin n → Fin (b+2)) state) : Prop := ∀ (x : List (Fin n → Fin (b+2))), (dfa.eval x → ∀ m, dfa.eval (padZeros m x))

def NFA.acceptZero [DecidableEq state] (nfa : NFA (Fin n → Fin (b+2)) state) : Prop := ∀ (x : List (Fin n → Fin (b+2))), (nfa.eval x → ∀ m, nfa.eval (padZeros m x))

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
theorem DFAO.bounded_out [Fintype state] (dfao : DFAO (Fin n → Fin (b+2)) state out) (x : List (Fin n → Fin (b+2))) (o: out)(h: ∀ (x : List (Fin n → Fin (b+2))), dfao.eval x = o → (∀ m, dfao.eval (padZeros m x) = o)) : ∀ k, dfao.eval (padZeros k x) = o → dfao.eval (padZeros (Fintype.card state) x) = o := by
  rintro k hkxo
  by_cases hkstate : k ≤ Fintype.card state
  . have: Fintype.card state = (Fintype.card state - k) + k := by omega
    rw[this, ← padZeros_add (Fintype.card state - k) k x]
    apply h
    exact hkxo

  simp only [not_le] at hkstate
  -- Question: How to get this kind of descent argument work in lean?
  . induction' hk : k - Fintype.card state using Nat.strong_induction_on  with d ih generalizing k
    have hkxlen : Fintype.card state ≤ (padZeros k x).length := by
      simp only [padZeros_length]
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
      have : i < (a ++ b').length := by
        rw[List.length_append]
        exact hi
      rw[← List.getElem_append_left this]
      trans (padZeros k x)[i]
      congr 1
      . exact hkxabc.symm
      . apply padZeros_zero k
        omega
      simp only [List.append_assoc, List.length_append]
      . omega

    have hazero : ∀ i, ∀ (hi: i < a.length),  a[i]' (by omega) = fun _ => 0 := by
      intro i hi
      rw[← List.getElem_append_left hi]
      apply habzero i
      . omega
    have hbzero : ∀ i, ∀ (hi: i < b'.length),  b'[i]' (by omega) = fun _ => 0 := by
      intro i hi
      -- rw[← List.getElem_append_right' a b'] Why?
      have : (a ++ b')[a.length + i]'(by rw[List.length_append]; omega) = b'[i] := by
        nth_rw 2 [List.getElem_append_right' a]
        congr 1
        ring
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
      simp[List.replicate_append_replicate]
      omega
    have hcx : c = padZeros (k - a.length - b'.length) x := by
      rw[har, hbr] at hkxabc
      rw[List.append_assoc, ← padZeros, ← padZeros, padZeros_add] at hkxabc
      simp only [padZeros] at hkxabc
      have : c = padZeros (k - (a.length + b'.length)) x := by
        apply List.eq_diff_of_replicate_append_eq
        . exact hkxabc.symm
        . omega
      rw[this]
      convert rfl using 2
      omega
    have hac : a ++ c = padZeros (k - b'.length) x := by
      rw[hcx, har]
      simp only [padZeros, List.length_replicate]
      rw[← List.append_assoc]
      simp only [List.length_replicate, List.replicate_append_replicate,
        List.append_cancel_right_eq, List.replicate_inj, AddLeftCancelMonoid.add_eq_zero,
        List.length_eq_zero, or_true, and_true]
      omega

    by_cases hkb : k - b'.length ≤ Fintype.card state
    . have : Fintype.card state = (Fintype.card state - (k - b'.length)) + (k - b'.length) := by omega
      rw[this, ← padZeros_add (Fintype.card state - (k - b'.length)) (k - b'.length) x, ← hac]
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

theorem DFA.bounded_accept [Fintype state] (dfa : DFA (Fin n → Fin (b+2)) state) (x : List (Fin n → Fin (b+2)))(h: dfa.acceptZero): ∀ z, (∃ k, z = padZeros k x) ∧ dfa.eval z → dfa.eval (padZeros (Fintype.card state) x) := by
  have := DFAO.bounded_out dfa x true
  intro z a
  simp_all only [implies_true, true_implies, DFA.acceptZero]
  obtain ⟨left, right⟩ := a
  obtain ⟨w, h_1⟩ := left
  subst h_1
  apply this
  · exact right

theorem NFA.bounded_accept [Fintype state] [DecidableEq state] (nfa : NFA (Fin n → Fin (b+2)) state) (x : List (Fin n → Fin (b+2)))(h: nfa.acceptZero): ∀ z, (∃ k, z = padZeros k x) ∧ nfa.eval z → nfa.eval (padZeros (Fintype.card (ListND state)) x) := by
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

def NFA.fixLeadingZeros [Fintype state] [DecidableEq state] (nfa : NFA (Fin n → Fin (b+2)) state) : NFA (Fin n → Fin (b+2)) state := {
  transition := nfa.transition
  start := nfa.transFrom (padZeros (Fintype.card (ListND state)) []) nfa.start
  output := nfa.output
}

theorem NFA.fixLeadingZeros_transFrom [Fintype state] [DecidableEq state] (nfa : NFA (Fin n → Fin (b+2)) state) (s : List (Fin n → Fin (b+2))): (nfa.fixLeadingZeros).transFrom s nfa.fixLeadingZeros.start = nfa.transFrom (padZeros (Fintype.card (ListND state)) s) nfa.start := by
  induction s using List.reverseRecOn
  case nil =>
    simp only [NFA.transFrom, NFA.fixLeadingZeros, padZeros]
  case append_singleton as a ih =>
    simp[NFA.transFrom_of_append, ih]
    nth_rw 2 [padZeros]
    rw[← List.append_assoc]
    rw[NFA.transFrom_of_append, padZeros]
    rfl


theorem NFA.fixLeadingZeros_eval [Fintype state] [DecidableEq state] (nfa : NFA (Fin n → Fin (b+2)) state) (x : List (Fin n → Fin (b+2))) : (nfa.fixLeadingZeros).eval x = nfa.eval (padZeros (Fintype.card (ListND state)) x) := by
  simp only [NFA.eval, NFA.evalFrom]
  rw[NFA.fixLeadingZeros_transFrom]
  rfl

theorem NFA.fixLeadingZeros.accept [Fintype state] [DecidableEq state] (nfa : NFA (Fin n → Fin (b+2)) state) (x : List (Fin n → Fin (b+2)))(h: nfa.acceptZero): ∀ z, (∃ k, z = padZeros k x) ∧ nfa.eval z → nfa.fixLeadingZeros.eval x := by
  intro z a
  simp only [NFA.fixLeadingZeros_eval]
  apply NFA.bounded_accept
  . exact h
  . exact a

theorem NFA.fixLeadingZeroes.acceptZero [Fintype state] [DecidableEq state] (nfa : NFA (Fin n → Fin (b+2)) state) (h: nfa.acceptZero): (nfa.fixLeadingZeros).acceptZero := by
  simp_all only [NFA.acceptZero]
  intro x h' m
  rw[NFA.fixLeadingZeros_eval] at h'
  rw[NFA.fixLeadingZeros_eval, padZeros_add]
  simp only [add_comm]
  rw[← padZeros_add]
  simp_all only

-- Legacy

-- theorem equality_acceptZero : (eqBase (b + 2) l m n).acceptZero := by
--   rw[DFA.acceptZero]
--   intro x h c
--   rw[padZeros]
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
