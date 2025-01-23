import Mathlib.Tactic
import Mathlib.Data.List.Basic
import Batteries.Data.List.Basic
import Mathlib.Data.Nat.Digits
import Automata.DFA
import Automata.NFA
import Automata.Pumping
import Automata.Input
import Automata.LeadingZeros
import Automata.Fin
import Automata.Collapse

def project (m : Fin (n+1)) (dfa : DFA (Fin (n+1) → Fin (b+2)) state) [DecidableEq state] :
  NFA (Fin n → Fin (b+2)) state := {
  transition :=
  fun a q => ⟨(List.map (fun (x : Fin (b+2)) => dfa.transition (recover_value m x a) q)
    (FinEnum.toList (Fin (b+2)))).dedup, by apply List.nodup_dedup⟩
  start := ⟨[dfa.start], List.nodup_singleton dfa.start⟩
  output := dfa.output
}

-- theorem transition_project' [DecidableEq state](dfa : DFA (Fin (n + 1) → Fin (b+2)) state) (m : Fin (n + 1)) (f : (Fin (n+1) → Fin (b+2))) (p q : state) : dfa.transition f p = q → q ∈ ((project m dfa).transition (remove_index m f) p).val := by
--   simp only [project, List.mem_dedup, List.mem_map, FinEnum.mem_toList, true_and]
--   intro h
--   use f m
--   simp[recover_value, insert_remove]
--   exact h

theorem transition_project [DecidableEq state](dfa : DFA (Fin (n + 1) → Fin (b+2)) state) (m : Fin (n + 1)) (f : (Fin (n+1) → Fin (b+2))) (p : state) : dfa.transition f p ∈ ((project m dfa).transition (remove_index m f) p).val := by
  simp only [project, List.mem_dedup, List.mem_map, FinEnum.mem_toList, true_and]
  use f m
  simp[recover_value, insert_remove]

theorem transFrom_project [DecidableEq state](dfa : DFA (Fin (n + 1) → Fin (b+2)) state) (m : Fin (n + 1)) (l : List (Fin (n+1) → Fin (b+2))) (p q : state) : dfa.transFrom l p = q → q ∈ ((project m dfa).transFrom (l.map (fun f => remove_index m f)) ⟨[p], by exact List.nodup_singleton p⟩).val := by
  intro h
  induction l generalizing p
  case nil =>
    simp_all only [List.map_nil]
    simp only [DFAO.transFrom] at h
    simp only [NFA.transFrom, List.mem_singleton]
    exact h.symm
  case cons f fs ih =>
    simp[DFAO.transFrom] at h
    simp[NFA.transFrom, NFA.transList]
    specialize ih (dfa.transition f p) h
    have := NFA.transFrom_sublist (ps := ⟨[dfa.transition f p], by exact List.nodup_singleton (dfa.transition f p)⟩) (project m dfa) (List.map (fun f ↦ remove_index m f) fs) ⟨(((project m dfa).transition (remove_index m f) p).val).dedup, by apply List.nodup_dedup⟩
    apply this
    . simp only [List.cons_subset, List.mem_dedup, List.nil_subset, and_true]
      apply transition_project
    . assumption

theorem evalFrom_project [DecidableEq state](dfa : DFA (Fin (n + 1) → Fin (b+2)) state) (m : Fin (n + 1)) (l : List (Fin (n+1) → Fin (b+2))) (p : state) : dfa.evalFrom l p → (project m dfa).evalFrom (l.map (fun f => remove_index m f)) ⟨[p], by exact List.nodup_singleton p⟩ := by
  simp[NFA.evalFrom, DFAO.evalFrom]
  intro h
  use (DFAO.transFrom dfa l p)
  constructor
  . apply transFrom_project
    rfl
  . simp only [project]
    exact h

theorem eval_project [DecidableEq state](dfa : DFA (Fin (n + 1) → Fin (b+2)) state) (m : Fin (n + 1)) (l : List (Fin (n+1) → Fin (b+2))) : dfa.eval l → (project m dfa).eval (l.map (fun f => remove_index m f)) := by
  simp[NFA.eval, DFAO.eval]
  exact evalFrom_project dfa m l dfa.start

-- theorem project_transition' [DecidableEq state](dfa : DFA (Fin (n + 1) → Fin (b+2)) state) (m : Fin (n + 1)) (f : (Fin n → Fin (b+2))) (p q : state) : q ∈ ((project m dfa).transition f p).val → ∃ f₁, f = remove_index m f₁ ∧ dfa.transition f₁ p = q := by
--   simp only [project, List.mem_dedup, List.mem_map, FinEnum.mem_toList, true_and]
--   intro h
--   rcases h with ⟨a, h'⟩
--   use recover_value m a f
--   constructor
--   . simp only [recover_value, remove_insert]
--   . exact h'

theorem project_transition [DecidableEq state](dfa : DFA (Fin (n + 1) → Fin (b+2)) state) (m : Fin (n + 1)) (f : (Fin n → Fin (b+2))) (p q : state) : q ∈ ((project m dfa).transition f p).val → ∃ a, dfa.transition (recover_value m a f) p = q := by
  simp only [project, List.mem_dedup, List.mem_map, FinEnum.mem_toList, true_and, imp_self]

theorem project_transFrom [DecidableEq state](dfa : DFA (Fin (n + 1) → Fin (b+2)) state) (m : Fin (n + 1)) (l : List (Fin n → Fin (b+2))) (q : state) (states : ListND state) : q ∈ ((project m dfa).transFrom l states).val → ∃ p ∈ states.val, ∃ (l₁ : List (Fin (n+1) → Fin (b+2))) , l = l₁.map (remove_index m) ∧ dfa.transFrom l₁ p = q:= by
  intro h
  induction l generalizing states
  case nil =>
    simp only [NFA.transFrom, List.mem_singleton] at h
    simp_all only [List.nil_eq, List.map_eq_nil, exists_eq_left]
    use q
    simp only [h, DFAO.transFrom, and_self]
  case cons f fs ih =>
    simp [NFA.transFrom] at h
    specialize ih ((project m dfa).transList f states)
    specialize ih h
    rcases ih with ⟨p, h₁, l₁, h₂, h₃⟩
    -- Need to obtain a p' ∈ states.val from h₁. so p ∈ NFA.transList implies exists p', p  is in transitions.
    have h₄ := NFA.transList_backtrack (project m dfa) f p states h₁
    rcases h₄ with ⟨p', h₅, h₆⟩
    use p'
    constructor
    . exact h₅
    . have h₇ := project_transition dfa m f p' p h₆
      rcases h₇ with ⟨a, h₈⟩
      use (recover_value m a f) :: l₁
      constructor
      . simp only [recover_value, List.map_cons, remove_insert, List.cons.injEq, true_and]
        simp only [h₂, remove_index]
      . aesop

theorem project_evalFrom [DecidableEq state](dfa : DFA (Fin (n + 1) → Fin (b+2)) state) (m : Fin (n + 1)) (l : List (Fin n → Fin (b+2))) (states : ListND state) : (project m dfa).evalFrom l states → ∃ p ∈ states.val, ∃ (l₁ : List (Fin (n+1) → Fin (b+2))) , l = l₁.map (remove_index m) ∧ dfa.evalFrom l₁ p:= by
  intro h
  simp_all [NFA.evalFrom, DFAO.evalFrom]
  rcases h with ⟨p, h₁, h₂⟩
  have h₃ := project_transFrom dfa m l p states h₁
  rcases h₃ with ⟨p', h₄, h₅, h₆, h₇⟩
  use p'
  constructor
  . exact h₄
  . use h₅
    constructor
    . exact h₆
    . simp only [project] at h₂
      simp only [h₇, h₂]

theorem project_eval [DecidableEq state](dfa : DFA (Fin (n + 1) → Fin (b+2)) state) (m : Fin (n + 1)) (l : List (Fin n → Fin (b+2))) : (project m dfa).eval l → ∃ (l₁ : List (Fin (n+1) → Fin (b+2))) , l = l₁.map (remove_index m) ∧ dfa.eval l₁ := by
  simp[NFA.eval, DFAO.eval]
  have h := project_evalFrom dfa m l (project m dfa).start
  intro h₁
  specialize h h₁
  rcases h with ⟨p, h₂, l', h₄⟩
  simp[project] at h₂

  aesop?

theorem project_eval_iff [DecidableEq state](dfa : DFA (Fin (n + 1) → Fin (b+2)) state) (m : Fin (n + 1)) (l : List (Fin n → Fin (b+2))) : (project m dfa).eval l ↔ ∃ (l₁ : List (Fin (n+1) → Fin (b+2))) , l = l₁.map (remove_index m) ∧ dfa.eval l₁ := by
  constructor
  . exact project_eval dfa m l
  . intro h
    rcases h with ⟨l₁, h₁, h₂⟩
    have h₃ := eval_project dfa m l₁ h₂
    aesop


theorem project_acceptZero [DecidableEq state] (dfa : DFA (Fin (n + 1) → Fin (b+2)) state) (h: DFA.acceptZero dfa) (m : Fin (n + 1)) : NFA.acceptZero (project m dfa) := by
  simp[NFA.acceptZero]
  intro l h'
  have h₁ := project_eval_iff dfa m l
  have h₂ := h₁.mp h'
  rcases h₂ with ⟨l₁, h₃, h₄⟩
  rw[DFA.acceptZero] at h
  specialize h l₁ h₄
  intro k
  specialize h k
  have h₅ := project_eval_iff dfa m (padZeroes k l)
  apply h₅.mpr
  use (padZeroes k l₁)
  constructor
  . simp only [padZeroes, List.map_append, List.map_replicate]
    have: List.replicate k (remove_index m (fun _ ↦ 0 : Fin (n+1) → Fin (b+2))) ++ List.map (remove_index m) l₁ = List.replicate k (fun _ ↦ 0) ++ List.map (remove_index m) l₁ := by
      simp only [List.append_cancel_right_eq, List.replicate_inj, true_and]
      right
      simp only [remove_index]
      ext x
      simp only [Fin.removeNth, Fin.val_zero]
    simp only [h₃, this]
  . exact h

theorem project_fix_respectZero [Fintype state][DecidableEq state] (dfa : DFA (Fin (n + 1) → Fin (b+2)) state) (m : Fin (n + 1)) (h: dfa.respectZero) : (project m dfa).fixLeadingZeros.respectZero := by
  sorry

theorem project_correct [Fintype state] [DecidableEq state] (l : List ℕ) (hl : l.length = len)(m : Fin (len + 1)) (dfa : DFA (Fin (len +1) → Fin (b+2)) state) (h: dfa.acceptZero):
  ∃ (x : ℕ), dfa.eval (inputToBase (b+2) (by norm_num) (l.insertNth m x) (by simp_rw[← hl]; apply List.length_insertNth; omega)) ↔ (project m dfa).eval (padZeroes (Fintype.card (ListND state)) (inputToBase (b+2) (by omega) l hl)):= by
  sorry

-- Legacy

-- Auxilliary theorems for recover
-- theorem finLt (m : Fin (n+1)) (b : ℕ) : b < m.val → b < n := by omega

-- theorem finPred (m : Fin n) (a : Fin n) (h : a > m): a.val - 1 < n - 1 := by omega

-- -- Auxilliary function for project
-- def recover_value (m : Fin (n + 1)) (x: Fin (b+2)) (f: Fin n → Fin (b+2)) :
--  (Fin (n + 1) → Fin (b+2)) :=
--     fun i => if h1: i.val < m.val then f ⟨i.val, finLt m i.val h1⟩
--       else if h2: i.val > m.val then f ⟨i.val - 1, finPred m i h2⟩ else x

-- theorem project_transStep [DecidableEq state](dfa : DFA (Fin (n + 1) → Fin (b+2)) state) (m : Fin (n + 1)) (x : Fin (b+2)) (f : (Fin n → Fin (b+2))) (p q : state) : dfa.transFrom [(recover_value m x f)] p = q → q ∈ ((project m dfa).transFrom [f] ⟨[p], by exact List.nodup_singleton p⟩).val := by
--   simp only [DFAO.transFrom, NFA.transFrom, NFA.transList, project, List.bind_cons, List.bind_nil,
--     List.append_nil, List.dedup_idem, List.mem_dedup, List.mem_map, FinEnum.mem_toList, true_and]
--   intro a
--   subst a
--   simp_all only [exists_apply_eq_apply]

-- theorem project_transStep [DecidableEq state](dfa : DFA (Fin (n + 1) → Fin (b+2)) state) (m : Fin (n + 1)) (f : (Fin (n+1) → Fin (b+2))) (p q : state) : dfa.transFrom [f] p = q → q ∈ ((project m dfa).transFrom [remove_index m f] ⟨[p], by exact List.nodup_singleton p⟩).val := by
--   simp only [DFAO.transFrom, NFA.transFrom, NFA.transList, project, List.bind_cons, List.bind_nil,
--     List.append_nil, List.dedup_idem, List.mem_dedup, List.mem_map, FinEnum.mem_toList, true_and]
--   intro h
--   use f m
--   simp[recover_value, insert_remove]
--   exact h
