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

theorem project_transition [DecidableEq state](dfa : DFA (Fin (n + 1) → Fin (b+2)) state) (m : Fin (n + 1)) (f : (Fin (n+1) → Fin (b+2))) (p q : state) : dfa.transition f p = q → q ∈ ((project m dfa).transition (remove_index m f) p).val := by
  simp only [project, List.mem_dedup, List.mem_map, FinEnum.mem_toList, true_and]
  intro h
  use f m
  simp[recover_value, insert_remove]
  exact h

theorem project_transition' [DecidableEq state](dfa : DFA (Fin (n + 1) → Fin (b+2)) state) (m : Fin (n + 1)) (f : (Fin (n+1) → Fin (b+2))) (p : state) : dfa.transition f p ∈ ((project m dfa).transition (remove_index m f) p).val := by
  simp only [project, List.mem_dedup, List.mem_map, FinEnum.mem_toList, true_and]
  use f m
  simp[recover_value, insert_remove]


theorem project_transFrom [DecidableEq state](dfa : DFA (Fin (n + 1) → Fin (b+2)) state) (m : Fin (n + 1)) (l : List (Fin (n+1) → Fin (b+2))) (p q : state) : dfa.transFrom l p = q → q ∈ ((project m dfa).transFrom (l.map (fun f => remove_index m f)) ⟨[p], by exact List.nodup_singleton p⟩).val := by
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
      apply project_transition'
    . assumption

theorem project_evalFrom [DecidableEq state](dfa : DFA (Fin (n + 1) → Fin (b+2)) state) (m : Fin (n + 1)) (l : List (Fin (n+1) → Fin (b+2))) (p : state) : dfa.evalFrom l p → (project m dfa).evalFrom (l.map (fun f => remove_index m f)) ⟨[p], by exact List.nodup_singleton p⟩ := by
  simp[NFA.evalFrom, DFAO.evalFrom]
  intro h
  use (DFAO.transFrom dfa l p)
  constructor
  . apply project_transFrom
    rfl
  . simp only [project]
    exact h

theorem project_eval [DecidableEq state](dfa : DFA (Fin (n + 1) → Fin (b+2)) state) (m : Fin (n + 1)) (l : List (Fin (n+1) → Fin (b+2))) : dfa.eval l → (project m dfa).eval (l.map (fun f => remove_index m f)) := by
  simp[NFA.eval, DFAO.eval]
  exact project_evalFrom dfa m l dfa.start


theorem project_acceptZero [DecidableEq state] (dfa : DFA (Fin (n + 1) → Fin (b+2)) state) (h: DFA.respectZero dfa) (m : Fin (n + 1)) : NFA.acceptZero (project m dfa) := by
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
