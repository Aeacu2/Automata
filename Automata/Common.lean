import Mathlib.Tactic
import Mathlib.Data.List.Basic
import Automata.DFA
import Automata.NFA
import Automata.Input
import Mathlib.Data.Nat.Digits

def thueMorse : DFAO (Fin 2) (Fin 2) (Fin 2) := {
  transition := fun a s => a + s
  start := 0
  output := fun x => x
}

def thueMorse0 : DFA (Fin 2) (Fin 2) := thueMorse.toDFA 0

def thueMorse1 : DFA (Fin 2) (Fin 2) := thueMorse.toDFA 1

def trueDFA: DFA (Fin 0) (Fin 1) := {
  transition := fun _ s => s
  start := 0
  output := fun _ => true
}

def falseDFA: DFA (Fin 0) (Fin 1) := {
  transition := fun _ s => s
  start := 0
  output := fun _ => false
}

def eqBase (k: ℕ) : DFA (Fin 2 → Fin k) (Fin 2) := {
  transition := fun f s => match s with
    | 0 => if (f 0).val = f 1 then 0 else 1
    | 1 => 1
  start := 0
  output := fun x => x == 0
}

def eqBase' (k: ℕ) (a b n : ℕ) (ha: a < n) (hb: b < n): DFA (Fin n → Fin k) (Fin 2) := {
  transition := fun f s => match s with
    | 0 => if (f ⟨a, ha⟩).val == f ⟨b, hb⟩ then 0 else 1
    | 1 => 1
  start := 0
  output := fun x => x == 0
}

/- Try to prove eqBase is correct

1. DFA accepts iff f 0 = f 1 for all f ∈ input
2. input natural numbers are equal iff f 0 = f 1 for all f ∈ input

-/
theorem eqBase_if_equal_aux (b : ℕ) (input: List (Fin 2 → Fin b)):
  (∀ f ∈ input, (f 0).val = f 1) → (eqBase b).evalFrom input 0 := by
  intro h
  induction input
  case nil =>
    simp[eqBase, DFAO.evalFrom, DFAO.transFrom]
  case cons f fs ih =>
    have h1 := h f
    simp only [List.mem_cons, true_or, Fin.isValue, true_implies] at h1
    simp only [DFAO.evalFrom, DFAO.transFrom, Fin.isValue]
    have: ((eqBase b).transition f 0) = 0 := by
      simp only [eqBase, Fin.isValue, beq_iff_eq, h1, ↓reduceIte]
    rw[this]
    apply ih
    intro f' hf'
    apply h
    simp only [List.mem_cons, or_true, hf']

theorem eqBase_trans_zero (k : ℕ) (state : Fin 2) (f : Fin 2 → Fin k) :
  (eqBase k).transition f state = 0 ↔ state = 0 ∧ (f 0).val = f 1 := by
  simp only [eqBase, Fin.isValue, beq_iff_eq]
  split <;> simp

/-
example (k : ℕ) (state : Fin 2) (f : Fin 2 → Fin k) :
  (eqBase k).transition f state = 0 ↔ state = 0 ∧ (f 0).val == f 1 := by
  constructor
  intro h1
  simp[eqBase] at h1
  constructor
  . by_contra h
    have: state = 1 := by exact Fin.eq_one_of_neq_zero state h
    simp[this] at h1
  . simp only [Fin.isValue, beq_iff_eq]
    have: ¬state = 0 → state = 1 := by intro hns; exact Fin.eq_one_of_neq_zero state hns
    have: state = 0 ∨ state = 1 := by tauto
    rcases this with hs | hs
    . simp only [hs, Fin.isValue, ite_eq_then, one_ne_zero, imp_false, Decidable.not_not] at h1
      exact h1
    . simp only [hs, Fin.isValue, one_ne_zero] at h1
  intro h
  rcases h with ⟨h1, h2⟩
  simp only [Fin.isValue, beq_iff_eq] at h2
  simp only [eqBase, Fin.isValue, beq_iff_eq, ↓reduceIte, h1, h2]
-/

theorem eqBase_transFrom_zero (k : ℕ) (state: Fin 2) (l : List (Fin 2 → Fin k)) :
  (eqBase k).transFrom l state = 0 ↔ state = 0 ∧ ∀ f ∈ l, (f 0).val = f 1 := by
  induction l generalizing state
  case nil =>
    simp[eqBase, DFAO.transFrom]
  case cons f fs ih =>
    simp[DFAO.transFrom]
    specialize ih ((eqBase k).transition f state)
    constructor
    . intro h
      have:= ih.mp h
      rcases this with ⟨h1, h2⟩
      have:= (eqBase_trans_zero k state f).mp h1
      rcases this with ⟨h3, h4⟩
      constructor
      . exact h3
      . constructor
        . simp only [Fin.isValue, beq_iff_eq] at h4
          exact h4
        . exact h2
    . intro h
      rcases h with ⟨h1, h2, h3⟩
      apply ih.mpr
      constructor
      . apply (eqBase_trans_zero k state f).mpr
        constructor
        . exact h1
        . simp only [Fin.isValue, beq_iff_eq]
          exact h2
      . exact h3

theorem eqInput_if_eqBase_aux (b : ℕ) (input: List (Fin 2 → Fin b)):
  (eqBase b).transFrom input 0 = 0 → (∀ f ∈ input, (f 0).val = f 1) := by
  intro h
  exact (eqBase_transFrom_zero b 0 input).mp h |>.2

theorem eqInput_if_eqBase (b : ℕ) (input: List (Fin 2 → Fin b)):
  (eqBase b).evalFrom input 0 → (∀ f ∈ input, (f 0).val = f 1) := by
  intro h
  have:= eqInput_if_eqBase_aux b input
  apply this
  simp[DFAO.evalFrom, DFAO.output, eqBase] at h
  apply h

theorem eqBase_iff_eqInput (b : ℕ) (input: List (Fin 2 → Fin b)):
  (eqBase b).eval input ↔ (∀ f ∈ input, (f 0).val = f 1) := by
  constructor
  . apply eqInput_if_eqBase b input
  . apply eqBase_if_equal_aux b input

theorem eqInput_if_equal (m n b : ℕ) (hb : b > 1) :
  m = n →  ∀ f ∈ inputToBase b hb [m, n], (f ⟨0, by simp⟩).val = f ⟨1, by simp⟩ := by
    intro h f hf
    --rw[h] at *
    have digitsEq : toBase b m = toBase b n := by rw[h]
    have lenEq : (toBase b m).length = (toBase b n).length := by rw[digitsEq]
    have mapTo : mapToBase b [m, n] = [toBase b m, toBase b n] := by rfl
    have mapLen : (mapToBase b [m, n]).length = 2 :=
    mapToBase_length b [m, n]
    have lenEqMap : ((mapToBase b [m, n])[0]).length = ((mapToBase b [m, n])[1]).length := by
      simp only [mapTo, List.getElem_cons_zero, lenEq, List.getElem_cons_succ]
    have maxLenEq : maxLen (mapToBase b [m, n]) = (toBase b m).length := by
      simp only [maxLen, h, zero_le, max_eq_left, max_self]
    have stretchLenLen_aux : (stretchLen (mapToBase b [m, n])).length = (mapToBase b [m, n]).length :=
      stretchLen_length (mapToBase b [m, n])
    have stretchLenLen : (stretchLen (mapToBase b [m, n])).length = 2 := by
      simp only [stretchLenLen_aux, mapLen]
    have stretchLenEq: (stretchLen (mapToBase b [m, n]))[0] =
    (stretchLen (mapToBase b [m, n]))[1] := by
      simp only [stretchLen, List.map, List.getElem_cons_zero, List.getElem_cons_succ, h]

    have inputEqZip : zipToAlphabetFin (maxLen (mapToBase b [m, n])) 2 (stretchLen (mapToBase b [m, n])) (by
      apply stretchLen_of_mapToBase_lt_base
      exact hb
    ) (by simp only [stretchLenLen, mapLen]) (by
      intro x hx
      simp[List.mem_iff_get] at hx
      rcases hx with ⟨s, hs, rfl⟩
      have: s.val = 0 ∨ s.val = 1 := by
        have:= s.isLt
        omega
      rcases this with hs | hs
      . apply stretchLen_uniform
        simp[hs]
        apply List.getElem_mem
      . apply stretchLen_uniform
        simp[hs]
        apply List.getElem_mem
    ) = inputToBase b hb [m, n] := by
      simp[inputToBase]

    have zipMatch: ∀ f ∈ zipToAlphabetFin (maxLen (mapToBase b [m, n])) 2 (stretchLen (mapToBase b [m, n])) (by
      apply stretchLen_of_mapToBase_lt_base
      exact hb
    ) (by simp only [stretchLenLen, mapLen]) (by
      intro x hx
      simp[List.mem_iff_get] at hx
      rcases hx with ⟨s, hs, rfl⟩
      have: s.val = 0 ∨ s.val = 1 := by
        have:= s.isLt
        omega
      rcases this with hs | hs
      . apply stretchLen_uniform
        simp[hs]
        apply List.getElem_mem
      . apply stretchLen_uniform
        simp[hs]
        apply List.getElem_mem
    ), (f 0).val = f 1 := by
      intro f hf
      sorry
    rw[← inputEqZip] at hf
    apply zipMatch f hf







theorem eqBase_iff_equal (b : ℕ) (m n : ℕ) (hb: b > 1):
  m = n → (eqBase b).eval (inputToBase b hb [m, n]) := by
  sorry

def leBase (k: ℕ)  : DFA (Fin 2 → Fin k) (Fin 2) := {
  transition := fun f s => match s with
    | 0 => if (f 0).val <= (f 1).val then 0 else 1
    | 1 => 1
  start := 0
  output := fun x => x == 0
}

def addBase (k: ℕ) : DFA (Fin 3 → Fin k) (Fin 3) := {
  transition := fun f s => match s with
    | 0 => if (f 0).val + f 1 == f 2 then 0 else
      if (f 0).val + f 1 + 1 == f 2 then 1
      else 2
    | 1 => if (f 0).val + f 1 + 1 == f 2 + k then 1 else
      if (f 0).val + f 1 == f 2 + k then 0
      else 2
    | 2 => 2
  start := 0
  output := fun x => x == 0
}
