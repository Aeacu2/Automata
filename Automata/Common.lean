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

#eval (eqBase 2).eval (inputToBase 2 (by norm_num) [2, 2])
--Exists x, x = 0?
#eval (project (eqBase 2) (by norm_num) ⟨0, by norm_num⟩).eval [fun _ => 0]

def eqBase' (k: ℕ) (a b n : ℕ) (ha: a < n) (hb: b < n): DFA (Fin n → Fin k) (Fin 2) := {
  transition := fun f s => match s with
    | 0 => if (f ⟨a, ha⟩).val == f ⟨b, hb⟩ then 0 else 1
    | 1 => 1
  start := 0
  output := fun x => x == 0
}

#eval (eqBase' 2 0 1 2 (by norm_num) (by norm_num)).eval [fun _ => 0, fun _ => 1]
#eval (eqBase' 2 0 1 2 (by norm_num) (by norm_num)).eval [fun x => x, fun x => x]


def leBase (k: ℕ)  : DFA (Fin 2 → Fin k) (Fin 2) := {
  transition := fun f s => match s with
    | 0 => if (f 0).val <= (f 1).val then 0 else 1
    | 1 => 1
  start := 0
  output := fun x => x == 0
}

-- Exists x, not 0 <= x?
#eval (project ((leBase 2).negate) (by norm_num) ⟨1, by norm_num⟩).eval [fun _ => 0]

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

--Exists x, x + 1 = 0?
#eval (project (addBase 2) (by norm_num) ⟨0, by norm_num⟩).evalFrom [fun x => if x == 0 then 1 else 0] [0]
--Exists x, 1 + 1 = x?
#eval (project (addBase 2) (by norm_num) ⟨2, by norm_num⟩).evalFrom [fun _ => 1] [0]

--FIX: Exists x, 1 + 1 = x?
#eval (project (addBase 2) (by norm_num) ⟨2, by norm_num⟩).evalFrom [fun _ => 0, fun _ => 1] [0]

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

example (k : ℕ) (state : Fin 2) (f : Fin 2 → Fin k) :
  (eqBase k).transition f state = 0 →  state = 0 ∧ (f 0).val = f 1 := by
  simp[eqBase, DFAO.transition]
  split <;> simp

theorem eqBase_trans_zero (k : ℕ) (state : Fin 2) (f : Fin 2 → Fin k) :
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

theorem equal_if_eqBase_aux_aux (b : ℕ) (input: List (Fin 2 → Fin b)):
  (eqBase b).transFrom input 0 = 0 → (∀ f ∈ input, (f 0).val = f 1) := by
  intro h
  exact (eqBase_transFrom_zero b 0 input).mp h |>.2
  -- exact this.2

theorem equal_if_eqBase_aux (b : ℕ) (input: List (Fin 2 → Fin b)):
  (eqBase b).evalFrom input 0 → (∀ f ∈ input, (f 0).val = f 1) := by
  intro h
  have:= equal_if_eqBase_aux_aux b input
  apply this
  simp[DFAO.evalFrom, DFAO.output, eqBase] at h
  apply h










theorem eqBase_if_equal (b : ℕ) (m n : ℕ) (hb: b > 1):
  m = n → (eqBase b).eval (inputToBase b hb [m, n]) := by
  sorry
