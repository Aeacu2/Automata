import Mathlib.Tactic
import Mathlib.Data.List.Basic
import Automata.DFA_Fin
import Automata.Input_Fin

def eqBase (k: ℕ) : DFA (Fin 2 → Fin k) (Fin 2) := {
  transition := fun f s => match s with
    | 0 => if (f 0).val = f 1 then 0 else 1
    | 1 => 1
  start := 0
  output := fun x => x == 0
}

theorem eqBase_if_equal_aux (b : ℕ) (f: Fin n → Fin 2 → Fin b) :
  (∀ (x : Fin n), ((f x) 0).val = (f x) 1) → (eqBase b).evalFrom f 0 := by
  intro h
  induction n
  case zero =>
    simp_all only [Fin.isValue, IsEmpty.forall_iff]
    rfl
  case succ n ih =>
    simp[DFAO.evalFrom, DFAO.transFrom]
    have : ((eqBase b).transition (f 0) 0) = 0 := by
      simp[eqBase]; exact h 0
    rw[this]
    specialize ih (Fin.tail f)
    apply ih
    intro x
    apply h

example (b : ℕ) (f: Fin n → Fin 2 → Fin b) :
  (∀ (x : ℕ) (hx: x < n), ((f ⟨x, hx⟩) 0).val = (f ⟨x, hx⟩) 1) → (eqBase b).evalFrom f 0 := by
  intro h
  induction n
  case zero =>
    simp_all only [Fin.isValue, IsEmpty.forall_iff]
    rfl
  case succ n ih =>
    simp[DFAO.evalFrom, DFAO.transFrom]
    have : ((eqBase b).transition (f 0) 0) = 0 := by
      simp[eqBase]; apply h 0
    rw[this]
    specialize ih (Fin.tail f)
    apply ih
    intro x
    specialize h (x + 1)
    intro hxn
    simp[Fin.tail]
    apply h


theorem eqBase_trans_zero (k : ℕ) (state : Fin 2) (f : Fin 2 → Fin k) :
  (eqBase k).transition f state = 0 ↔ state = 0 ∧ (f 0).val = f 1 := by
  simp only [eqBase, Fin.isValue, beq_iff_eq]
  split <;> simp

theorem eqBase_transFrom_zero (k : ℕ) (state: Fin 2) (f : Fin n → Fin 2 → Fin k) :
  (eqBase k).transFrom f state = 0 ↔ state = 0 ∧ ∀ (x : Fin n), ((f x) 0).val = f x 1 := by
  induction n generalizing state
  case zero =>
    simp_all only [Fin.isValue, IsEmpty.forall_iff, and_true]
    rfl
  case succ n ih =>
    simp[DFAO.transFrom]
    specialize ih ((eqBase k).transition (f 0) state) (Fin.tail f)
    rw[ih]
    constructor
    . intro h
      rcases h with ⟨h1, h2⟩
      have:= (eqBase_trans_zero k state (f 0)).mp h1
      rcases this with ⟨rfl, h⟩
      simp only [Fin.isValue, true_and]
      intro x
      by_cases hx: x = 0 -- x.val = 0 also won't work
      . rw[hx]
        exact h
      . specialize h2 ⟨x.val - 1, by omega⟩
        simp[Fin.tail] at h2
        have : x.val ≠ 0 := by
          intro h'
          apply hx
          exact Eq.symm (Fin.eq_of_val_eq (id (Eq.symm h')))
        -- cases' x with x
        -- .
        -- doesn't work have : ¬ x.val = 0 := by omega
        have h3: x.val - 1 + 1 = x.val := by omega
        simp_all only [Fin.isValue, true_and, Fin.eta, ne_eq]
    . sorry
