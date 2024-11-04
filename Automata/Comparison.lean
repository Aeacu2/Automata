import Mathlib.Tactic
import Mathlib.Data.List.Basic
import Automata.DFA
import Automata.NFA
import Automata.Input
import Mathlib.Data.Nat.Digits


def ltBase (k: ℕ)  : DFA (Fin 2 → Fin k) (Fin 3) := {
  transition := fun f s => match s with
    | 0 => if (f 0).val < (f 1).val then 1 else if (f 0).val = (f 1).val then 0 else 2
    | 1 => 1
    | 2 => 2
  start := 0
  output := fun x => x == 1
}

/-
Try to prove ltBase is correct

1. DFA accepts iff f 0 < f 1 eventually, before which f 0 = f 1.
2. m < n iff inputToBase has f 0 < f 1 eventually, before which f 0 = f 1.

-/

theorem ltBase_iff_ltInput (k: ℕ) (l: List (Fin 2 → Fin k)) (s: Fin 3) :
  (ltBase k).eval l ↔ ∃ i, ∀ (hi: i < l.length), (l[i] 0).val < (l[i] 1).val
    ∧ ∀ j, ∀ (hj: j < i), (l[j] 0).val = (l[j] 1).val:= by sorry

theorem ltInput_iff_lt (m n k: ℕ) (hk: 2 ≤ k) :
  m < n ↔ ∃ i, ∀ (hi: i < (inputToBase k hk [m, n]).length), ((inputToBase k hk [m, n])[i] ⟨0, by simp⟩).val < ((inputToBase k hk [m, n])[i] ⟨1, by simp⟩).val
    ∧ ∀ j, ∀ (hj: j < i), ((inputToBase k hk [m, n])[j] ⟨0, by simp⟩).val = ((inputToBase k hk [m, n])[j] ⟨1, by simp⟩).val:= by sorry
