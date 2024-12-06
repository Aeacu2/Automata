import Mathlib.Tactic
import Automata.DFA
import Automata.NFA
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

def DFA.acceptZero (dfa : DFA (Fin n → Fin (b+2)) state) : Prop := ∀ (x : List (Fin n → Fin (b+2))), dfa.eval x → (∀ m, dfa.eval (padZeroes m x))

def NFA.acceptZero [DecidableEq state] (nfa : NFA (Fin n → Fin (b+2)) state) : Prop := ∀ (x : List (Fin n → Fin (b+2))), nfa.eval x → (∀ m, nfa.eval (padZeroes m x))

theorem equality_acceptZero : (eqBase (b + 2) l m n).acceptZero := by
  rw[DFA.acceptZero]
  intro x h c
  rw[padZeroes]
  rw[DFAO.eval, DFAO.evalFrom, DFAO.transFrom_of_append]
  sorry
