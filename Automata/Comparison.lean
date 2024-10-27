import Mathlib.Tactic
import Mathlib.Data.List.Basic
import Automata.DFA
import Automata.NFA
import Automata.Input
import Mathlib.Data.Nat.Digits


def leBase (k: ℕ)  : DFA (Fin 2 → Fin k) (Fin 2) := {
  transition := fun f s => match s with
    | 0 => if (f 0).val <= (f 1).val then 0 else 1
    | 1 => 1
  start := 0
  output := fun x => x == 0
}
