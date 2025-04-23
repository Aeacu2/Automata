import Mathlib.Tactic
import Mathlib.Data.List.Basic
import Automata.DFA
import Automata.NFA
import Automata.Input_new
import Mathlib.Data.Nat.Digits

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
