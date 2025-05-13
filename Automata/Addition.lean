import Mathlib.Tactic
import Mathlib.Data.List.Basic
import Automata.DFA
import Automata.NFA
import Mathlib.Data.Nat.Digits

def addBase (b m: ℕ) (i j k : Fin m): DFA (Fin m → Fin (b+2)) (Fin 3) := {
  transition := fun f s => match s with
    | 0 => if (f i).val + f j == f k then 0 else
      if (f i).val + f j + 1 == f k then 1
      else 2
    | 1 => if (f i).val + f j + 1 == f k + b then 1 else
      if (f i).val + f j == f k + b then 0
      else 2
    | 2 => 2
  start := 0
  output := fun x => x == 0
}
