import Mathlib.Tactic
import Mathlib.Data.List.Basic
import Automata.DFA
import Automata.NFA
import Mathlib.Data.Nat.Digits


def thueMorse : DFAO (Fin 1 → Fin 2) (Fin 2) (Fin 2) := {
  transition := fun a s => a 0 + s
  start := 0
  output := fun x => x
}

def thueMorse0 : DFA (Fin 1 → Fin 2) (Fin 2) := thueMorse.toDFA 0

def thueMorse1 : DFA (Fin 1 → Fin 2) (Fin 2) := thueMorse.toDFA 1
