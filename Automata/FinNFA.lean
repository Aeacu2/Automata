import Mathlib.Tactic
import Mathlib.Data.FinEnum
import Mathlib.Data.List.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Logic.IsEmpty
import Mathlib.Data.Finset.Card
import Automata.FinDFA

open Std

variable {α β state1 state2 state : Type} [FinEnum α] [FinEnum β] [FinEnum state1] [FinEnum state2] [FinEnum state]

structure NFA (α state : Type ) [FinEnum α] [FinEnum state]:=
  (transition : α → state → List state)
  (start : List state)
  (accept : state → Bool)
deriving Inhabited, DecidableEq

def n : NFA (Fin 2) (Fin 3) where
  transition := fun a s => [s+1, s+a]
  start := [0]
  accept := fun x => x == 2

def NFA.step (nfa : NFA α state) (a : α) (qs : List state) : List state :=
  (qs.bind fun q => nfa.transition a q).eraseDups

def NFA.evalFrom {α state : Type} [FinEnum α] [FinEnum state] (nfa : NFA α state) (s : List α) (qs : List state) : Bool :=
  match s with
    | [] => qs.any nfa.accept
    | a::as => NFA.evalFrom nfa as (NFA.step nfa a qs)

def NFA.eval {α state : Type} [FinEnum α] [FinEnum state] (nfa : NFA α state) (s : List α) : Bool :=
  NFA.evalFrom nfa s nfa.start

#eval NFA.eval n [0]
#eval NFA.eval n [0, 0]

def NFA.toDFA {α state : Type} [FinEnum α] [FinEnum state] (nfa : NFA α state) : DFA α (Finset state) where
  transition := fun a qs => {q' | ∃ q ∈ qs, q' ∈ nfa.transition a q}.toFinset
  start := nfa.start.toFinset
  accept := fun qs => ∃ q ∈ qs, nfa.accept q

#eval (n.toDFA).eval [0, 0]

theorem NFA.toDFA_correct {α state : Type} [FinEnum α] [FinEnum state] (nfa : NFA α state) (s : List α) (q: state) :
  (nfa.toDFA).evalFrom s {q} = nfa.evalFrom s [q] := by
  induction s generalizing q
  case nil =>
    simp [NFA.evalFrom, DFA.evalFrom, NFA.toDFA]
  case cons x xs ih =>
    simp [ih, NFA.evalFrom, DFA.evalFrom, NFA.toDFA]

    done
