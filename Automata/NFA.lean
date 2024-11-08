import Mathlib.Tactic
import Mathlib.Data.List.Basic
import Automata.DFA
import Mathlib.Data.FinEnum

open Computability

structure NFA (α state : Type) :=
  (transition : α → state → List state)
  (start : List state)
  (output : state → Bool)

def NFA.transList (nfa : NFA α state) (a : α) (qs : List state) [BEq state] : List state :=
  (qs.bind fun q => nfa.transition a q)

def NFA.evalFrom (nfa : NFA α state) (s : List α) (qs : List state) [BEq state] : Bool :=
  match s with
    | [] => qs.any nfa.output
    | a::as => NFA.evalFrom nfa as (NFA.transList nfa a qs)

def NFA.eval (nfa : NFA α state) (s : List α) [BEq state] : Bool :=
  NFA.evalFrom nfa s nfa.start

def NFA.toDFA (nfa : NFA α state) [BEq state] : DFA α (List state) where
  transition := fun a qs => NFA.transList nfa a qs
  start := nfa.start
  output := fun qs => qs.any nfa.output

theorem NFA.toDFA_transition (nfa : NFA α state) (a : α) (qs : List state) [BEq state]:
  (nfa.toDFA).transition a qs = NFA.transList nfa a qs := by rfl

theorem NFA.toDFA_evalFrom (nfa : NFA α state) (x : List α) (qs: List state) [BEq state]:
  (nfa.toDFA).evalFrom x qs = nfa.evalFrom x qs := by
  induction x generalizing qs
  case nil =>
    simp only [NFA.evalFrom, DFAO.evalFrom, DFAO.transFrom, NFA.toDFA]
  case cons y ys ih =>
    simp only [NFA.evalFrom, DFAO.evalFrom, NFA.toDFA_transition]
    exact ih (nfa.transList y qs)

theorem NFA.toDFA_eval (nfa : NFA α state) (s : List α) [BEq state]
  : (nfa.toDFA).eval s = nfa.eval s := NFA.toDFA_evalFrom nfa s nfa.start

/- TODO
theorem NFA.pumping_lemma_evalFrom [Fintype state] [BEq state] {nfa : NFA α state} {x : List α} {qs : List state}(hx : nfa.evalFrom x qs)(hlen : Fintype.card state ≤ x.length) :
    ∃ a b c, x = a ++ b ++ c ∧ a.length + b.length ≤ Fintype.card state ∧ b ≠ []
      ∧ ∀ y ∈ ({a} * {b}∗ * {c} : Language α), nfa.evalFrom y qs := by
  rw [← toDFA_evalFrom] at hx
  exact nfa.toDFA.pumping_lemma_evalFrom hx hlen
  done
-/
