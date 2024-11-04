import Mathlib.Tactic
import Mathlib.Data.List.Basic
import Automata.DFA
import Mathlib.Data.FinEnum

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

theorem NFA.toDFA_evalFrom (nfa : NFA α state) (s : List α) (qs: List state) [BEq state]:
  (nfa.toDFA).evalFrom s qs = nfa.evalFrom s qs := by
  induction s generalizing qs
  case nil =>
    simp only [NFA.evalFrom, DFAO.evalFrom, DFAO.transFrom, NFA.toDFA]
  case cons x xs ih =>
    simp only [NFA.evalFrom, DFAO.evalFrom, NFA.toDFA_transition]
    exact ih (nfa.transList x qs)

theorem NFA.toDFA_eval (nfa : NFA α state) (s : List α) [BEq state]
  : (nfa.toDFA).eval s = nfa.eval s := NFA.toDFA_evalFrom nfa s nfa.start


/- USELESS CODE
def project' (dfa : DFA (β × α) state) [BEq state] [FinEnum β] : NFA α state := {
  transition := fun a q => (List.map (fun (x : β) => dfa.transition (x, a) q) (FinEnum.toList β))
  start := [dfa.start]
  output := dfa.output
}
-/
