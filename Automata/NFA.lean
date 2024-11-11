import Mathlib.Tactic
import Mathlib.Data.List.Basic
import Automata.DFA
import Mathlib.Data.List.Defs
import Mathlib.Data.FinEnum

open Computability

-- A type for Lists with no duplicates, for synthesizing [Fintype ListND] state from [Fintype state]
abbrev ListND (α : Type) := {l : List α // l.Nodup}

structure NFA (α state : Type) :=
  (transition : α → state → ListND state)
  (start : ListND state)
  (output : state → Bool)

def NFA.transList (nfa : NFA α state) (a : α) (qs : ListND state) [DecidableEq state] : ListND state :=
  ⟨(qs.val.bind fun q => nfa.transition a q).dedup, (by apply List.nodup_dedup)⟩

def NFA.evalFrom (nfa : NFA α state) (s : List α) (qs : ListND state) [DecidableEq state] : Bool :=
  match s with
    | [] => qs.val.any nfa.output
    | a::as => NFA.evalFrom nfa as (NFA.transList nfa a qs)

def NFA.eval (nfa : NFA α state) (s : List α) [DecidableEq state] : Bool :=
  NFA.evalFrom nfa s nfa.start

def NFA.toDFA (nfa : NFA α state) [DecidableEq state] : DFA α (ListND state) where
  transition := fun a qs => NFA.transList nfa a qs
  start := nfa.start
  output := fun qs => qs.val.any nfa.output

theorem NFA.toDFA_transition (nfa : NFA α state) (a : α) (qs : ListND state) [DecidableEq state]:
  (nfa.toDFA).transition a qs = NFA.transList nfa a qs := by rfl

theorem NFA.toDFA_evalFrom (nfa : NFA α state) (x : List α) (qs: ListND state) [DecidableEq state]:
  (nfa.toDFA).evalFrom x qs = nfa.evalFrom x qs := by
  induction x generalizing qs
  case nil =>
    simp only [NFA.evalFrom, DFAO.evalFrom, DFAO.transFrom, NFA.toDFA]
  case cons y ys ih =>
    simp only [NFA.evalFrom, DFAO.evalFrom, NFA.toDFA_transition]
    exact ih (nfa.transList y qs)

theorem NFA.toDFA_eval (nfa : NFA α state) (s : List α) [DecidableEq state]
  : (nfa.toDFA).eval s = nfa.eval s := NFA.toDFA_evalFrom nfa s nfa.start


theorem NFA.pumping_lemma_evalFrom [Fintype state] [DecidableEq state] {nfa : NFA α state} {x : List α} {qs : ListND state}(hx : nfa.evalFrom x qs)(hlen : Fintype.card (ListND state) ≤ x.length) :
    ∃ a b c, x = a ++ b ++ c ∧ a.length + b.length ≤ Fintype.card (ListND state) ∧ b ≠ []
      ∧ ∀ y ∈ ({a} * {b}∗ * {c} : Language α), nfa.evalFrom y qs := by
  rw [← toDFA_evalFrom] at hx
  obtain ⟨a, b, c, hxabc, hablen, hne, hy⟩ := nfa.toDFA.pumping_lemma_evalFrom hx hlen
  use a, b, c
  constructor
  . exact hxabc
  constructor
  . exact hablen
  constructor
  . exact hne
  intro y h
  specialize hy y h
  rwa [← toDFA_evalFrom nfa y qs]

theorem NFA.pumping_lemma_eval [Fintype state] [DecidableEq state] {nfa : NFA α state} {x : List α}(hx : nfa.eval x)(hlen : Fintype.card (ListND state) ≤ x.length) :
    ∃ a b c, x = a ++ b ++ c ∧ a.length + b.length ≤ Fintype.card (ListND state) ∧ b ≠ []
      ∧ ∀ y ∈ ({a} * {b}∗ * {c} : Language α), nfa.eval y := by
  exact pumping_lemma_evalFrom hx hlen


