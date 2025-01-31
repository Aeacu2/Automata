import Mathlib.Tactic
import Automata.DFA

-- Operations on DFAs: negation, intersection, union
def DFA.negate (dfa: DFA α state) : DFA α state := {
  transition := dfa.transition
  start := dfa.start
  output := fun x =>  ! dfa.output x
}

def DFA.intersection (dfa1 : DFA α state1) (dfa2 : DFA α state2) : DFA α (state1 × state2) := {
  transition := fun a q => ⟨dfa1.transition a q.1, dfa2.transition a q.2⟩,
  start := (dfa1.start, dfa2.start),
  output := fun (q1, q2) => dfa1.output q1 && dfa2.output q2
}

def DFA.union  (dfa1 : DFA α state1) (dfa2 : DFA α state2) : DFA α (state1 × state2) := {
  transition := fun a q => ⟨dfa1.transition a q.1, dfa2.transition a q.2⟩,
  start := (dfa1.start, dfa2.start),
  output := fun (q1, q2) => dfa1.output q1 || dfa2.output q2
}

theorem DFA.negate_output (dfa : DFA α state) (q : state) :
  (dfa.negate).output q = ! dfa.output q := by rfl

theorem DFA.negate_transition (dfa : DFA α state) :
  (dfa.negate).transition = dfa.transition := by rfl

theorem DFA.negate_transFrom (dfa : DFA α state) (s : List α) (q : state) :
  (dfa.negate).transFrom s q = dfa.transFrom s q := by
  induction s generalizing q
  case nil => rfl
  case cons a s ih =>
    rw [DFAO.transFrom, DFAO.transFrom, DFA.negate_transition, ih]

theorem DFA.negate_evalFrom (dfa : DFA α state) (s : List α) (q : state) :
  (dfa.negate).evalFrom s q = ! dfa.evalFrom s q := by
  simp[DFAO.evalFrom, DFA.negate_transFrom, DFA.negate_output]

theorem DFA.negate_eval (dfa : DFA α state) (s : List α) :
  (dfa.negate).eval s = ! dfa.eval s := by
  exact DFA.negate_evalFrom dfa s dfa.start

theorem DFA.intersection_output (dfa1 : DFA α state1) (dfa2 : DFA α state2) (q1 : state1) (q2 : state2) :
  (dfa1.intersection dfa2).output (q1, q2) = (dfa1.output q1 && dfa2.output q2) := by rfl

theorem DFA.intersection_transition (dfa1 : DFA α state1) (dfa2 : DFA α state2) :
  (dfa1.intersection dfa2).transition = fun a q => ⟨dfa1.transition a q.1, dfa2.transition a q.2⟩ := by rfl

theorem DFA.intersection_transFrom (dfa1 : DFA α state1) (dfa2 : DFA α state2) (s : List α) (q1 : state1) (q2 : state2) :
  (dfa1.intersection dfa2).transFrom s (q1, q2) = (dfa1.transFrom s q1, dfa2.transFrom s q2) := by
  induction s generalizing q1 q2
  case nil => rfl
  case cons a s ih =>
    simp [DFAO.transFrom, DFA.intersection_transition, ih]

theorem DFA.intersection_evalFrom (dfa1 : DFA α state1) (dfa2 : DFA α state2) (s : List α) (q1 : state1) (q2 : state2) :
  (dfa1.intersection dfa2).evalFrom s (q1, q2) = (dfa1.evalFrom s q1 && dfa2.evalFrom s q2) := by
  simp[DFAO.evalFrom, DFA.intersection_transFrom, DFA.intersection_output]

theorem DFA.intersection_eval (dfa1 : DFA α state1) (dfa2 : DFA α state2)
  (s : List α) : (dfa1.intersection dfa2).eval s = (dfa1.eval s && dfa2.eval s) := by
  exact DFA.intersection_evalFrom dfa1 dfa2 s dfa1.start dfa2.start

theorem DFA.union_output (dfa1 : DFA α state1) (dfa2 : DFA α state2) (q1 : state1) (q2 : state2) :
  (dfa1.union dfa2).output (q1, q2) = (dfa1.output q1 || dfa2.output q2) := by rfl

theorem DFA.union_transition (dfa1 : DFA α state1) (dfa2 : DFA α state2) :
  (dfa1.union dfa2).transition = fun a q => ⟨dfa1.transition a q.1, dfa2.transition a q.2⟩ := by rfl

theorem DFA.union_transFrom (dfa1 : DFA α state1) (dfa2 : DFA α state2) (s : List α) (q1 : state1) (q2 : state2) :
  (dfa1.union dfa2).transFrom s (q1, q2) = (dfa1.transFrom s q1, dfa2.transFrom s q2) := by
  induction s generalizing q1 q2
  case nil => rfl
  case cons a s ih =>
    simp [DFAO.transFrom, DFA.union_transition, ih]

theorem DFA.union_evalFrom (dfa1 : DFA α state1) (dfa2 : DFA α state2) (s : List α) (q1 : state1) (q2 : state2) :
  (dfa1.union dfa2).evalFrom s (q1, q2) = (dfa1.evalFrom s q1 || dfa2.evalFrom s q2) := by
  simp[DFAO.evalFrom, DFA.union_transFrom, DFA.union_output]

theorem DFA.union_eval (dfa1 : DFA α state1) (dfa2 : DFA α state2)
  (s : List α) : (dfa1.union dfa2).eval s = (dfa1.eval s || dfa2.eval s) := by
  exact DFA.union_evalFrom dfa1 dfa2 s dfa1.start dfa2.start
