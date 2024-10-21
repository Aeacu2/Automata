import Mathlib.Tactic
import Mathlib.Data.List.Basic
import Automata.DFA
import Mathlib.Data.FinEnum

structure NFA (α state : Type) :=
  (transition : α → state → List state)
  (start : List state)
  (output : state → Bool)

def NFA.stepList (nfa : NFA α state) (a : α) (qs : List state) [BEq state] : List state :=
  (qs.bind fun q => nfa.transition a q)

def NFA.evalFrom (nfa : NFA α state) (s : List α) (qs : List state) [BEq state] : Bool :=
  match s with
    | [] => qs.any nfa.output
    | a::as => NFA.evalFrom nfa as (NFA.stepList nfa a qs)

def NFA.eval (nfa : NFA α state) (s : List α) [BEq state] : Bool :=
  NFA.evalFrom nfa s nfa.start

def NFA.toDFA (nfa : NFA α state) [BEq state] : DFA α (List state) where
  transition := fun a qs => NFA.stepList nfa a qs
  start := nfa.start
  output := fun qs => qs.any nfa.output

theorem NFA.toDFA_transition (nfa : NFA α state) (a : α) (qs : List state) [BEq state]:
  (nfa.toDFA).transition a qs = NFA.stepList nfa a qs := by rfl

theorem NFA.toDFA_evalFrom (nfa : NFA α state) (s : List α) (qs: List state) [BEq state]:
  (nfa.toDFA).evalFrom s qs = nfa.evalFrom s qs := by
  induction s generalizing qs
  case nil =>
    simp only [NFA.evalFrom, DFAO.evalFrom, DFAO.transFrom, NFA.toDFA]
  case cons x xs ih =>
    simp only [NFA.evalFrom, DFAO.evalFrom, NFA.toDFA_transition]
    exact ih (nfa.stepList x qs)

theorem NFA.toDFA_eval (nfa : NFA α state) (s : List α) [BEq state]
  : (nfa.toDFA).eval s = nfa.eval s := NFA.toDFA_evalFrom nfa s nfa.start

variable (β : Type)

theorem finLt (m : Fin n) (b : ℕ) (h : n ≥ 1): b < m.val → b < n-1 := by omega

theorem finPred (m : Fin n) (a : Fin n) (h : a > m): a.val - 1 < n - 1 := by omega

def recover (h: n ≥ 1) (m : Fin n) (x: Fin k):
  (Fin (n-1) → Fin k) → (Fin n → Fin k) :=
    fun i => fun j => if h1: j.val < m.val then i ⟨j.val, finLt m j.val h h1⟩
      else if h2: j.val > m.val then i ⟨j.val - 1, finPred m j h2⟩ else x

def project (dfa : DFA (Fin n → Fin k) state) (h: n ≥ 1) (m : Fin n) [BEq state] :
  NFA (Fin (n - 1) → Fin k) state := {
  transition :=
  fun a q => (List.map (fun (x : Fin k) => dfa.transition (recover h m x a) q)
    (FinEnum.toList (Fin k)))
  start := [dfa.start]
  output := dfa.output
}

/-
def project' (dfa : DFA (β × α) state) [BEq state] [FinEnum β] : NFA α state := {
  transition := fun a q => (List.map (fun (x : β) => dfa.transition (x, a) q) (FinEnum.toList β))
  start := [dfa.start]
  output := dfa.output
}
-/
