import Mathlib.Tactic
import Mathlib.Data.FinEnum

open Std

structure DFA (α state : Type) [FinEnum α] [FinEnum state]:=
  (transition : α → state → state)
  (start : state)
  (accept : state → Bool)
deriving Inhabited, DecidableEq

def d : DFA (Fin 2) (Fin 2) where
  transition := fun s _ => s
  start := 0
  accept := fun _ => true

def DFA.evalFrom {α state : Type} [FinEnum α] [FinEnum state] (dfa : DFA α state) (s : List α) (q : state) : Bool :=
  match s with
    | [] => dfa.accept q
    | a::as => DFA.evalFrom dfa as (dfa.transition a q)

def DFA.eval {α state : Type} [FinEnum α] [FinEnum state] (dfa : DFA α state) (s : List α) : Bool :=
  DFA.evalFrom dfa s dfa.start

def DFA.eval' {α state : Type} [FinEnum α] [FinEnum state] (dfa : DFA α state) (s : List α) : Bool :=
  let rec go : List α → state → Bool
    | [], q => dfa.accept q
    | a::as, q => go as (dfa.transition a q)
  go s dfa.start



#eval DFA.eval d [0]

variable {α β state1 state2 state : Type} [FinEnum α] [FinEnum β] [FinEnum state1] [FinEnum state2] [FinEnum state]


def DFA.negate  (dfa: DFA α state ) : DFA α state := {
  transition := dfa.transition
  start := dfa.start
  accept := fun x =>  ! dfa.accept x
}

#eval DFA.eval (DFA.negate d) [0]

def DFA.product_i  (dfa1 : DFA α state1) (dfa2 : DFA β state2) : DFA (α × β) (state1 × state2) := {
  transition := fun (q1, q2) a => ⟨dfa1.transition q1 a.1, dfa2.transition q2 a.2⟩,
  start := (dfa1.start, dfa2.start),
  accept := fun (q1, q2) => dfa1.accept q1 && dfa2.accept q2
}

def DFA.product_u  (dfa1 : DFA α state1) (dfa2 : DFA β state2) : DFA (α × β) (state1 × state2) := {
  transition := fun (q1, q2) a => (dfa1.transition q1 a.1, dfa2.transition q2 a.2),
  start := (dfa1.start, dfa2.start),
  accept := fun (q1, q2) => dfa1.accept q1 || dfa2.accept q2
}

#eval DFA.eval (DFA.product_i d (DFA.negate d)) [(0, 0)]
#eval DFA.eval (DFA.product_u d (DFA.negate d)) [(0, 0)]

#eval (d.product_i d.negate).eval [(0, 0)]
#eval d.product_i d.negate |>.eval [(0, 0)]
#check Lean.Expr

theorem DFA.negate_start (dfa : DFA α state) :
  (dfa.negate).start = dfa.start := by rfl

theorem DFA.negate_transition (dfa : DFA α state) :
  (dfa.negate).transition = dfa.transition := by rfl

theorem DFA.negate_accept (dfa : DFA α state) (q : state) :
  (dfa.negate).accept q = ! dfa.accept q := by rfl

theorem DFA.negate_evalFrom (dfa : DFA α state) (s : List α) (q : state) :
  (dfa.negate).evalFrom s q = ! dfa.evalFrom s q := by
  induction s generalizing q
  case nil => rfl
  case cons a s ih =>
    rw [DFA.evalFrom, DFA.evalFrom, DFA.negate_transition, ih]

theorem DFA.negate_eval (dfa : DFA α state) (s : List α) :
  (dfa.negate).eval s = ! dfa.eval s := by
  exact DFA.negate_evalFrom dfa s dfa.start

theorem DFA.product_i_start (dfa1 : DFA α state1) (dfa2 : DFA β state2) :
  (dfa1.product_i dfa2).start = (dfa1.start, dfa2.start) := by rfl

theorem DFA.product_i_transition (dfa1 : DFA α state1) (dfa2 : DFA β state2) :
  (dfa1.product_i dfa2).transition = fun (q1, q2) a => ⟨dfa1.transition q1 a.1, dfa2.transition q2 a.2⟩ := by rfl

theorem DFA.product_i_accept (dfa1 : DFA α state1) (dfa2 : DFA β state2) (q1 : state1) (q2 : state2) :
  (dfa1.product_i dfa2).accept (q1, q2) = (dfa1.accept q1 && dfa2.accept q2) := by rfl

theorem DFA.product_i_evalFrom (dfa1 : DFA α state1) (dfa2 : DFA β state2) (s : List (α × β)) (q1 : state1) (q2 : state2) :
  (dfa1.product_i dfa2).evalFrom s (q1, q2) = (dfa1.evalFrom (s.map Prod.fst) q1 && dfa2.evalFrom (s.map Prod.snd) q2) := by
  induction s generalizing q1 q2
  case nil => rfl
  case cons a s ih =>
    simp [DFA.evalFrom, DFA.product_i_transition, ih]
    -- rw [DFA.evalFrom, DFA.product_i_transition, ih]
    -- rw [List.map_cons, List.map_cons, DFA.evalFrom, DFA.evalFrom]


theorem DFA.product_i_eval (dfa1 : DFA α state1) (dfa2 : DFA β state2)
  (s : List (α × β)) : (dfa1.product_i dfa2).eval s
    =  (dfa1.eval (s.map Prod.fst) && dfa2.eval (s.map Prod.snd)) := by
  exact DFA.product_i_evalFrom dfa1 dfa2 s dfa1.start dfa2.start

theorem DFA.product_u_start (dfa1 : DFA α state1) (dfa2 : DFA β state2) :
  (dfa1.product_u dfa2).start = (dfa1.start, dfa2.start) := by rfl

theorem DFA.product_u_transition (dfa1 : DFA α state1) (dfa2 : DFA β state2) :
  (dfa1.product_u dfa2).transition = fun (q1, q2) a => (dfa1.transition q1 a.1, dfa2.transition q2 a.2) := by rfl

theorem DFA.product_u_accept (dfa1 : DFA α state1) (dfa2 : DFA β state2) (q1 : state1) (q2 : state2) :
  (dfa1.product_u dfa2).accept (q1, q2) = (dfa1.accept q1 || dfa2.accept q2) := by rfl

theorem DFA.product_u_evalFrom (dfa1 : DFA α state1) (dfa2 : DFA β state2) (s : List (α × β)) (q1 : state1) (q2 : state2) :
  (dfa1.product_u dfa2).evalFrom s (q1, q2) = (dfa1.evalFrom (s.map Prod.fst) q1 || dfa2.evalFrom (s.map Prod.snd) q2) := by
  induction s generalizing q1 q2
  case nil => rfl
  case cons a s ih =>
    rw [DFA.evalFrom, DFA.product_u_transition, ih]
    rw [List.map_cons, List.map_cons, DFA.evalFrom, DFA.evalFrom]

theorem DFA.product_u_eval (dfa1 : DFA α state1) (dfa2 : DFA β state2)
  (s : List (α × β)) : (dfa1.product_u dfa2).eval s
    =  (dfa1.eval (s.map Prod.fst) || dfa2.eval (s.map Prod.snd)) := by
  exact DFA.product_u_evalFrom dfa1 dfa2 s dfa1.start dfa2.start
