import Mathlib.Tactic
import Mathlib.Data.FinEnum

open Std

variable {α β state1 state2 state : Type} [FinEnum α] [FinEnum β] [FinEnum state1] [FinEnum state2] [FinEnum state]

structure DFA (α state : Type ) [FinEnum α] [FinEnum state]:=
  (transition : α → state → state)
  (start : state)
  (accept : state → Bool)
deriving Inhabited, DecidableEq

def d : DFA (Fin 2) (Fin 2) where
  transition := fun s _ => s
  start := 0
  accept := fun _ => true

def DFA.accepts_at {α state : Type} [FinEnum α] [FinEnum state] (dfa : DFA α state) (s : List α) (q : state) : Bool :=
  match s with
    | [] => dfa.accept q
    | a::as => DFA.accepts_at dfa as (dfa.transition a q)

def DFA.accepts {α state : Type} [FinEnum α] [FinEnum state] (dfa : DFA α state) (s : List α) : Bool :=
  DFA.accepts_at dfa s dfa.start



#eval DFA.accepts d [0]


def DFA.negate  (dfa: DFA α state ) : DFA α state := {
  transition := dfa.transition
  start := dfa.start
  accept := fun x =>  ! dfa.accept x
}

#eval DFA.accepts (DFA.negate d) [0]

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

#eval DFA.accepts (DFA.product_i d (DFA.negate d)) [(0, 0)]
#eval DFA.accepts (DFA.product_u d (DFA.negate d)) [(0, 0)]

#eval (d.product_i d.negate).accepts [(0, 0)]
#eval d.product_i d.negate |>.accepts [(0, 0)]

theorem DFA.negate_start (dfa : DFA α state) :
  (dfa.negate).start = dfa.start := by rfl

theorem DFA.negate_transition (dfa : DFA α state) :
  (dfa.negate).transition = dfa.transition := by rfl

theorem DFA.negate_accept (dfa : DFA α state) (q : state) :
  (dfa.negate).accept q = ! dfa.accept q := by rfl

theorem DFA.negate_accepts_at (dfa : DFA α state) (s : List α) (q : state) :
  (dfa.negate).accepts_at s q = ! dfa.accepts_at s q := by
  induction s generalizing q
  case nil => rfl
  case cons a s ih =>
    rw [DFA.accepts_at, DFA.accepts_at, DFA.negate_transition, ih]

theorem DFA.negate_accepts (dfa : DFA α state) (s : List α) :
  (dfa.negate).accepts s = ! dfa.accepts s := by
  rw [DFA.accepts, DFA.accepts]
  exact DFA.negate_accepts_at dfa s dfa.start

theorem DFA.product_i_start (dfa1 : DFA α state1) (dfa2 : DFA β state2) :
  (dfa1.product_i dfa2).start = (dfa1.start, dfa2.start) := by rfl

theorem DFA.product_i_transition (dfa1 : DFA α state1) (dfa2 : DFA β state2) :
  (dfa1.product_i dfa2).transition = fun (q1, q2) a => ⟨dfa1.transition q1 a.1, dfa2.transition q2 a.2⟩ := by rfl

theorem DFA.product_i_accept (dfa1 : DFA α state1) (dfa2 : DFA β state2) (q1 : state1) (q2 : state2) :
  (dfa1.product_i dfa2).accept (q1, q2) = (dfa1.accept q1 && dfa2.accept q2) := by rfl

theorem DFA.product_i_accepts_at (dfa1 : DFA α state1) (dfa2 : DFA β state2) (s : List (α × β)) (q1 : state1) (q2 : state2) :
  (dfa1.product_i dfa2).accepts_at s (q1, q2) = (dfa1.accepts_at (s.map Prod.fst) q1 && dfa2.accepts_at (s.map Prod.snd) q2) := by
  induction s generalizing q1 q2
  case nil => rfl
  case cons a s ih =>
    rw [DFA.accepts_at, DFA.product_i_transition, ih]
    rw [List.map_cons, List.map_cons, DFA.accepts_at, DFA.accepts_at]


theorem DFA.product_i_accepts (dfa1 : DFA α state1) (dfa2 : DFA β state2)
  (s : List (α × β)) : (dfa1.product_i dfa2).accepts s
    =  (dfa1.accepts (s.map Prod.fst) && dfa2.accepts (s.map Prod.snd)) := by
  rw [DFA.accepts, DFA.accepts]
  exact DFA.product_i_accepts_at dfa1 dfa2 s dfa1.start dfa2.start

theorem DFA.product_u_start (dfa1 : DFA α state1) (dfa2 : DFA β state2) :
  (dfa1.product_u dfa2).start = (dfa1.start, dfa2.start) := by rfl

theorem DFA.product_u_transition (dfa1 : DFA α state1) (dfa2 : DFA β state2) :
  (dfa1.product_u dfa2).transition = fun (q1, q2) a => (dfa1.transition q1 a.1, dfa2.transition q2 a.2) := by rfl

theorem DFA.product_u_accept (dfa1 : DFA α state1) (dfa2 : DFA β state2) (q1 : state1) (q2 : state2) :
  (dfa1.product_u dfa2).accept (q1, q2) = (dfa1.accept q1 || dfa2.accept q2) := by rfl

theorem DFA.product_u_accepts_at (dfa1 : DFA α state1) (dfa2 : DFA β state2) (s : List (α × β)) (q1 : state1) (q2 : state2) :
  (dfa1.product_u dfa2).accepts_at s (q1, q2) = (dfa1.accepts_at (s.map Prod.fst) q1 || dfa2.accepts_at (s.map Prod.snd) q2) := by
  induction s generalizing q1 q2
  case nil => rfl
  case cons a s ih =>
    rw [DFA.accepts_at, DFA.product_u_transition, ih]
    rw [List.map_cons, List.map_cons, DFA.accepts_at, DFA.accepts_at]

theorem DFA.product_u_accepts (dfa1 : DFA α state1) (dfa2 : DFA β state2)
  (s : List (α × β)) : (dfa1.product_u dfa2).accepts s
    =  (dfa1.accepts (s.map Prod.fst) || dfa2.accepts (s.map Prod.snd)) := by
  rw [DFA.accepts, DFA.accepts]
  exact DFA.product_u_accepts_at dfa1 dfa2 s dfa1.start dfa2.start

structure NFA (α state : Type ) [FinEnum α] [FinEnum state]:=
  (transition : α → state → List state)
  (start : state)
  (accept : state → Bool)

def n : NFA (Fin 2) (Fin 3) where
  transition := fun a s => [s+1, s+a]
  start := 0
  accept := fun x => x == 2

def NFA.accepts {α state : Type} [FinEnum α] [FinEnum state] (nfa : NFA α state) (s : List α) : Bool :=
  let rec aux : List α → List state → Bool
    | [], qs => qs.any nfa.accept
    | a::as, qs => aux as (List.join (qs.map (nfa.transition a)))
  aux s [nfa.start]

#eval NFA.accepts n [0]
#eval NFA.accepts n [0, 0]


#eval (d.product_i d.negate).accepts [(0, 0)]
#eval d.product_i d.negate |>.accepts [(0, 0)]

def foo (x : Nat) := x + 2

#eval foo <| 3 + 3


structure Foo (α : Type) where
  x : α
deriving Inhabited, Repr

structure Bar where

#eval (default : Foo Nat)

#check Nat

inductive MyType where
  | a
  | b
  | c
deriving Inhabited, DecidableEq, Repr, Fintype

#eval (default : MyType)

#check MyType.a

#synth Fintype MyType

instance fin_enum_card_zero_equiv {α : Type} [FinEnum α] (h : FinEnum.card α = 0) : α ≃ Fin 0 := by
  have h' : α ≃ Fin (FinEnum.card α) := FinEnum.equiv
  rw [h] at h'
  exact h'


def NFA.determinize {α state : Type} [FinEnum α] [FinEnum state] (nfa : NFA α state) : DFA α (FinEnum.toList state).sublists where
  transition := fun a f => (fun q => ∃ q', f q' ∧ q ∈ nfa.transition a q')
  start := fun x => x == nfa.start
  accept := fun f => ∃ q, f q ∧ nfa.accept q


#eval! (n.determinize).accepts [0, 0]


instance fin_enum_card_zero_equiv {α : Type} [FinEnum α] (h : FinEnum.card α = 0) : α ≃ Fin 0 := by
  have h' : α ≃ Fin (FinEnum.card α) := FinEnum.equiv
  rw [h] at h'
  exact h'

instance empty_func_one {α β : Type} {h: α ≃ Fin 0} : (α → β) ≃ Fin 1 := by
  rcases h with ⟨f, g, h, k⟩
  constructor
  . sorry
  . sorry
  . intro ab

    sorry
  . sorry



#check Fintype.card_eq_zero_iff
#check FinEnum.instFintype

instance FinEnumToBool.finEnum [FinEnum α] : FinEnum (α → Bool) := {
  card := 2^(FinEnum.card α),
  equiv := by
    generalize h : FinEnum.card α = c
    induction c generalizing α with
    | zero =>
      rw[pow_zero]
      have empty: IsEmpty α := by
        apply Fintype.card_eq_zero_iff.mp
        sorry
      sorry
    | succ n ih => sorry
}
