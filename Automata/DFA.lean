import Mathlib.Tactic

structure DFAO (α state out: Type):=
  (transition : α → state → state)
  (start : state)
  (output : state → out)

def DFAO.evalFrom (dfao : DFAO α state out) (s : List α) (q : state) : out :=
  match s with
    | [] => dfao.output q
    | a::as => DFAO.evalFrom dfao as (dfao.transition a q)

def DFAO.eval (dfao : DFAO α state out) (s : List α) : out :=
  DFAO.evalFrom dfao s dfao.start

-- A DFA is a DFAO where the output is a boolean
abbrev DFA (α state : Type) := DFAO α state Bool

def DFAO.toDFA (dfao : DFAO α state out) (o: out) [BEq out]: DFA α state := {
  transition := dfao.transition,
  start := dfao.start,
  output := fun s => (dfao.output s) == o
}

def DFAO.toDFA_evalFrom (dfao : DFAO α state out)
  (o: out) (s : List α) (q : state) [BEq out] :
    (dfao.toDFA o).evalFrom s q = ((dfao.evalFrom s q) == o) := by
  induction s generalizing q with
  | nil => rfl
  | cons x xs ih =>
    simp only [DFAO.evalFrom, DFAO.toDFA]
    exact ih (dfao.transition x q)

def DFAO.toDFA_eval (dfao : DFAO α state out)
  (o: out) (s : List α) [BEq out] :
    (dfao.toDFA o).eval s = (dfao.eval s == o) := by
  exact DFAO.toDFA_evalFrom dfao o s dfao.start

def DFA.negate (dfa: DFA α state) : DFA α state := {
  transition := dfa.transition
  start := dfa.start
  output := fun x =>  ! dfa.output x
}

def DFA.product_i (dfa1 : DFA α state1) (dfa2 : DFA α state2) : DFA (α ) (state1 × state2) := {
  transition := fun a q => ⟨dfa1.transition a q.1, dfa2.transition a q.2⟩,
  start := (dfa1.start, dfa2.start),
  output := fun (q1, q2) => dfa1.output q1 && dfa2.output q2
}

def DFA.product_u  (dfa1 : DFA α state1) (dfa2 : DFA α state2) : DFA (α) (state1 × state2) := {
  transition := fun a q => ⟨dfa1.transition a q.1, dfa2.transition a q.2⟩,
  start := (dfa1.start, dfa2.start),
  output := fun (q1, q2) => dfa1.output q1 || dfa2.output q2
}

theorem DFA.negate_transition (dfa : DFA α state) :
  (dfa.negate).transition = dfa.transition := by rfl

theorem DFA.negate_evalFrom (dfa : DFA α state) (s : List α) (q : state) :
  (dfa.negate).evalFrom s q = ! dfa.evalFrom s q := by
  induction s generalizing q
  case nil => rfl
  case cons a s ih =>
    rw [DFAO.evalFrom, DFAO.evalFrom, DFA.negate_transition, ih]

theorem DFA.negate_eval (dfa : DFA α state) (s : List α) :
  (dfa.negate).eval s = ! dfa.eval s := by
  exact DFA.negate_evalFrom dfa s dfa.start

theorem DFA.product_i_transition (dfa1 : DFA α state1) (dfa2 : DFA α state2) :
  (dfa1.product_i dfa2).transition = fun a q => ⟨dfa1.transition a q.1, dfa2.transition a q.2⟩ := by rfl

theorem DFA.product_i_evalFrom (dfa1 : DFA α state1) (dfa2 : DFA α state2) (s : List α) (q1 : state1) (q2 : state2) :
  (dfa1.product_i dfa2).evalFrom s (q1, q2) = (dfa1.evalFrom s q1 && dfa2.evalFrom s q2) := by
  induction s generalizing q1 q2
  case nil => rfl
  case cons a s ih =>
    simp [DFAO.evalFrom, DFA.product_i_transition, ih]
    -- rw [DFA.evalFrom, DFA.product_i_transition, ih]
    -- rw [List.map_cons, List.map_cons, DFA.evalFrom, DFA.evalFrom]

theorem DFA.product_i_eval (dfa1 : DFA α state1) (dfa2 : DFA α state2)
  (s : List α) : (dfa1.product_i dfa2).eval s = (dfa1.eval s && dfa2.eval s) := by
  exact DFA.product_i_evalFrom dfa1 dfa2 s dfa1.start dfa2.start

theorem DFA.product_u_transition (dfa1 : DFA α state1) (dfa2 : DFA α state2) :
  (dfa1.product_u dfa2).transition = fun a q => ⟨dfa1.transition a q.1, dfa2.transition a q.2⟩ := by rfl

theorem DFA.product_u_evalFrom (dfa1 : DFA α state1) (dfa2 : DFA α state2) (s : List α) (q1 : state1) (q2 : state2) :
  (dfa1.product_u dfa2).evalFrom s (q1, q2) = (dfa1.evalFrom s q1 || dfa2.evalFrom s q2) := by
  induction s generalizing q1 q2
  case nil => rfl
  case cons a s ih =>
    simp [DFAO.evalFrom, DFA.product_u_transition, ih]

theorem DFA.product_u_eval (dfa1 : DFA α state1) (dfa2 : DFA α state2)
  (s : List α) : (dfa1.product_u dfa2).eval s = (dfa1.eval s || dfa2.eval s) := by
  exact DFA.product_u_evalFrom dfa1 dfa2 s dfa1.start dfa2.start
