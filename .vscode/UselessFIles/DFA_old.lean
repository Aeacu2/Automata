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
structure DFA (α state : Type) extends DFAO α state Bool

def DFAO.toDFA (dfao : DFAO α state out) (o: out) [BEq out]: DFA α state := {
  transition := dfao.transition,
  start := dfao.start,
  output := fun s => (dfao.output s) == o
}

def DFA.evalFrom (dfa : DFA α state) (s : List α) (q : state) : Bool :=
  match s with
    | [] => dfa.output q
    | a::as => DFA.evalFrom dfa as (dfa.transition a q)

def DFA.eval (dfa : DFA α state) (s : List α) : Bool :=
  DFA.evalFrom dfa s dfa.start

def DFAO.toDFA_evalFrom (dfao : DFAO α state out)
  (o: out) (s : List α) (q : state) [BEq out] :
    (dfao.toDFA o).evalFrom s q = ((dfao.evalFrom s q) == o) := by
  induction s generalizing q with
  | nil => rfl
  | cons x xs ih =>
    simp only [DFA.evalFrom, DFAO.toDFA, DFAO.evalFrom, DFAO.toDFA]
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

def DFA.product_i (dfa1 : DFA α state1) (dfa2 : DFA β state2) : DFA (α × β) (state1 × state2) := {
  transition := fun (q1, q2) a => ⟨dfa1.transition q1 a.1, dfa2.transition q2 a.2⟩,
  start := (dfa1.start, dfa2.start),
  output := fun (q1, q2) => dfa1.output q1 && dfa2.output q2
}

def DFA.product_u  (dfa1 : DFA α state1) (dfa2 : DFA β state2) : DFA (α × β) (state1 × state2) := {
  transition := fun (q1, q2) a => (dfa1.transition q1 a.1, dfa2.transition q2 a.2),
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
    rw [DFA.evalFrom, DFA.evalFrom, DFA.negate_transition, ih]

theorem DFA.negate_eval (dfa : DFA α state) (s : List α) :
  (dfa.negate).eval s = ! dfa.eval s := by
  exact DFA.negate_evalFrom dfa s dfa.start

theorem DFA.product_i_transition (dfa1 : DFA α state1) (dfa2 : DFA β state2) :
  (dfa1.product_i dfa2).transition = fun (q1, q2) a => ⟨dfa1.transition q1 a.1, dfa2.transition q2 a.2⟩ := by rfl

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

theorem DFA.product_u_transition (dfa1 : DFA α state1) (dfa2 : DFA β state2) :
  (dfa1.product_u dfa2).transition = fun (q1, q2) a => (dfa1.transition q1 a.1, dfa2.transition q2 a.2) := by rfl

theorem DFA.product_u_evalFrom (dfa1 : DFA α state1) (dfa2 : DFA β state2) (s : List (α × β)) (q1 : state1) (q2 : state2) :
  (dfa1.product_u dfa2).evalFrom s (q1, q2) = (dfa1.evalFrom (s.map Prod.fst) q1 || dfa2.evalFrom (s.map Prod.snd) q2) := by
  induction s generalizing q1 q2
  case nil => rfl
  case cons a s ih =>
    simp [DFA.evalFrom, DFA.product_u_transition, ih]

theorem DFA.product_u_eval (dfa1 : DFA α state1) (dfa2 : DFA β state2)
  (s : List (α × β)) : (dfa1.product_u dfa2).eval s
    =  (dfa1.eval (s.map Prod.fst) || dfa2.eval (s.map Prod.snd)) := by
  exact DFA.product_u_evalFrom dfa1 dfa2 s dfa1.start dfa2.start


def fixLeadingZero [NeZero n] (dfa : DFA (Fin n) state) : DFA (Fin n) (Option state) := {
  transition := fun a q => match q with
    | none => if a == 0 then none else some (dfa.transition a dfa.start)
    | some q => some (dfa.transition a q),
  start := none,
  output := fun q => match q with
    | none => dfa.output dfa.start
    | some q => dfa.output q
}

theorem fixLeadingZero_transition_none [NeZero n] (dfa : DFA (Fin n) state) (a : (Fin n)) :
  (fixLeadingZero dfa).transition a none =
    if a == 0 then none else some (dfa.transition a dfa.start) := rfl

theorem fixLeadingZero_evalFrom [NeZero n] (dfa : DFA (Fin n) state) (s : List (Fin n)) (q : state) :
  (fixLeadingZero dfa).evalFrom s (some q) = dfa.evalFrom s q := by
  induction s generalizing q
  case nil => rfl
  case cons a s ih =>
    simp only [DFA.evalFrom]
    exact ih (dfa.transition a q)

theorem fixLeadingZero_eval [NeZero n] (dfa : DFA (Fin n) state) (s : List (Fin n)) :
  (fixLeadingZero dfa).eval s = dfa.eval s := by
  simp only [DFA.eval]
  induction s
  case nil => rfl
  case cons a s _ =>
    have h: (fixLeadingZero dfa).start = none := rfl
    simp only [DFA.evalFrom, h, fixLeadingZero_transition_none]
    sorry
