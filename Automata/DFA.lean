import Mathlib.Tactic

structure DFAO (α state out: Type):=
  (transition : α → state → state)
  (start : state)
  (output : state → out)

variable {α state out : Type}

def DFAO.transFrom (dfao : DFAO α state out) (x : List α) (s : state) : state :=
  match x with
    | [] => s
    | a::as => DFAO.transFrom dfao as (dfao.transition a s)

def DFAO.evalFrom (dfao : DFAO α state out) (x : List α) (q : state) : out :=
  dfao.output (DFAO.transFrom dfao x q)

def DFAO.eval (dfao : DFAO α state out) (x : List α) : out :=
  DFAO.evalFrom dfao x dfao.start

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

