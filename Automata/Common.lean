import Mathlib.Tactic
import Mathlib.Data.List.Basic
import Automata.DFA
import Automata.NFA
import Mathlib.Data.Nat.Digits

def thueMorse : DFAO (Fin 2) (Fin 2) (Fin 2) := {
  transition := fun a s => a + s
  start := 0
  output := fun x => x
}

#eval thueMorse.eval [0]
#eval thueMorse.eval [1]
#eval thueMorse.eval [1, 0]
#eval thueMorse.eval [1, 1]
#eval thueMorse.eval [1, 0, 0]
#eval thueMorse.eval [1, 0, 1]
#eval thueMorse.eval [1, 1, 0]
#eval thueMorse.eval [1, 1, 1]

def thueMorse0 : DFA (Fin 2) (Fin 2) := thueMorse.toDFA 0
#eval thueMorse0.eval [0]
#eval thueMorse0.eval [1]
#eval thueMorse0.eval [1, 0]
#eval thueMorse0.eval [1, 1]
#eval thueMorse0.eval [1, 0, 0]
#eval thueMorse0.eval [1, 0, 1]
#eval thueMorse0.eval [1, 1, 0]
#eval thueMorse0.eval [1, 1, 1]

def thueMorse1 : DFA (Fin 2) (Fin 2) := thueMorse.toDFA 1
#eval thueMorse1.eval [0]
#eval thueMorse1.eval [1]
#eval thueMorse1.eval [1, 0]
#eval thueMorse1.eval [1, 1]
#eval thueMorse1.eval [1, 0, 0]
#eval thueMorse1.eval [1, 0, 1]
#eval thueMorse1.eval [1, 1, 0]
#eval thueMorse1.eval [1, 1, 1]

def trueDFA: DFA (Fin 0) (Fin 1) := {
  transition := fun _ s => s
  start := 0
  output := fun _ => true
}

def falseDFA: DFA (Fin 0) (Fin 1) := {
  transition := fun _ s => s
  start := 0
  output := fun _ => false
}

#eval trueDFA.eval []
#eval falseDFA.eval []


def eqBase (n: ℕ) : DFA (Fin 2 → Fin n) (Fin 2) := {
  transition := fun f s => match s with
    | 0 => if (f 0).val == f 1 then 0 else 1
    | 1 => 1
  start := 0
  output := fun x => x == 0
}

#eval (eqBase 2).eval [fun _ => 0, fun _ => 1]
#eval (eqBase 2).eval [fun x => x, fun x => x]

def addBase (n: ℕ) : DFA (Fin 3 → Fin n) (Fin 3) := {
  transition := fun f s => match s with
    | 0 => if f 0 + f 1 == f 2 then 0 else
      if (f 0).val + f 1 + 1 == f 2 then 1
      else 2
    | 1 => if (f 0).val + f 1 + 1 == f 2 + n then 1 else
      if (f 0).val + f 1 == f 2 + n then 0
      else 2
    | 2 => 2
  start := 0
  output := fun x => x == 0
}

def ltBase (n: ℕ)  : DFA (Fin 2 → Fin n) (Fin 3) := {
  transition := fun f s => match s with
    | 0 => if (f 0).val < (f 1).val then 1 else if (f 0).val == (f 1).val then 0 else 2
    | 1 => 1
    | 2 => 2
  start := 0
  output := fun x => x == 1
}


#check Nat.toDigits
#eval Nat.digits 2 12

def digits' (b: ℕ) (n: ℕ) (h: b > 1) : List (Fin b) :=
  (Nat.digits b n).attach.map (fun x => ⟨x.1, Nat.digits_lt_base h x.2⟩)
#eval digits' 2 12 (by norm_num)


/- Q: Number bases in lean?

 Q: How to project a variable that's not in the first component?

 Q: How to deal, generally with formulas containing subformulas
 that does not have all the variables:
 like ∀x, y, x + y = 1 ∧ (x = 0 ∨ y = 0)?
 Need to extend the alphabet type of automatas to accomondate?

 Or use product alphabet: then projection becomes trickier

-/
