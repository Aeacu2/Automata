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


def eqBase (k: ℕ) : DFA (Fin 2 → Fin k) (Fin 2) := {
  transition := fun f s => match s with
    | 0 => if (f 0).val == f 1 then 0 else 1
    | 1 => 1
  start := 0
  output := fun x => x == 0
}

def eqBase' (k: ℕ) (a b n : ℕ) (ha: a < n) (hb: b < n): DFA (Fin n → Fin k) (Fin 2) := {
  transition := fun f s => match s with
    | 0 => if (f ⟨a, ha⟩).val == f ⟨b, hb⟩ then 0 else 1
    | 1 => 1
  start := 0
  output := fun x => x == 0
}

#eval (eqBase 2).eval [fun _ => 0, fun _ => 1]
#eval (eqBase 2).eval [fun x => x, fun x => x]
#eval (eqBase' 2 0 1 2 (by norm_num) (by norm_num)).eval [fun _ => 0, fun _ => 1]
#eval (eqBase' 2 0 1 2 (by norm_num) (by norm_num)).eval [fun x => x, fun x => x]


def addBase (k: ℕ) : DFA (Fin 3 → Fin k) (Fin 3) := {
  transition := fun f s => match s with
    | 0 => if f 0 + f 1 == f 2 then 0 else
      if (f 0).val + f 1 + 1 == f 2 then 1
      else 2
    | 1 => if (f 0).val + f 1 + 1 == f 2 + k then 1 else
      if (f 0).val + f 1 == f 2 + k then 0
      else 2
    | 2 => 2
  start := 0
  output := fun x => x == 0
}

def ltBase (k: ℕ)  : DFA (Fin 2 → Fin k) (Fin 3) := {
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
