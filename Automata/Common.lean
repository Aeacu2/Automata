import Mathlib.Tactic
import Mathlib.Data.List.Basic
import Automata.DFA
import Automata.NFA
import Automata.Input
import Mathlib.Data.Nat.Digits

def thueMorse : DFAO (Fin 2) (Fin 2) (Fin 2) := {
  transition := fun a s => a + s
  start := 0
  output := fun x => x
}


def thueMorse0 : DFA (Fin 2) (Fin 2) := thueMorse.toDFA 0

def thueMorse1 : DFA (Fin 2) (Fin 2) := thueMorse.toDFA 1

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

def eqBase (k: ℕ) : DFA (Fin 2 → Fin k) (Fin 2) := {
  transition := fun f s => match s with
    | 0 => if (f 0).val == f 1 then 0 else 1
    | 1 => 1
  start := 0
  output := fun x => x == 0
}

--Exists x, x = 0?
#eval (project (eqBase 2) (by norm_num) ⟨0, by norm_num⟩).eval [fun _ => 0]

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

-- Exists x, x < 0?
#eval (project (ltBase 2) (by norm_num) ⟨0, by norm_num⟩).eval [fun _ => 0]

--Exists x, x + 1 = 0? Wrong Answer!
#eval (project (addBase 2) (by norm_num) ⟨0, by norm_num⟩).evalFrom [fun x => if x == 0 then 1 else 0] [0]



theorem eqBase_if_equal_aux (b : ℕ) (m n : ℕ) (hb: b > 1):
  m = n → (eqBase b).evalFrom (inputToBase b hb [m, n]) 0 := by
  intro h
  rw[h]
  generalize hl: (inputToBase b hb [n, n]).length = l
  induction l with
  | zero =>
    simp only [List.length_eq_zero] at hl
    rw[hl]
    simp[eqBase, DFAO.evalFrom]
  | succ l ih =>


  sorry



theorem eqBase_if_equal (b : ℕ) (m n : ℕ) (hb: b > 1):
  m = n → (eqBase b).eval (inputToBase b hb [m, n]) := by
  rw[DFAO.eval]
  intro h
  rw[h]
  generalize hl: (inputToBase b hb [n, n]).length = l
  induction l with
  | zero =>
    simp only [List.length_eq_zero] at hl
    rw[hl]
    simp[eqBase, DFAO.evalFrom]
  | succ l ih =>


  sorry
