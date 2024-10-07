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

def thueMorse0 : DFA (Fin 2) (Fin 2) := thueMorse.toDFA 0

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

def digits' (b: ℕ) (n: ℕ) (h: b > 1) : List (Fin b) :=
  (Nat.digits b n).attach.map (fun x => ⟨x.1, Nat.digits_lt_base h x.2⟩)

#eval digits' 2 12 (by norm_num)

def toBase (b : ℕ) (n : ℕ): List ℕ :=
  (Nat.digits b n).reverse

theorem toBase_lt_base (b: ℕ) (n: ℕ) (hb: b > 1) :
  x ∈ (toBase b n) → x < b := by
  intro h
  simp only [toBase] at h
  have h1: x ∈ Nat.digits b n := List.mem_reverse.mp h
  apply Nat.digits_lt_base
  exact hb
  exact h1

def ofBase (b : ℕ) (l : List ℕ) : ℕ :=
  l.foldl (fun x y => x * b + y) 0

theorem ofBase_toBase (b: ℕ) (n: ℕ) : ofBase b (toBase b n) = n := by
  simp only [toBase, ofBase, List.foldl_reverse, add_comm, mul_comm]
  have h: Nat.ofDigits b (b.digits n) = n := Nat.ofDigits_digits b n
  nth_rewrite 2 [← h]
  rw [Nat.ofDigits_eq_foldr]
  rfl

def addLeadingZeros (n: ℕ) (l: List ℕ): List ℕ :=
  (List.replicate n 0) ++ l

theorem addLeadingZerosLength (n: ℕ) (l: List ℕ) :
  (addLeadingZeros n l).length = n + l.length :=
  by simp only [addLeadingZeros, List.length_append, List.length_replicate]

theorem ofBase_addLeadingZeros (b: ℕ)(n: ℕ) (l: List ℕ) :
  ofBase b (addLeadingZeros n l) = ofBase b l := by
  simp only [ofBase, addLeadingZeros]
  induction n
  case zero => simp
  case succ n ih =>
    simp [addLeadingZeros, List.replicate, List.foldl, ih]

#eval toBase 2 12
#eval ofBase 2 [1, 1, 0, 0]

def mapToBase (b: ℕ) (l: List ℕ) : List (List ℕ) :=
  l.map (toBase b)

def maxLen : (l: List (List α)) → ℕ
  | [] => 0
  | x :: xs => max x.length (maxLen xs)


--def maxLen (l: List (List α)) : ℕ := l.foldl (fun x y => max x y.length) 0


theorem len_lt_maxLen' (l: List α) (ls: List (List α)) :
  l.length ≤ maxLen (l :: ls) := by
  induction ls generalizing l with
  | nil => simp[maxLen]
  | cons head tail _ =>
    simp [maxLen]


theorem len_lt_maxLen (l: List α) (ls: List (List α)) :
  l ∈ ls → l.length ≤ maxLen ls := by
  intro h
  induction ls generalizing l with
  | nil => simp only [List.not_mem_nil] at h
  | cons head tail ih =>
    have h1: l = head ∨ l ∈ tail := List.eq_or_mem_of_mem_cons h
    rcases h1 with (rfl | h1)
    . apply len_lt_maxLen'
    . simp[maxLen]
      right
      exact ih l h1

def toBaseZip (b : ℕ) (hb: b > 1) (l: List ℕ) : (List (Fin l.length → Fin b)) :=




  sorry
