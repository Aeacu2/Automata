import Mathlib.Tactic
import Mathlib.Data.List.Basic
import Mathlib.Data.Nat.Digits
import Automata.DFA
import Automata.NFA
import Automata.Input
import Automata.Addition


-- Auxilliary theorems for recover
theorem finLt (m : Fin n) (b : ℕ) (h : n ≥ 1): b < m.val → b < n-1 := by omega

theorem finPred (m : Fin n) (a : Fin n) (h : a > m): a.val - 1 < n - 1 := by omega


-- Auxilliary function for project
def recover (m : Fin (n + 1)) (x: Fin k):
  (Fin n → Fin k) → (Fin (n + 1) → Fin k) :=
    fun i => fun j => if h1: j.val < m.val then i ⟨j.val, finLt m j.val (by norm_num) h1⟩
      else if h2: j.val > m.val then i ⟨j.val - 1, finPred m j h2⟩ else x

def project (dfa : DFA (Fin (n+1) → Fin k) state) (m : Fin n) [BEq state] :
  NFA (Fin n → Fin k) state := {
  transition :=
  fun a q => (List.map (fun (x : Fin k) => dfa.transition (recover m x a) q)
    (FinEnum.toList (Fin k)))
  start := [dfa.start]
  output := dfa.output
}

-- Auxilliary function for project
def recover' (h: n ≥ 1) (m : Fin n) (x: Fin k):
  (Fin (n-1) → Fin k) → (Fin n → Fin k) :=
    fun i => fun j => if h1: j.val < m.val then i ⟨j.val, finLt m j.val h h1⟩
      else if h2: j.val > m.val then i ⟨j.val - 1, finPred m j h2⟩ else x

def project' (dfa : DFA (Fin n → Fin k) state) (h: n ≥ 1) (m : Fin n) [BEq state] :
  NFA (Fin (n - 1) → Fin k) state := {
  transition :=
  fun a q => (List.map (fun (x : Fin k) => dfa.transition (recover' h m x a) q)
    (FinEnum.toList (Fin k)))
  start := [dfa.start]
  output := dfa.output
}

-- Problem: exists x, 1 + 1 = x?
#eval (project (addBase 2)  2).eval [fun _ => 1]
-- Fix:
#eval (project (addBase 2) 2).eval [fun _ => 0, fun _ => 1]
