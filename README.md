# This project attempts to formalize and verify automatas (and operations on them) for computational purposes in Lean.
Goal of ITP project 1: in Common.lean, prove the correctness of the equality checking automata for natural numbers in base b (eqBase b): 
m = n ↔ (eqBase b).eval (inputToBase b hb [m, n])
