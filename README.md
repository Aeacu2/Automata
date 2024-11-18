# This project attempts to formalize and verify automatas (and operations on them) for computational purposes in Lean.
ITP project 1 (Completed in Equality.lean) : Prove the correctness of the equality checking automata for natural numbers in base b (eqBase b): 
m = n ↔ (eqBase b).eval (inputToBase b hb [m, n])

Goal of ITP project 2: Implement new versions of DFAO/DFA/NFA.eval based on vectors as opposed to Lists (Preview in Experiments.lean), and use them to experiment on simplifing definitions and proofs. Various theorems need to be reproved, in particular the pumping lemmas for new versions of evals needs new proofs.