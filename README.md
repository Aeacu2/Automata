# This project attempts to formalize and verify automata (and operations on them) for computational purposes in Lean.
ITP project 1 (Completed in Equality.lean) : Prove the correctness of the equality checking automation for natural numbers in base b (eqBase b): 
m = n ↔ (eqBase b).eval (inputToBase b hb [m, n])

ITP project 2 : 
1. Equality.lean: Generalized and simplified proofs for arbitrary letter length
2. Fin.lean: Implemented common Fin operations for inserting and removing elements from a Fin vector. Proved important insert_remove and remove_insert lemmas
3. Replicate.lean: Definitions and theorems for List.replicate and append.
4. Pumping.lean: Pumping lemmas for DFAO, DFA, and NFA.
5. LeadingZeros.lean: Deal with leading zero issues for automata: defined properties respectZero and acceptZero for DFA and NFA, proved lemmas, and that the equality automation respects zero. Bounded acceptance theorem for DFAO, DFA, and NFA are proven from the pumping lemmas, which are crucial to fix leading zero issues for projection
6. NFA.lean: Important transList_subList and transFrom_subList theorems
7. Projection.lean: ListND type to synthesizing Finset state for the NFA pumping lemma. Proved that projection behaves as expected on general inputs (projection_transFrom, projection_evalFrom, projection_eval)
8. Collapse.lean: Implemented the collapse operation to simply automata and make projection easier. Proved that it behaves as expected on general inputs (collapse_transFrom, collapse_evalFrom, collapse_eval). Moreover, proved that it is correct for natural number inputs.
9. Minor reorganization in Input.lean and Boolean.lean.