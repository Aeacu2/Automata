def hello := "world"

/-
Description of Project:

This project aims to formalize automatas for computational purposes in Lean. Automatas as currently formalized in Mathlib.Computability.DFA/NFA use Sets, which makes them inefficient for computing.

In DFA.lean, we define DFAO -- DFA with output, and abbreviate DFAO where the output is Bool as DFA. Various theorems and operations are given, such as the pumping lemma and the product constructions.

In NFA.lean, we define NFA using the type ListND, list with no duplicates. This allows us to synthesize Fintype (ListND state) from Fintype state. An operation to convert NFA to DFA is given with a correctness proof, and the pumping lemma follows.

In Input.lean, we define operations to covert a list of natural numbers to a list of base-b alphabet inputs for a DFA. Various properties of the input transformation are proven.

In Equality.lean, we define an automata which checks if two numbers are equal. The correctness is proven by considering the relationship between the automata, the input list of letters, and the input numbers.

In Projection.lean, we define a function which turns a DFA with n+1 inputs to an NFA with n inputs, by projecting a specified index. This is supposed to simulate an existential quantifier. It is unknown how the correctness of this operation can be proven.

Other files are currently small examples awaiting expansion.
-/
