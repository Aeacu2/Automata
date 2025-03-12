import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Tactic

variable (P Q R S : Prop)

/-
Replace the following sorry's by proofs.
-/

example : (P → Q) ∧ (Q → R) → P → R := by
  tauto

example (h : P → Q) (h1 : P ∧ R) : Q ∧ R := by
  tauto

example (h : ¬ (P ∧ Q)) : P → ¬ Q := by
  tauto

example (h : ¬ (P → Q)) : ¬ Q := by
  tauto

example (h : P ∧ ¬ Q) : ¬ (P → Q) := by
  tauto

example (h1 : P ∨ Q) (h2 : P → R) : R ∨ Q := by
  tauto

example (h1 : P ∨ Q → R) : (P → R) ∧ (Q → R) := by
  tauto

example (h1 : P → R) (h2 : Q → R) : P ∨ Q → R := by
  tauto

example (h : ¬ (P ∨ Q)) : ¬ P ∧ ¬ Q := by
  tauto

-- this one requires classical logic!
example (h : ¬ (P ∧ Q)) : ¬ P ∨ ¬ Q := by
  by_contra h'
  apply h
  constructor
  by_contra hp
  apply h'
  left
  exact hp
  by_contra hq
  apply h'
  right
  exact hq

-- this one too
example (h : P → Q) : ¬ P ∨ Q := by
  by_contra h'
  apply h'
  right
  apply h
  by_contra hp
  apply h'
  left
  exact hp

/-
Prove the following using only `rw` and the identities given.

Remember that you can use `rw [← h]` to use an identity in the reverse direction,
and you can provides argument to general identities to instantiate them.
-/

#check add_assoc
#check add_comm
#check pow_mul
#check mul_comm
#check mul_add

example (x y z : Nat) : (x + y) + z = (z + y) + x := by
  rw [add_assoc, add_comm, add_comm y]

example (x y z : Nat) : (x^y)^z = (x^z)^y := by
  rw [← pow_mul, ← pow_mul, mul_comm]

example (x y z w : Nat) : (x^y)^(z + w) = x^(y * z + y * w) := by
  rw [← pow_mul, mul_add]

/-
A *group* is a structure with *, ⁻¹, 1 satisfing the basic group laws.

  https://en.wikipedia.org/wiki/Group_(mathematics)
-/

section
-- Lean lets us declare a group as follows.
variable {G : Type*} [Group G]

#check @mul_left_inv
#check @mul_right_inv
#check @mul_one
#check @one_mul
#check @mul_assoc

example (x y : G) : x * y * y⁻¹ = x := by
  rw [mul_assoc, mul_right_inv, mul_one]

/-
A group is *abelian* if it satisfies the additional law that
`x * y = y * x` for all `x` and `y`.

Fill in the sorry's in the next two theorems. The final one shows that
any group satisfying `x * x = 1` for every `x` is abelian.

You can use `rw [h]` to replace any expression of the form `e * e` by `1`.
-/

theorem fact1 (h : ∀ x : G, x * x = 1) (y z : G) :
    y * z = y * (y * z) * (y * z) * z := by
  rw[mul_assoc, mul_assoc, ← mul_assoc (y * z), h, one_mul]

theorem fact2 (h : ∀ x : G, x * x = 1) (y z : G) :
    z * y = y * (y * z) * (y * z) * z := by
  rw [mul_assoc, mul_assoc, mul_assoc, mul_assoc, h, mul_one, ← mul_assoc, h, one_mul]

theorem main (h : ∀ x : G, x * x = 1) (y z : G) :
    y * z = z * y := by
  rw [fact1 h y z, fact2 h y z]

end
