import Mathlib.Tactic
import Automata.Equality
import Automata.Addition
import Automata.Projection

theorem zero_is_zero : 0 = 0 := by
  apply (eqBase_iff_equal 2 (by norm_num) [0, 0] 2 (by norm_num) 0 1).mpr
  unfold DFAO.eval DFAO.evalFrom
  native_decide


theorem foo : 100000 = 100000 := by
  apply (eqBase_iff_equal 2 (by norm_num) [100000, 100000] 2 (by norm_num) 0 1).mpr
  native_decide

-- What's difficult
-- ∃ x, x = 0?
#eval (project 0 (eqBase 2 2 0 1)).eval [fun _ => 0]

-- ∃ x, 1 + 1 = x?
#eval (project 2 (addBase 2)).eval [fun _ => 1]
-- Wrong! Why? Projection only searches for representations in restricted length, 1+1 = 2 needs 2 bits.
#eval (project 2 (addBase 2)).eval [fun _ => 0, fun _ => 1]
-- Correct after padding with 0s

#eval (project 2 (addBase 2)).fixLeadingZeros.eval [fun _ => 1]
