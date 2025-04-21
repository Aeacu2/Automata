import Mathlib.Tactic
import Automata.Equality
import Automata.Addition
import Automata.Projection
import Automata.Boolean
import Automata.ThueMorse

theorem zero_is_zero : 0 = 0 := by
  apply (eqBase_iff_equal 2 (by norm_num) [0, 0] 2 (by norm_num) 0 1).mpr
  native_decide


theorem foo : 100000 = 100000 := by
  apply (eqBase_iff_equal 2 (by norm_num) [100000, 100000] 2 (by norm_num) 0 1).mpr
  native_decide

-- ∃ x, x = 0?
#eval (project 0 (eqBase 2 2 0 1)).eval [fun _ => 0]

-- ∃ x, 1 + 1 = x?
#eval (project 2 (addBase 2)).eval [fun _ => 1]
-- Wrong! Why? Projection only searches for representations in restricted length, 1+1 = 2 needs 2 bits.
#eval (project 2 (addBase 2)).eval [fun _ => 0, fun _ => 1]
-- Correct with fixing leading zeros
#eval (project 2 (addBase 2)).fixLeadingZeros.eval [fun _ => 1]

-- ∃ x, t[x] = 0?
#eval (project 0 (thueMorse.toDFA 0)).fixLeadingZeros.eval [fun _ => 0]

