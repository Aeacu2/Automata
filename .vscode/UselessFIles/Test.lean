import Mathlib.Data.Real.Basic
import Mathlib.Tactic
impo

set_option trace.profiler true

#eval [(fun _ => 0 : Fin 2 → Fin (0 + 2)), fun _ => 1]
-- Problem: exists x, 1 + 1 = x?
#eval (project 2 (addBase 2)).eval [fun _ => 1]
-- Fix:
#eval (project 2 (addBase 2)).eval [fun _ => 0, fun _ => 1]

#eval (project 2 (addBase 2)).eval (inputToBase 2 (by omega) [100000, 10000])

-- Exists x, y + x = x?
#eval (project 1 (collapse 2 1 (addBase 2))).eval (inputToBase 2 (by omega) [100000])

#eval (project 1 (collapse 2 1 (addBase 2))).eval (inputToBase 2 (by omega) [10])

-- Exists x, x + x = x?
#eval (project 0 (collapse 1 0 (collapse 2 1 (addBase 2)))).eval (inputToBase 2 (by omega) [])
