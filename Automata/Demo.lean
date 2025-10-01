import Mathlib.Tactic
import Automata.Equality
import Automata.Projection
import Automata.Boolean
import Automata.Addition

set_option trace.profiler true

-- theorem demo : ¬ ∃ x : ℕ, ¬ ∃ y, x = y := by
-- -- Build x = y
--   have : ∀ x y : ℕ, x = y ↔ (eqBase 0 2 1 0).eval (toWord ![y, x] 0 ) := by
--     intro x y
--     rw[eqBase_iff]
--     simp_all
--   simp_rw [this]
-- -- Build ∃ y, x = y
--   have : ∀ x, ((∃ y, (eqBase 0 2 1 0).eval (toWord ![y, x] 0)) ↔ (project (eqBase 0 2 1 0)).fixLeadingZeros.toDFA.eval (toWord ![x] 0)) := by
--     intro x
--     rw[project_iff]
--     exact equality_respectZero
--   simp_rw [this]
-- -- Build ¬ ∃ y, x = y
--   have : ∀ x, ((¬ (project (eqBase 0 2 1 0)).fixLeadingZeros.toDFA.eval (toWord ![x] 0) = true) ↔ (project (eqBase 0 2 1 0)).fixLeadingZeros.toDFA.negate.eval (toWord ![x] 0) = true) := by
--     intro x
--     rw[negate_iff]
--   simp_rw [this]
-- --Build ∃ x, ¬ ∃ y, x = y
--   have : (∃ x, DFAO.eval (project (eqBase 0 2 1 0)).fixLeadingZeros.toDFA.negate (toWord ![x] 0) = true) ↔ ((project (project (eqBase 0 2 1 0)).fixLeadingZeros.toDFA.negate).fixLeadingZeros.toDFA.eval (toWord ![] 0) = true) := by
--       rw[project_iff]
--       apply DFA.negate_respectZero
--       apply project_fix_toDFA_respectZero
--       exact equality_respectZero
--   simp_rw[this]
-- -- Finally, build ¬ ∃ x, ¬ ∃ y, x = y
--   have : ¬ (project (project (eqBase 0 2 1 0)).fixLeadingZeros.toDFA.negate).fixLeadingZeros.toDFA.eval (toWord ![] 0) =
--     true ↔ (project (project (eqBase 0 2 1 0)).fixLeadingZeros.toDFA.negate).fixLeadingZeros.toDFA.negate.eval (toWord ![] 0) = true := by
--     rw[negate_iff]
--   simp_rw[this]
-- -- Check result
--   native_decide

theorem proxy : ∃ x : ℕ, ∃ y, x = y := by
  -- Build x = y
  have : ∀ x y : ℕ, (x = y) ↔ (eqBase 0 2 1 0).eval (toWord ![y, x] 0) := by
    intro x y
    rw [eqBase_iff]
    simp_all
  simp_rw [this]

  -- Build ∃ y, x = y
  have : ∀ x, (∃ y, (eqBase 0 2 1 0).eval (toWord ![y, x] 0)) ↔
      (project (eqBase 0 2 1 0)).fixLeadingZeros.toDFA.eval (toWord ![x] 0) := by
    intro x
    rw [project_iff]
    exact equality_respectZero
  simp_rw [this]

  -- Build ∃ x, ∃ y, x = y
  have : (∃ x, (project (eqBase 0 2 1 0)).fixLeadingZeros.toDFA.eval (toWord ![x] 0)) ↔
      (project (project (eqBase 0 2 1 0)).fixLeadingZeros.toDFA).fixLeadingZeros.toDFA.eval (toWord ![] 0) := by
    rw [project_iff]
    apply project_fix_toDFA_respectZero
    exact equality_respectZero
  simp_rw [this]

  -- Check result
  native_decide

  def addDFA := addBase 0 3 0 1 2 -- DFA for x + y = z

  -- #eval (project (project (project addDFA).fixLeadingZeros.toDFA).fixLeadingZeros.toDFA).eval (toWord ![] 0) -- memory out
