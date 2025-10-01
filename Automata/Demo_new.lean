import Mathlib.Tactic
import Automata.Equality_new
import Automata.Projection_new
import Automata.Boolean_new
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

-- theorem proxyz : ∃ x : ℕ, ∃ y, ∃ z, (x = y) ∧ y = z := by
--   -- Build x = y
--   have : ∀ x y z : ℕ, (x = y) ↔ (eqBase 0 3 1 0).eval (toWord ![y, x, z] 0) := by
--     intro x y z
--     rw [eqBase_iff]
--     simp_all
--   --simp only [this, exists_congr_prop, and_congr_left]
--   simp_rw [this] --Fails

--   -- Build y = z
--   have : ∀ x y z : ℕ, (y = z) ↔ (eqBase 0 3 2 1).eval (toWord ![y, x, z] 0) := by
--     intro x y z
--     rw [eqBase_iff]
--     simp_all
--   simp_rw [this]

--   -- Build x = y ∧ y = z using intersection
--   have : ∀ x y z : ℕ,
--       ((eqBase 0 3 1 0).eval (toWord ![y, x, z] 0) ∧
--        (eqBase 0 3 2 1).eval (toWord ![y, x, z] 0)) ↔
--       ((eqBase 0 3 1 0).intersection (eqBase 0 3 2 1)).eval (toWord ![y, x, z] 0) := by
--     intro x y z
--     rw [← intersection_iff]
--   simp_rw [this]

--   -- Build ∃ z
--   have : ∀ x y, (∃ z, (eqBase 0 3 1 0).intersection (eqBase 0 3 2 1)).eval (toWord ![y, x, z] 0) ↔
--       (project ((eqBase 0 3 1 0).intersection (eqBase 0 3 2 1))).fixLeadingZeros.toDFA.eval (toWord ![y, x] 0) := by
--     intro x y
--     rw [project_iff]
--     exact equality_respectZero
--   simp_rw [this]

--   -- Build ∃ y
--   have : ∀ x, (∃ y, (project ((eqBase 0 3 1 0).intersection (eqBase 0 3 2 1))).fixLeadingZeros.toDFA.eval (toWord ![y, x] 0)) ↔
--       (project (project ((eqBase 0 3 1 0).intersection (eqBase 0 3 2 1))).fixLeadingZeros.toDFA).fixLeadingZeros.toDFA.eval (toWord ![x] 0) := by
--     intro x
--     rw [project_iff]
--     apply project_fix_toDFA_respectZero
--     exact equality_respectZero
--   simp_rw [this]

--   -- Build ∃ x
--   have : (∃ x, (project (project ((eqBase 0 3 1 0).intersection (eqBase 0 3 2 1))).fixLeadingZeros.toDFA).fixLeadingZeros.toDFA.eval (toWord ![x] 0)) ↔
--       (project (project (project ((eqBase 0 3 1 0).intersection (eqBase 0 3 2 1))).fixLeadingZeros.toDFA).fixLeadingZeros.toDFA).fixLeadingZeros.toDFA.eval (toWord ![] 0) := by
--     rw [project_iff]
--     apply project_fix_toDFA_respectZero
--     exact equality_respectZero
--   simp_rw [this]

--   -- Check result
--   native_decide

-- #eval (project (project (project ((eqBase 0 3 1 0).intersection (eqBase 0 3 2 1))).fixLeadingZeros.toDFA).fixLeadingZeros.toDFA).fixLeadingZeros.toDFA.eval (toWord ![] 0)

-- -- ∀ x : ℕ, ∀ y : ℕ, x = y ∨ ¬ (x = y)
-- def eqDFA := eqBase 0 2 1 0                    -- DFA for x = y
-- def neqDFA := eqDFA.negate                      -- DFA for x ≠ y
-- def unionDFA := eqDFA.union neqDFA                -- DFA for x = y ∨ x ≠ y
-- def finalDFA :=
--   (project
--     (project unionDFA.negate).fixLeadingZeros.toDFA.negate).fixLeadingZeros.toDFA

-- #eval finalDFA.eval (toWord ![] 0)  -- memory out

def addDFA := addBase 0 3 0 1 2 -- DFA for x + y = z

#eval (project (project (project addDFA).fixLeadingZeros.toDFA).fixLeadingZeros.toDFA).eval (toWord ![] 0) -- Successful
