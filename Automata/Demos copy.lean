import Mathlib.Tactic
import Automata.Equality
import Automata.Projection_new
import Automata.Boolean

-- #eval DFAO.eval
--     (project
--             (project
--                   ((eqBase 0 2 1 0).negate.intersection
--                     (eqBase 0 2 1 0))).fixLeadingZeros.toDFA).fixLeadingZeros.toDFA.negate
--     (toWord ![] 0)

-- ∀ x, ∀ y, x = y ∨ x ≠ y
theorem demo_fail : ¬ ∃ x : ℕ, ∃ y, ¬ (x = y) ∧ x = y := by
-- Build x = y
  have : ∀ x y : ℕ, x = y ↔ (eqBase 0 2 1 0).eval (toWord ![y, x] 0 ) := by
    intro x y
    have := eqBase_iff 0 2 ![y, x] 1 0
    rw[this]
    simp_all
-- substitute
  simp_rw [this]
-- Build ¬ (x = y)
  have : ∀ x y, ¬ (eqBase 0 2 1 0).eval (toWord ![y, x] 0) = true ↔ (eqBase 0 2 1 0).negate.eval (toWord ![y, x] 0) = true := by
    intro x y
    have := negate_iff (eqBase 0 2 1 0) (toWord ![y, x] 0)
    rw[this]
-- substitute
  simp_rw [this]
-- Build ¬ (x = y) ∧ x = y
  have : ∀ x y, ((eqBase 0 2 1 0).negate.eval (toWord ![y, x] 0) = true ∧ (eqBase 0 2 1 0).eval (toWord ![y, x] 0) = true) ↔ ((eqBase 0 2 1 0).negate.intersection (eqBase 0 2 1 0)).eval (toWord ![y, x] 0) = true  := by
    intro x y
    have := intersection_iff (eqBase 0 2 1 0).negate (eqBase 0 2 1 0) (toWord ![y, x] 0)
    rw[this]
-- substitute
  simp_rw [this]

-- Build ∃ y, ¬ (x = y) ∧ x = y
  have : ∀ x, ((∃ y, ((eqBase 0 2 1 0).negate.intersection (eqBase 0 2 1 0)).eval (toWord ![y, x] 0)) ↔ (project ((eqBase 0 2 1 0).negate.intersection (eqBase 0 2 1 0))).fixLeadingZeros.toDFA.eval (toWord ![x] 0)) := by
    intro x
    have := project_iff ![x] ((eqBase 0 2 1 0).negate.intersection (eqBase 0 2 1 0)) (by
      apply DFA.intersection_respectZero
      . apply DFA.negate_respectZero
        exact equality_respectZero
      . exact equality_respectZero
    )
    rw[this]
-- substitute
  simp_rw [this]

-- Build ∃ x, ∃ y, ¬ (x = y) ∧ x = y
  have : (∃ x, (project ((eqBase 0 2 1 0).negate.intersection (eqBase 0 2 1 0))).fixLeadingZeros.toDFA.eval (toWord ![x] 0) = true) ↔ ((project (project ((eqBase 0 2 1 0).negate.intersection (eqBase 0 2 1 0))).fixLeadingZeros.toDFA).fixLeadingZeros.toDFA.eval (toWord ![] 0) = true) := by
    have := project_iff ![] (project ((eqBase 0 2 1 0).negate.intersection (eqBase 0 2 1 0))).fixLeadingZeros.toDFA (by

      have : ((eqBase 0 2 1 0).negate.intersection (eqBase 0 2 1 0)).respectZero := by
        apply DFA.intersection_respectZero
        . apply DFA.negate_respectZero
          exact equality_respectZero
        . exact equality_respectZero
      exact project_fix_toDFA_respectZero ((eqBase 0 2 1 0).negate.intersection (eqBase 0 2 1 0)) this
    )
    rw[this]
-- substitute
  simp_rw[this]

-- Build ¬ ∃ x, ∃ y, ¬ (x = y) ∧ x = y
  have : (¬ (project (project ((eqBase 0 2 1 0).negate.intersection (eqBase 0 2 1 0))).fixLeadingZeros.toDFA).fixLeadingZeros.toDFA.eval (toWord ![] 0) = true) ↔ (project (project ((eqBase 0 2 1 0).negate.intersection (eqBase 0 2 1 0))).fixLeadingZeros.toDFA).fixLeadingZeros.toDFA.negate.eval (toWord ![] 0) = true := by
    have := negate_iff ((project (project ((eqBase 0 2 1 0).negate.intersection (eqBase 0 2 1 0))).fixLeadingZeros.toDFA).fixLeadingZeros.toDFA) (toWord ![] 0)
    rw[this]
-- substitute
  simp_rw[this]
  sorry
  --rfl'
-- Check result
  -- native_decide


set_option maxRecDepth 5000

-- ∀ x, ∃ y, x = y
theorem demo : ∀ x : ℕ, ∃ y, x = y := by
-- convert expression
  suffices ¬ ∃ x : ℕ, ¬ ∃ y, x = y by
    tauto
-- Build x = y
  have : ∀ x y : ℕ, x = y ↔ (eqBase 0 2 1 0).eval (toWord ![y, x] 0 ) := by
    intro x y
    rw[eqBase_iff]
    simp_all
-- substitute
  simp_rw [this]

-- Build ∃ y, x = y
  have : ∀ x, ((∃ y, (eqBase 0 2 1 0).eval (toWord ![y, x] 0)) ↔ (project  (eqBase 0 2 1 0)).fixLeadingZeros.toDFA.eval (toWord ![x] 0)) := by
    intro x
    rw[project_iff]
    exact equality_respectZero
-- substitute
  simp_rw [this]

-- Build ¬ ∃ y, x = y
  have : ∀ x, ((¬ (project (eqBase 0 2 1 0)).fixLeadingZeros.toDFA.eval (toWord ![x] 0) = true) ↔ (project (eqBase 0 2 1 0)).fixLeadingZeros.toDFA.negate.eval (toWord ![x] 0) = true) := by
    intro x
    rw[negate_iff]
-- substitute
  simp_rw [this]

--Build ∃ x, ¬ ∃ y, x = y
  have : (∃ x, DFAO.eval (project (eqBase 0 2 1 0)).fixLeadingZeros.toDFA.negate (toWord ![x] 0) = true) ↔ ((project (project (eqBase 0 2 1 0)).fixLeadingZeros.toDFA.negate).fixLeadingZeros.toDFA.eval (toWord ![] 0) = true) := by
      rw[project_iff]
      apply DFA.negate_respectZero
      apply project_fix_toDFA_respectZero
      exact equality_respectZero
-- substitute
  simp_rw[this]

-- Finally, build ¬ ∃ x, ¬ ∃ y, x = y
  have : ¬ (project (project (eqBase 0 2 1 0)).fixLeadingZeros.toDFA.negate).fixLeadingZeros.toDFA.eval (toWord ![] 0) =
    true ↔ (project (project (eqBase 0 2 1 0)).fixLeadingZeros.toDFA.negate).fixLeadingZeros.toDFA.negate.eval (toWord ![] 0) = true := by
    rw[negate_iff]
-- substitute
  simp_rw[this]
-- Check result
  rfl'


-- #eval (addBase 2 3 0 1 2).eval (toWord ![20, 2, 22] 2)

-- theorem zero_is_zero : 0 = 0 := by
--   apply (eqBase_iff_equal 0 2 (fun _ => 0) 0 1).mpr
--   native_decide

-- #eval (project 1 (eqBase 0 2 0 1)).fixLeadingZeros.eval (toWord ![1] 0)

-- theorem foo : 100000 = 100000 := by
--   apply (eqBase_iff_equal 0 2 (fun _ => 100000) 0 1).mpr
--   native_decide

-- theorem pro : ∃ (x : ℕ), x = 0 := by

--   have : ∀ x : ℕ, x = 0 ↔ (eqBase 0 2 0 1).eval (toWord (Fin.insertNth 0 x (fun _ => 0)) 0) := by
--     intro x
--     have := eqBase_iff_equal 0 2 (Fin.insertNth 0 x (fun _ => 0)) 0 1
--     simp[Fin.insertNth, Fin.insert] at this
--     simp[Fin.insertNth, Fin.insert]
--     exact this

--   simp only [this]

--   have : ∃ (x : ℕ), DFAO.eval (eqBase 0 2 0 1) (toWord (Fin.insertNth 0 x (fun _ => 0)) 0) = true := by
--     refine (project_iff (fun x ↦ 0) 0 (eqBase 0 2 0 1) ?_).mp ?_
--     . exact equality_respectZero
--     . native_decide

--   rcases this with ⟨x, hx⟩
--   use x


-- theorem proxy : ∃ x : ℕ, ∃ y, x = y := by
--   have : ∀ x y : ℕ, x = y ↔ (eqBase 0 2 0 1).eval (toWord ![x, y] 0 ) := by
--     intro x y
--     have := eqBase_iff_equal 0 2 ![x, y] 0 1
--     exact this
--   simp_rw [this]
--   have : ∀ x, ((∃ y, (eqBase 0 2 0 1).eval (toWord ![x, y] 0)) ↔ (project 1 (eqBase 0 2 0 1)).fixLeadingZeros.eval (toWord ![x] 0)) := by
--     intro x
--     have := project_iff ![x] 1 (eqBase 0 2 0 1) (by exact equality_respectZero)
--     rw [this]
--     have : ∀ x_1, (Fin.insertNth 1 x_1 ![x]) = ![x, x_1] := by
--       intro x_1
--       exact List.ofFn_inj.mp rfl
--     simp_rw [this]
--   apply exists_congr this |>.mpr
--   have := project_iff ![] 0 (project 1 (eqBase 0 2 0 1)).fixLeadingZeros.toDFA (by
--     rw[DFA.respectZero]
--     intro x m
--     rw[NFA.toDFA_eval, NFA.toDFA_eval]
--     have := project_fix_respectZero (eqBase 0 2 0 1)
--     specialize this 1 (by exact equality_respectZero)
--     rw[this]
--   )

--   have rw: (∃ x, DFAO.eval (project 1 (eqBase 0 2 0 1)).fixLeadingZeros.toDFA (toWord (Fin.insertNth 0 x ![]) 0) = true) ↔ ∃ x, (project 1 (eqBase 0 2 0 1)).fixLeadingZeros.eval (toWord (Fin.insertNth 0 x ![]) 0) = true := by
--     simp
--     constructor
--     . intro h
--       rcases h with ⟨x, hx⟩
--       use x
--       rw[← NFA.toDFA_eval]
--       exact hx
--     . intro h
--       rcases h with ⟨x, hx⟩
--       use x
--       rw[NFA.toDFA_eval]
--       exact hx
--   rw [rw] at this
--   have rw2 : ∀ x, (Fin.insertNth 0 x ![]) = @Matrix.vecCons ℕ 0 x ![]  := by
--     intro x
--     simp_all only [Nat.reduceAdd, Fin.isValue, Nat.succ_eq_add_one, Fin.insertNth_zero']
--     rfl
--   simp_rw [rw2] at this
--   apply this.mp
--   native_decide

-- #check exists_congr
-- theorem prox : ∃ (x : ℕ), x = x := by
--   have : ∀ x : ℕ, x = x ↔ (eqBase 0 2 0 1).eval (toWord (Fin.insertNth 1 x (Fin.insertNth 0 x (fun _ => 1))) 0) := by
--     intro x
--     have := eqBase_iff_equal 0 2 (Fin.insertNth 1 x (Fin.insertNth 0 x (fun _ => 1))) 0 1
--     convert this

--   apply exists_congr this |>.mpr
--   have : ∀ x : ℕ, (eqBase 0 2 0 1).eval (toWord (Fin.insertNth 1 x (Fin.insertNth 0 x (fun _ => 1))) 0) ↔ (collapse 1 0 (eqBase 0 2 0 1)).eval ((toWord (Fin.insertNth 1 x (Fin.insertNth 0 x (fun _ => 1))) 0).map (remove_index 1)) := by
--     intro x
--     sorry
--   sorry
