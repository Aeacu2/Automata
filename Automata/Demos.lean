import Mathlib.Tactic
import Automata.Equality
import Automata.Addition
import Automata.Projection
import Automata.Boolean
import Automata.ThueMorse

namespace Mathlib.Tactic

open Lean Meta Elab Elab.Tactic

elab "reduce!" loc?:(ppSpace Parser.Tactic.location)? : tactic =>
  runDefEqTactic (fun _ e => reduceAll e) loc? "reduce!"

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
set_option maxRecDepth 5000

theorem demo : ¬ ∃ x : ℕ, ¬ ∃ y, x = y := by
-- Build x = y
  have : ∀ x y : ℕ, x = y ↔ (eqBase 0 2 0 1).eval (toWord ![x, y] 0 ) := by
    intro x y
    have := eqBase_iff_equal 0 2 ![x, y] 0 1
    exact this
-- substitute
  simp_rw [this]

-- Build ∃ y, x = y
  have : ∀ x, ((∃ y, (eqBase 0 2 0 1).eval (toWord ![x, y] 0)) ↔ (project 1 (eqBase 0 2 0 1)).fixLeadingZeros.toDFA.eval (toWord ![x] 0)) := by
    intro x
    have := project_iff ![x] 1 (eqBase 0 2 0 1) (by exact equality_respectZero)
    rw [this]
    have : ∀ x_1, (Fin.insertNth 1 x_1 ![x]) = ![x, x_1] := by
      intro x_1
      exact List.ofFn_inj.mp rfl
    simp_rw [this]
-- substitute
  simp_rw [this]

-- Build ¬ ∃ y, x = y
  have : ∀ x, ((¬ (project 1 (eqBase 0 2 0 1)).fixLeadingZeros.toDFA.eval (toWord ![x] 0) = true) ↔ (project 1 (eqBase 0 2 0 1)).fixLeadingZeros.toDFA.negate.eval (toWord ![x] 0) = true) := by
    intro x
    rw[DFA.negate_eval]
    simp only [Nat.reduceAdd, Fin.isValue, Nat.succ_eq_add_one, Bool.not_eq_true,
      Bool.not_eq_eq_eq_not, Bool.not_true]
-- substitute
  simp_rw [this]

--Build ∃ x, ¬ ∃ y, x = y
  have : (∃ x, DFAO.eval (project 1 (eqBase 0 2 0 1)).fixLeadingZeros.toDFA.negate (toWord ![x] 0) = true) ↔ ((project 0 (project 1 (eqBase 0 2 0 1)).fixLeadingZeros.toDFA.negate).fixLeadingZeros.toDFA.eval (toWord ![] 0) = true) := by
      have := project_iff ![] 0 (project 1 (eqBase 0 2 0 1)).fixLeadingZeros.toDFA.negate (by
        rw[DFA.respectZero]
        intro x m
        simp[DFA.negate_eval, NFA.toDFA_eval]
        have := project_fix_respectZero (eqBase 0 2 0 1)
        specialize this 1 (by exact equality_respectZero)
        exact Bool.coe_iff_coe.mp (this x m)
      )
      have rw2 : ∀ x, (Fin.insertNth 0 x ![]) = @Matrix.vecCons ℕ 0 x ![]  := by
        intro x
        simp_all only [Nat.reduceAdd, Fin.isValue, Nat.succ_eq_add_one, Fin.insertNth_zero']
        rfl
      simp_rw [rw2] at this
      rw[← this, NFA.toDFA_eval]
-- substitute
  simp_rw[this]

-- Finally, build ¬ ∃ x, ¬ ∃ y, x = y
  have : ¬ (project 0 (project 1 (eqBase 0 2 0 1)).fixLeadingZeros.toDFA.negate).fixLeadingZeros.toDFA.eval (toWord ![] 0) =
    true ↔ (project 0 (project 1 (eqBase 0 2 0 1)).fixLeadingZeros.toDFA.negate).fixLeadingZeros.toDFA.negate.eval (toWord ![] 0) = true := by
    rw[DFA.negate_eval]; simp
-- substitute
  simp_rw[this]
-- Check result
  rfl'

-- Check result
  -- native_decide

-- set_option maxRecDepth 5000

-- #reduce (proofs := true) (types := true) (DFAO.eval (project 0 (project 1 (eqBase 0 2 0 1)).fixLeadingZeros.toDFA.negate).fixLeadingZeros.toDFA.negate (toWord ![] 0) = true)

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
