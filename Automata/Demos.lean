import Mathlib.Tactic
import Automata.Equality_new
import Automata.Addition
import Automata.Projection_new
import Automata.Boolean
import Automata.ThueMorse
import Automata.Collapse

theorem zero_is_zero : 0 = 0 := by
  apply (eqBase_iff_equal 0 2 (fun _ => 0) 0 1).mpr
  native_decide


theorem foo : 100000 = 100000 := by
  apply (eqBase_iff_equal 0 2 (fun _ => 100000) 0 1).mpr
  native_decide

theorem pro : ∃ (x : ℕ), x = 0 := by
  have : ∀ x : ℕ, x = 0 ↔ (eqBase 0 2 0 1).eval (toWord (recover_value 0 x (fun _ => 0)) 0) := by
    intro x
    have := eqBase_iff_equal 0 2 (recover_value 0 x (fun _ => 0)) 0 1
    simp[recover_value, Fin.insert] at this
    simp[recover_value, Fin.insert]
    exact this

  -- rw[this]

  have : ∃ (x : ℕ), DFAO.eval (eqBase 0 2 0 1) (toWord (recover_value 0 x (fun _ => 0)) 0) = true := by
    refine (project_iff (fun x ↦ 0) 0 (eqBase 0 2 0 1) ?_).mp ?_
    . exact equality_respectZero
    . native_decide

  rcases this with ⟨x, hx⟩
  use x
  rw[this]
  exact hx

theorem prox : ∃ (x : ℕ), x = x := by
  have : ∀ x : ℕ, x = x ↔ (eqBase 0 2 0 1).eval (toWord (recover_value 1 x (recover_value 0 x (fun _ => 1))) 0) := by
    intro x
    have := eqBase_iff_equal 0 2 (recover_value 1 x (recover_value 0 x (fun _ => 1))) 0 1
    convert this
  have : ∀ x : ℕ, (eqBase 0 2 0 1).eval (toWord (recover_value 1 x (recover_value 0 x (fun _ => 1))) 0) ↔ (collapse 1 0 (eqBase 0 2 0 1)).eval ((toWord (recover_value 1 x (recover_value 0 x (fun _ => 1))) 0).map (remove_index 1)) := by
    intro x
    sorry
  sorry
