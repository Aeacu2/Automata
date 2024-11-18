import Mathlib.Tactic
import Mathlib.Data.List.Basic

theorem List.replicate_append_length (x : List α) : (List.replicate n a ++ x).length = n + x.length := by
  rw[List.length_append, List.length_replicate]

theorem List.getElem_of_replicate_append_left (x : List α) (h : i < n) : (List.replicate n a ++ x)[i]'(by simp only [List.length_append, List.length_replicate]; omega) = a := by
  rw[List.getElem_append_left]
  rw[List.getElem_replicate]
  simpa only [List.length_replicate]

theorem List.getElem_of_replicate_append_right (x : List α) (h : i < x.length) : (List.replicate n a ++ x)[i + n]'(by simp only [List.length_append, List.length_replicate]; omega) = x[i]'(by omega) := by
  rw[List.getElem_append_right]
  . simp only [length_replicate, add_tsub_cancel_right]
  . simp only [length_replicate, add_lt_iff_neg_right, not_lt_zero', not_false_eq_true]
  . simpa only [length_replicate, add_tsub_cancel_right]

theorem List.replciate_append_elem (n: ℕ) (l: List ℕ) :
  x ∈ ((List.replicate n a) ++ l) → x = a ∨ x ∈ l := by
  intro h
  simp only [List.mem_append, List.replicate] at h
  rcases h with (h | h)
  . left
    have : x ∈ [a] := List.replicate_subset_singleton n a h
    simp_all only [mem_replicate, ne_eq, mem_singleton]
  . right
    exact h

theorem List.eq_of_replicate_append_eq {x y : List α} (h : List.replicate n a ++ x = List.replicate n a ++ y) : x = y := by
  induction n with
  | zero =>
    rw[List.replicate_zero, List.nil_append] at h
    exact h
  | succ n ih =>
    rw[List.replicate_succ, List.cons_append] at h
    injection h with h1 h2
    exact ih h2

theorem List.replicate_append_add (n m : ℕ) (x : List α) : List.replicate n a ++ List.replicate m a ++ x = List.replicate (n + m) a ++ x := by
  simp only [List.append_replicate_replicate]

theorem List.eq_diff_of_replicate_append_eq {x y : List α} (h : List.replicate m a ++ x = List.replicate n a ++ y) (hmn : m ≤ n) : x = List.replicate (n - m) a ++ y := by
  have: n = m + (n - m) := by omega
  rw[this] at h
  rw[← List.append_replicate_replicate, List.append_assoc] at h
  apply List.append_cancel_left h
