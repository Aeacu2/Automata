import Mathlib.Tactic
import Mathlib.Data.List.Basic
import Mathlib.Data.Nat.Digits
import Automata.DFA
import Automata.NFA
import Automata.Input
import Automata.Addition


-- Auxilliary theorems for recover
theorem finLt (m : Fin (n+1)) (b : ℕ) : b < m.val → b < n := by omega

theorem finPred (m : Fin n) (a : Fin n) (h : a > m): a.val - 1 < n - 1 := by omega


-- Auxilliary function for project
def recover (m : Fin (n + 1)) (x: Fin k):
  (Fin n → Fin k) → (Fin (n + 1) → Fin k) :=
    fun i => fun j => if h1: j.val < m.val then i ⟨j.val, finLt m j.val h1⟩
      else if h2: j.val > m.val then i ⟨j.val - 1, finPred m j h2⟩ else x



def project (dfa : DFA (Fin (n+1) → Fin k) state) (m : Fin (n+1)) [DecidableEq state] :
  NFA (Fin n → Fin k) state := {
  transition :=
  fun a q => ⟨(List.map (fun (x : Fin k) => dfa.transition (recover m x a) q)
    (FinEnum.toList (Fin k))).dedup, by apply List.nodup_dedup⟩
  start := ⟨[dfa.start], by exact List.nodup_singleton dfa.start⟩
  output := dfa.output
}

-- Problem: exists x, 1 + 1 = x?
#eval (project (addBase 2)  2).eval [fun _ => 1]
-- Fix:
#eval (project (addBase 2) 2).eval [fun _ => 0, fun _ => 1]

theorem DFAO.bounded_accept [Fintype state] (dfao : DFAO (Fin n → Fin (b+2)) state out) (x : List (Fin n → Fin (b+2))) (o: out)(h: ∀ (x : List (Fin n → Fin (b+2))), dfao.eval x = o → (∀ y, (∃ m, y = (List.replicate m (fun _ => 0)) ++ x) →  dfao.eval y = o)) : ∀ z, (∃ k, z = (List.replicate k (fun _ => 0)) ++ x) ∧ dfao.eval z = o → dfao.eval (List.replicate (Fintype.card state) (fun _ => 0) ++ x) = o := by
  rintro z ⟨⟨k, hz⟩, hzo⟩
  by_cases hkstate : k ≤ Fintype.card state
  . apply h z
    . exact hzo
    . use Fintype.card state - k
      rw[hz]
      rw[← List.append_assoc, ← List.replicate_add]
      subst hzo hz
      simp only [List.append_cancel_right_eq, List.replicate_inj, or_true, and_true]
      omega

  simp only [not_le] at hkstate
  -- Question: How to get this kind of descent argument work in lean?
  . induction' hk : k - Fintype.card state using Nat.strong_induction_on  with d ih generalizing k z
    have hzlen : Fintype.card state ≤ z.length := by
      rw[hz]
      simp only [List.length_append, List.length_replicate]
      omega

    obtain ⟨a, b', c, hzabc, hablen, hne, hy⟩ := dfao.pumping_lemma_eval hzo hzlen
    have hacl : dfao.eval (a ++ c) = o := by
      apply hy
      simp only [Language.mem_mul, exists_exists_and_exists_and_eq_and, List.append_assoc]
      use a, (by exact rfl), [], (by exact Language.nil_mem_kstar {b'}), c, (by exact rfl)
      simp only [List.nil_append]
    -- have hblen : 0 < b'.length := by
    --   exact List.length_pos_of_ne_nil hne

    have habzero' : ∀ i, ∀ (hi: i < a.length + b'.length),  z[i]'(by omega) = fun _ => 0 := by
      intro i hi
      have hik : i < k := by
        omega
      simp only [hz]
      rw[List.getElem_append_left, List.getElem_replicate]
      rwa[List.length_replicate]
    have habzero : ∀ i, ∀ (hi: i < a.length + b'.length),  (a ++ b')[i]' (by rw[List.length_append]; exact hi) = fun _ => 0 := by
      intro i hi
      rw[← List.getElem_append_left (a++b') c]
      -- rw[← hzabc] Why?
      subst hzabc
      specialize habzero' i hi
      -- Why not exact?
      simp_all

    have hazero : ∀ i, ∀ (hi: i < a.length),  a[i]' (by omega) = fun _ => 0 := by
      intro i hi
      rw[← List.getElem_append_left a b']
      apply habzero i
      . omega
    have hbzero : ∀ i, ∀ (hi: i < b'.length),  b'[i]' (by omega) = fun _ => 0 := by
      intro i hi
      -- rw[← List.getElem_append_right' a b'] Why?
      have : (a ++ b')[a.length + i]'(by rw[List.length_append]; omega) = b'[i] := by
        rw[List.getElem_append_right']
        simp only [add_tsub_cancel_left]
        omega
      rw[← this]
      apply habzero (a.length + i)
      omega
    have har: a = List.replicate a.length (fun _ => 0) := by
      apply List.ext_getElem
      . simp
      . aesop
        -- intro n_1 h₁ h₂
        -- subst hzabc hacl hk
        -- simp_all only [ne_eq, List.append_assoc, forall_exists_index, List.append_cancel_right_eq, List.replicate_inj,
        -- or_true, and_true, forall_eq', true_implies, List.getElem_replicate]
    -- AESOP wouldn't work again, even on the same problem!
    -- have har: a = List.replicate a.length (fun _ => 0) := by
    --   apply List.ext_getElem
    --   . simp
    --   . aesop
    have hbr: b' = List.replicate b'.length (fun _ => 0) := by
      apply List.ext_getElem
      . simp
      . intro n_1 h₁ h₂
        simp only [List.getElem_replicate]
        exact hbzero n_1 h₁
    have habk : a.length + b'.length < k := by omega
    have hk : (List.replicate k (fun x : Fin n → Fin (b+2) => 0)) = (List.replicate (a.length + b'.length) (fun x : Fin n → Fin (b+2) => 0)) ++ (List.replicate (k - a.length - b'.length) (fun x : Fin n → Fin (b+2) => 0)) := by
      simp[List.append_replicate_replicate]
      omega
    -- Why Fail? subst hk
    have hcx : c = (List.replicate (k - a.length - b'.length) (fun _ => 0)) ++ x := by
      rw[har, hbr] at hzabc
      rw[hzabc] at hz
      simp only [List.append_replicate_replicate] at hz
      -- AHhhh! NO!
      -- rw[hk] at hz
      sorry
    have hac : a ++ c = List.replicate (k - b'.length) (fun _ => 0) ++ x := by
      rw[hcx, har]
      rw[← List.append_assoc]
      simp only [List.length_replicate, List.append_replicate_replicate,
        List.append_cancel_right_eq, List.replicate_inj, AddLeftCancelMonoid.add_eq_zero,
        List.length_eq_zero, or_true, and_true]
      omega
    by_cases hkb : k - b'.length ≤ Fintype.card state
    . apply h (a ++ c)
      . exact hacl
      . -- subst/rw hac !!!
        use Fintype.card state - (k - b'.length)
        simp only [hac]
        rw[← List.append_assoc]
        simp only [List.append_replicate_replicate, List.append_cancel_right_eq, List.replicate_inj,
          or_true, and_true]
        omega
    . simp only [not_le] at hkb
      have hblen : 0 < b'.length := by
        exact List.length_pos_of_ne_nil hne

      specialize ih (k - b'.length - Fintype.card state) (by omega) (a ++ c) (hacl) (k - b'.length) hac hkb rfl

      exact ih

#check DFAO.bounded_accept

--Previous version of recover and project
-- def recover' (h: n ≥ 1) (m : Fin n) (x: Fin k):
--   (Fin (n-1) → Fin k) → (Fin n → Fin k) :=
--     fun i => fun j => if h1: j.val < m.val then i ⟨j.val, finLt m j.val h h1⟩
--       else if h2: j.val > m.val then i ⟨j.val - 1, finPred m j h2⟩ else x

-- def project' (dfa : DFA (Fin n → Fin k) state) (h: n ≥ 1) (m : Fin n) [BEq state] :
--   NFA (Fin (n - 1) → Fin k) state := {
--   transition :=
--   fun a q => (List.map (fun (x : Fin k) => dfa.transition (recover' h m x a) q)
--     (FinEnum.toList (Fin k)))
--   start := [dfa.start]
--   output := dfa.output
-- }


-- #eval (project' (addBase 2) (by norm_num) 2).eval [fun (_ : Fin 2) => 1]

-- #eval (project' (addBase 2) (by norm_num) 2).eval [fun _ => 0, fun _ => 1]
