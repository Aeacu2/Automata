import Mathlib.Tactic
import Automata.DFA
import Automata.Input
import Automata.Vector
import Automata.Equality_Gen

/-
1. General Equality
2. The Collapse Problem
3. Fin operations? Mathlib weird
4. Casting!
5. Writeup?

-/

variable {α : Type} {n : ℕ} {b : ℕ}

-- Auxilliary functions for collapse
def tail (f: Fin (n+1) → α) : Fin n → α :=
  fun i => f (i.succ)

#check Fin.insertNth

def remove_index (i : Fin (n + 1)) (f: Fin (n + 1) → α):
   (Fin n → α) :=
    fun j => f (if j.val < i.val then j else ⟨j.val + 1, by omega⟩)

def recover_index (i : Fin (n + 1)) (k: Fin n) (f: Fin n → α):
   (Fin (n + 1) → α) :=
    fun j => if hlt : j < i then f ⟨j, by omega⟩ else if hgt : j > i then f ⟨j - 1, by omega⟩ else f k



theorem remove_recover (i : Fin (n + 1)) (k: Fin n) (f: Fin n → α) :
  remove_index i (recover_index i k f) = f := by
  ext x
  simp[remove_index, recover_index]
  split; simp only [Fin.coe_castSucc, Fin.eta, dite_eq_ite, ite_eq_then, not_lt]
  . intro h
    have : i.val ≤ x.val := by exact h
    omega
  . split
    . rename_i hsucc h
      have : x.val + 1 < i.val := by
        simp_all only [not_lt]
        exact h
      omega
    . split
      . rfl
      . rename_i h₁ h₂ h₃
        have : ¬ x.val + 1 < i.val := by
          simp_all only [not_lt]
          exact h₂
        have : ¬ i.val < x.val + 1 := by
          simp_all only [not_lt]
          exact h₃
        omega

theorem recover_remove (i : Fin (n + 1)) (k: Fin n) (f: Fin (n + 1) → α) (hf: f i = f k) (hik : i.val > k.val ) :
  recover_index i k (remove_index i f) = f := by
  ext x
  simp[remove_index, recover_index]
  split; simp only [Fin.coe_castSucc, Fin.eta, dite_eq_ite, ite_eq_then, not_lt]
  . split; simp_all
    . split
      .
        -- have : i.val < x.val := by omega

        omega
      . rcases x with ⟨x, hx⟩
        cases x; contradiction
        rfl
    . simp_all only [Fin.coe_eq_castSucc, gt_iff_lt, not_lt]
      have : x = i := by omega
      subst this
      simp_all only [le_refl]

def collapse (i : Fin (n+1)) (k : Fin n) (dfa : DFA (Fin (n+1) → α) state) : DFA (Fin n → α) state := {
  transition := fun a q => dfa.transition (recover_index i k a) q
  start := dfa.start
  output := dfa.output
}

theorem collapse_transFrom (dfa : DFA (Fin (n + 1) → α) state) (i : Fin (n + 1)) (k: Fin n) (l : List (Fin n → α))
  : dfa.transFrom (l.map (recover_index i k)) = (collapse i k dfa).transFrom l := by
  induction l
  case nil =>
    simp_all only [List.map_nil]
    rfl
  case cons x xs ih =>
    simp_all only [collapse, DFAO.transFrom]

theorem collapse_evalFrom (dfa : DFA (Fin (n + 1) → α) state) (i : Fin (n + 1)) (k: Fin n) (l : List (Fin n → α)) (s : state)
  : dfa.evalFrom (l.map (recover_index i k)) s = (collapse i k dfa).evalFrom l s := by
  simp only [DFAO.evalFrom, collapse_transFrom]
  rfl

theorem collapse_eval (dfa : DFA (Fin (n + 1) → α) state) (i : Fin (n + 1)) (k: Fin n) (l : List (Fin n → α))
  : dfa.eval (l.map (recover_index i k)) = (collapse i k dfa).eval l := collapse_evalFrom dfa i k l dfa.start

theorem collapse_correct (dfa : DFA (Fin (n + 1) → Fin (b + 2)) state) (l : List ℕ) (i : Fin (n + 1)) (k: Fin n)  (hlLen : l.length = n + 1) (hl : l[i] = l[k]) (hik : i.val > k.val) :
  dfa.eval (inputToBase (b + 2) (by omega) l (hlLen)) = (collapse i k dfa).eval (((inputToBase (b + 2) (by omega) l (hlLen))).map (remove_index i)) := by
  rw[← collapse_eval]
  congr

  have := @eqInput_if_equal (n+1) (b) l hlLen ⟨i, by omega⟩ ⟨k, by omega⟩ hl

  simp only [List.map_map]
  suffices : ∀ v ∈ (inputToBase (b + 2) _ l hlLen), (recover_index i k ∘ remove_index i) v = v
  .
    ext j v
    constructor
    . intro h
      simp_all
      apply this
      exact List.getElem?_mem h
    . intro h
      simp_all
      rcases h with ⟨v', ⟨h₁, h₂⟩⟩
      rw[h₁, ← this v', h₂]
      . exact List.getElem?_mem h₁

  intro v hv
  dsimp
  rw[recover_remove]
  specialize this v hv
  .
    simp_all only [Fin.getElem_fin, gt_iff_lt, Fin.eta, Fin.coe_eq_castSucc]
    ext : 1
    simp_all only
    rfl
  . exact hik


#check @dcast
