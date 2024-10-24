import Mathlib.Tactic
import Mathlib.Data.List.Basic
import Automata.DFA
import Automata.NFA
import Automata.Input
import Mathlib.Data.Nat.Digits

def thueMorse : DFAO (Fin 2) (Fin 2) (Fin 2) := {
  transition := fun a s => a + s
  start := 0
  output := fun x => x
}

def thueMorse0 : DFA (Fin 2) (Fin 2) := thueMorse.toDFA 0

def thueMorse1 : DFA (Fin 2) (Fin 2) := thueMorse.toDFA 1

def trueDFA: DFA (Fin 0) (Fin 1) := {
  transition := fun _ s => s
  start := 0
  output := fun _ => true
}

def falseDFA: DFA (Fin 0) (Fin 1) := {
  transition := fun _ s => s
  start := 0
  output := fun _ => false
}

def eqBase (k: ℕ) : DFA (Fin 2 → Fin k) (Fin 2) := {
  transition := fun f s => match s with
    | 0 => if (f 0).val = f 1 then 0 else 1
    | 1 => 1
  start := 0
  output := fun x => x == 0
}

def eqBase' (k: ℕ) (a b n : ℕ) (ha: a < n) (hb: b < n): DFA (Fin n → Fin k) (Fin 2) := {
  transition := fun f s => match s with
    | 0 => if (f ⟨a, ha⟩).val == f ⟨b, hb⟩ then 0 else 1
    | 1 => 1
  start := 0
  output := fun x => x == 0
}

/- Try to prove eqBase is correct

1. DFA accepts iff f 0 = f 1 for all f ∈ input
2. input natural numbers are equal iff f 0 = f 1 for all f ∈ input

-/

--Start of Step 1
--Right to Left
theorem eqBase_if_equal_aux (b : ℕ) (input: List (Fin 2 → Fin b)):
  (∀ f ∈ input, (f 0).val = f 1) → (eqBase b).evalFrom input 0 := by
  intro h
  induction input
  case nil =>
    simp[eqBase, DFAO.evalFrom, DFAO.transFrom]
  case cons f fs ih =>
    have h1 := h f
    simp only [List.mem_cons, true_or, Fin.isValue, true_implies] at h1
    simp only [DFAO.evalFrom, DFAO.transFrom, Fin.isValue]
    have: ((eqBase b).transition f 0) = 0 := by
      simp only [eqBase, Fin.isValue, beq_iff_eq, h1, ↓reduceIte]
    rw[this]
    apply ih
    intro f' hf'
    apply h
    simp only [List.mem_cons, or_true, hf']


-- Left to right, much harder
theorem eqBase_trans_zero (k : ℕ) (state : Fin 2) (f : Fin 2 → Fin k) :
  (eqBase k).transition f state = 0 ↔ state = 0 ∧ (f 0).val = f 1 := by
  simp only [eqBase, Fin.isValue, beq_iff_eq]
  split <;> simp

/- A Longer proof, useless
example (k : ℕ) (state : Fin 2) (f : Fin 2 → Fin k) :
  (eqBase k).transition f state = 0 ↔ state = 0 ∧ (f 0).val == f 1 := by
  constructor
  intro h1
  simp[eqBase] at h1
  constructor
  . by_contra h
    have: state = 1 := by exact Fin.eq_one_of_neq_zero state h
    simp[this] at h1
  . simp only [Fin.isValue, beq_iff_eq]
    have: ¬state = 0 → state = 1 := by intro hns; exact Fin.eq_one_of_neq_zero state hns
    have: state = 0 ∨ state = 1 := by tauto
    rcases this with hs | hs
    . simp only [hs, Fin.isValue, ite_eq_then, one_ne_zero, imp_false, Decidable.not_not] at h1
      exact h1
    . simp only [hs, Fin.isValue, one_ne_zero] at h1
  intro h
  rcases h with ⟨h1, h2⟩
  simp only [Fin.isValue, beq_iff_eq] at h2
  simp only [eqBase, Fin.isValue, beq_iff_eq, ↓reduceIte, h1, h2]
-/


theorem eqBase_transFrom_zero (k : ℕ) (state: Fin 2) (l : List (Fin 2 → Fin k)) :
  (eqBase k).transFrom l state = 0 ↔ state = 0 ∧ ∀ f ∈ l, (f 0).val = f 1 := by
  induction l generalizing state
  case nil =>
    simp[eqBase, DFAO.transFrom]
  case cons f fs ih =>
    simp[DFAO.transFrom]
    specialize ih ((eqBase k).transition f state)
    constructor
    . intro h
      have:= ih.mp h
      rcases this with ⟨h1, h2⟩
      have:= (eqBase_trans_zero k state f).mp h1
      rcases this with ⟨h3, h4⟩
      constructor
      . exact h3
      . constructor
        . simp only [Fin.isValue, beq_iff_eq] at h4
          exact h4
        . exact h2
    . intro h
      rcases h with ⟨h1, h2, h3⟩
      apply ih.mpr
      constructor
      . apply (eqBase_trans_zero k state f).mpr
        constructor
        . exact h1
        . simp only [Fin.isValue, beq_iff_eq]
          exact h2
      . exact h3

theorem eqInput_if_eqBase_aux (b : ℕ) (input: List (Fin 2 → Fin b)):
  (eqBase b).transFrom input 0 = 0 → (∀ f ∈ input, (f 0).val = f 1) := by
  intro h
  exact (eqBase_transFrom_zero b 0 input).mp h |>.2

theorem eqInput_if_eqBase (b : ℕ) (input: List (Fin 2 → Fin b)):
  (eqBase b).evalFrom input 0 → (∀ f ∈ input, (f 0).val = f 1) := by
  intro h
  have:= eqInput_if_eqBase_aux b input
  apply this
  simp[DFAO.evalFrom, DFAO.output, eqBase] at h
  apply h

-- End of Left to right, final step 1 statement:
theorem eqBase_iff_eqInput (b : ℕ) (input: List (Fin 2 → Fin b)):
  (eqBase b).eval input ↔ (∀ f ∈ input, (f 0).val = f 1) := by
  constructor
  . apply eqInput_if_eqBase b input
  . apply eqBase_if_equal_aux b input

-- Start of step 2, left to right
theorem tailIndex (l: List α) (hl: l.length > 0) :
  ∀ i,∀ (hi: i + 1 < l.length), l.tail[i]'(by
    simp only [List.length_tail]; omega
  ) = l[i + 1] := by
    induction l
    case nil => simp only [List.length_nil, gt_iff_lt, lt_self_iff_false] at hl
    case cons x xs _ =>
      simp only [List.length_cons, add_lt_add_iff_right, List.tail, List.getElem_cons_succ,
        implies_true]

--An Auxillary theorem for left to right
theorem zipOfIndexEq (lsLength : ℕ) (lss: List (List ℕ))
      (hlb: ∀ x ∈ lss, ∀ y ∈ x, y < b) (hlss: lss.length = 2)
      (hls: ∀ ls ∈ lss, ls.length = lsLength) (hIndexEq: ∀i, ∀ (hi : i < lsLength), lss[0][i]'(by
        have: lss[0] ∈ lss := by
          apply List.getElem_mem
        rw[hls lss[0] this]
        exact hi
      ) = lss[1][i]'(by
        have: lss[1] ∈ lss := by
          apply List.getElem_mem
        rw[hls lss[1] this]
        exact hi
      )): ∀ f ∈ (zipToAlphabetFin lsLength 2 lss hlb hlss hls), (f 0).val = f 1:= by
      intro f hf
      induction lsLength generalizing lss
      case zero =>
        simp [List.length_eq_zero, zipToAlphabetFin] at hf
      case succ lsLength ih =>
        simp[zipToAlphabetFin] at hf
        rcases hf with hf | hf
        . specialize hIndexEq 0 (by norm_num)
          simp[hf, hIndexEq]
        . apply ih (List.map (fun ls ↦ ls.tail) lss)
          . intro i hi
            simp only [List.getElem_map]
            rw[tailIndex, tailIndex]
            apply hIndexEq
            simp only [add_lt_add_iff_right]
            exact hi
            . have : lss[1] ∈ lss := by apply List.getElem_mem lss 1
              specialize hls lss[1]
              rw[hls this]
              simp
            . have : lss[0] ∈ lss := by apply List.getElem_mem lss 0
              specialize hls lss[0]
              rw[hls this]
              simp
          . exact hf

theorem eqInput_if_equal (m n b : ℕ) (hb : b > 1) :
  m = n →  ∀ f ∈ inputToBase b hb [m, n], (f ⟨0, by simp⟩).val = f ⟨1, by simp⟩ := by
    intro h
    --rw[h] at *
    -- have digitsEq : toBase b m = toBase b n := by rw[h]
    -- have lenEq : (toBase b m).length = (toBase b n).length := by rw[digitsEq]
    -- have mapTo : mapToBase b [m, n] = [toBase b m, toBase b n] := by rfl
    have mapLen : (mapToBase b [m, n]).length = 2 :=
    mapToBase_length b [m, n]
    -- have lenEqMap : ((mapToBase b [m, n])[0]).length = ((mapToBase b [m, n])[1]).length := by
    --   simp only [mapTo, List.getElem_cons_zero, lenEq, List.getElem_cons_succ]
    -- have maxLenEq : maxLen (mapToBase b [m, n]) = (toBase b m).length := by
    --   simp only [maxLen, h, zero_le, max_eq_left, max_self]
    have stretchLenLen_aux : (stretchLen (mapToBase b [m, n])).length = (mapToBase b [m, n]).length :=
      stretchLen_length (mapToBase b [m, n])
    have stretchLenLen : (stretchLen (mapToBase b [m, n])).length = 2 := by
      simp only [stretchLenLen_aux, mapLen]
    have stretchLenEq: (stretchLen (mapToBase b [m, n]))[0] =
    (stretchLen (mapToBase b [m, n]))[1] := by
      simp only [stretchLen, List.map, List.getElem_cons_zero, List.getElem_cons_succ, h]

    have indexValid0 : 0 < (stretchLen (mapToBase b [m, n])).length := by
      simp [stretchLenLen]

    have indexValid1 : 1 < (stretchLen (mapToBase b [m, n])).length := by simp [stretchLenLen]

    have lenStretchLen0 : (stretchLen (mapToBase b [m, n]))[0].length = maxLen (mapToBase b [m, n]) := by
      apply stretchLen_uniform
      exact List.getElem_mem (stretchLen (mapToBase b [m, n])) 0 indexValid0

    have lenStretchLen1 : (stretchLen (mapToBase b [m, n]))[1].length = maxLen (mapToBase b [m, n]) := by
      apply stretchLen_uniform
      exact List.getElem_mem (stretchLen (mapToBase b [m, n])) 1 indexValid1

    have stretchLenIndexEq (i: ℕ)(hi: i < (maxLen (mapToBase b [m, n]))): (stretchLen (mapToBase b [m, n]))[0][i]'(by
      simp[lenStretchLen0]
      exact hi
    ) = (stretchLen (mapToBase b [m, n]))[1][i]'(by
      simp[lenStretchLen1]
      exact hi
    ) := by
      simp[stretchLenEq]
    intro f hf
    rw[inputToBase] at hf
    apply zipOfIndexEq (maxLen (mapToBase b [m, n])) (stretchLen (mapToBase b [m, n]))
    . apply stretchLenIndexEq
    . exact hf

      --WOW!!!!

--Right to left
theorem equal_if_eqInput (m n b : ℕ) (hb : b > 1) :
  (∀ f ∈ inputToBase b hb [m, n], (f ⟨0, by simp⟩).val = f ⟨1, by simp⟩) → m = n := by



  sorry

--statement of Step 2
theorem eqInput_iff_equal (m n b : ℕ) (hb : b > 1):
  (∀ f ∈ inputToBase b hb [m, n], (f ⟨0, by simp⟩).val = f ⟨1, by simp⟩) ↔ m = n := by
    constructor
    . apply equal_if_eqInput
    . apply eqInput_if_equal

--Final theorem for the correctness of eqBase b
theorem eqBase_iff_equal (m n b : ℕ) (hb: b > 1):
  m = n ↔ (eqBase b).eval (inputToBase b hb [m, n]) := by
  constructor
  . intro h
    apply (eqBase_iff_eqInput b (inputToBase b hb [m, n])).mpr
    apply (eqInput_iff_equal m n b hb).mpr h
  . intro h
    apply (eqInput_iff_equal m n b hb).mp
    apply (eqBase_iff_eqInput b (inputToBase b hb [m, n])).mp h

def leBase (k: ℕ)  : DFA (Fin 2 → Fin k) (Fin 2) := {
  transition := fun f s => match s with
    | 0 => if (f 0).val <= (f 1).val then 0 else 1
    | 1 => 1
  start := 0
  output := fun x => x == 0
}

def addBase (k: ℕ) : DFA (Fin 3 → Fin k) (Fin 3) := {
  transition := fun f s => match s with
    | 0 => if (f 0).val + f 1 == f 2 then 0 else
      if (f 0).val + f 1 + 1 == f 2 then 1
      else 2
    | 1 => if (f 0).val + f 1 + 1 == f 2 + k then 1 else
      if (f 0).val + f 1 == f 2 + k then 0
      else 2
    | 2 => 2
  start := 0
  output := fun x => x == 0
}
