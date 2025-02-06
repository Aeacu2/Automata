import Mathlib.Tactic
import Mathlib.Data.List.Basic
import Automata.DFA
import Automata.NFA
import Automata.Input
import Automata.Boolean
import Automata.Replicate
import Automata.LeadingZeros
import Mathlib.Data.Nat.Digits

-- The equality checking automata for two numbers in a long list of inputs.
def eqBase (k n: ℕ) (a b : Fin n): DFA (Fin n → Fin k) (Fin 2) := {
  transition := fun f s => match s with
    | 0 => if (f a).val == f b then 0 else 1
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
theorem eqBase_if_equal_aux (input: List (Fin n → Fin k)):
  (∀ f ∈ input, (f a).val = f b) → (eqBase k n a b).evalFrom input 0 := by
  intro h
  induction input
  case nil =>
    simp[eqBase, DFAO.evalFrom, DFAO.transFrom]
  case cons f fs ih =>
    have h1 := h f
    simp only [List.mem_cons, true_or, Fin.isValue, true_implies] at h1
    simp only [DFAO.evalFrom, DFAO.transFrom, Fin.isValue]
    have: ((eqBase k n a b).transition f 0) = 0 := by
      simp only [eqBase, Fin.isValue, beq_iff_eq, h1, ↓reduceIte]
    rw[this]
    apply ih
    intro f' hf'
    apply h
    simp only [List.mem_cons, or_true, hf']


-- Left to right, much harder
theorem eqBase_trans_zero (state : Fin 2) (f : Fin n → Fin k) :
  (eqBase k n a b).transition f state = 0 ↔ state = 0 ∧ (f a).val = f b := by
  simp only [eqBase, Fin.isValue, beq_iff_eq]
  split <;> simp


theorem eqBase_transFrom_zero (state: Fin 2) (l : List (Fin n → Fin k)) :
  (eqBase k n a b).transFrom l state = 0 ↔ state = 0 ∧ ∀ f ∈ l, (f a).val = f b := by
  induction l generalizing state
  case nil =>
    simp[eqBase, DFAO.transFrom]
  case cons f fs ih =>
    simp[DFAO.transFrom]
    specialize ih ((eqBase k n a b).transition f state)
    constructor
    . intro h
      have:= ih.mp h
      rcases this with ⟨h1, h2⟩
      have:= (eqBase_trans_zero state f).mp h1
      rcases this with ⟨h3, h4⟩
      exact ⟨h3, ⟨h4, h2⟩⟩
    . intro h
      rcases h with ⟨h1, h2, h3⟩
      apply ih.mpr
      constructor
      . apply (eqBase_trans_zero state f).mpr
        exact ⟨h1, h2⟩
      . exact h3

theorem eqInput_if_eqBase_aux (input: List (Fin n → Fin k)):
  (eqBase k n a b).transFrom input 0 = 0 → (∀ f ∈ input, (f a).val = f b) := by
  intro h
  exact (eqBase_transFrom_zero 0 input).mp h |>.2

theorem eqInput_if_eqBase (input: List (Fin n → Fin k)):
  (eqBase k n a b).evalFrom input 0 → (∀ f ∈ input, (f a).val = f b) := by
  intro h
  have:= eqInput_if_eqBase_aux (b := b) (a := a) input
  apply this
  -- simp[DFAO.evalFrom, eqBase] at h
  simp_all only [DFAO.evalFrom, eqBase, beq_iff_eq, true_implies]

-- End of Left to right, final step 1 statement:
theorem eqBase_iff_eqInput (k : ℕ) (input: List (Fin n → Fin k)):
  (eqBase k n a b).eval input ↔ (∀ f ∈ input, (f a).val = f b) := by
  constructor
  . apply eqInput_if_eqBase input
  . apply eqBase_if_equal_aux input


--An Auxillary theorem for left to right
theorem eqZipOfIndexEq (lsLength : ℕ) (lss: List (List ℕ))
      (hlb: ∀ x ∈ lss, ∀ y ∈ x, y < b) (hlss: lss.length = l) (m n : Fin l)
      (hls: ∀ ls ∈ lss, ls.length = lsLength) (hIndexEq: ∀i, ∀ (hi : i < lsLength), lss[m][i]'(by
        have: lss[m] ∈ lss := by
          apply List.getElem_mem
        rw[hls lss[m] this]
        exact hi
      ) = lss[n][i]'(by
        have: lss[n] ∈ lss := by
          apply List.getElem_mem
        rw[hls lss[n] this]
        exact hi
      )): ∀ f ∈ (zipToAlphabetFin lsLength l lss hlb hlss hls), (f m).val = f n:= by
      intro f hf
      induction lsLength generalizing lss
      case zero =>
        simp only [zipToAlphabetFin, List.not_mem_nil] at hf
      case succ lsLength ih =>
        simp only [zipToAlphabetFin, Fin.getElem_fin, List.mem_cons] at hf
        rcases hf with hf | hf
        . specialize hIndexEq 0 (by norm_num)
          simp[hf, hIndexEq]
          exact hIndexEq
        . apply ih (List.map (fun ls ↦ ls.tail) lss)
          . intro i hi
            simp only [Fin.getElem_fin, List.getElem_map]
            rw[List.getElem_tail, List.getElem_tail]
            apply hIndexEq
            simp only [add_lt_add_iff_right]
            exact hi
          . exact hf

theorem eqInput_if_equal (input : List ℕ) (hl: input.length = l) (m n : Fin l) :
  input[m] = input[n] →  ∀ f ∈ inputToBase (b + 2) (by omega) input hl, (f m).val = (f n) := by
    intro h
    have stretchLenLen_aux : (stretchLen (mapToBase (b+2) input)).length = (mapToBase (b+2) input).length :=
      stretchLen_length (mapToBase (b+2) input)

    have stretchLenLen : (stretchLen (mapToBase (b+2) input)).length = input.length := by
      simp only [stretchLenLen_aux, mapToBase_length]

    have stretchLenEq: (stretchLen (mapToBase (b+2) input))[m] =
    (stretchLen (mapToBase (b+2) input))[n] := by
      simp_all[stretchLen, mapToBase, h]

    have indexValid0 : m < (stretchLen (mapToBase (b+2) input)).length := by
      simp [stretchLenLen]
      omega

    have indexValid1 : n < (stretchLen (mapToBase (b+2) input)).length := by
      simp [stretchLenLen]
      omega

    have lenStretchLen0 : (stretchLen (mapToBase (b+2) input))[m].length = maxLen (mapToBase (b+2) input) := by
      apply stretchLen_uniform
      exact List.getElem_mem (stretchLen (mapToBase (b+2) input)) m indexValid0

    have lenStretchLen1 : (stretchLen (mapToBase (b+2) input))[n].length = maxLen (mapToBase (b+2) input) := by
      apply stretchLen_uniform
      exact List.getElem_mem (stretchLen (mapToBase (b+2) input)) n indexValid1

    have stretchLenIndexEq (i: ℕ)(hi: i < (maxLen (mapToBase (b+2) input))): (stretchLen (mapToBase (b+2) input))[m][i] = (stretchLen (mapToBase (b+2) input))[n][i] := by
      simp only [stretchLenEq]

    intro f hf
    rw[inputToBase] at hf
    apply eqZipOfIndexEq (maxLen (mapToBase (b+2) input)) (stretchLen (mapToBase (b+2) input))
    . apply stretchLenIndexEq
    . exact hf

--Right to left
theorem equal_if_toBaseEq: toBase b m = toBase b n → m = n := by
  intro h
  rw[← ofBase_toBase b n, ← ofBase_toBase b m]
  congr

theorem equal_if_mapToBaseEq (input: List ℕ) (hl: input.length = l) (m n : Fin l) :
  (mapToBase (b+2) input)[m]'(by simp[mapToBase, hl]) = (mapToBase (b+2) input)[n]'(by simp[mapToBase, hl]) → input[m] = input[n] := by
  intro h
  simp only [mapToBase, List.map_cons, List.map_nil, List.getElem_cons_zero,
    List.getElem_cons_succ] at h

  apply equal_if_toBaseEq
  simp_all only [Fin.getElem_fin, List.getElem_map]
  exact h

theorem eq_if_addZeroesEq_nonzero (n: ℕ) (L: List (List ℕ)) (k l: Fin L.length) (hn: n ≥ maxLen L)  (lenk :0 < L[k].length) (hk: L[k][0] ≠ 0) (lenl :0 < L[l].length) (hl: L[l][0] ≠ 0) :
  addZeroes (n - L[k].length) L[k] = addZeroes (n - L[l].length) L[l] → L[k] = L[l] := by
  intro h
  simp only [maxLen, zero_le, max_eq_left, ge_iff_le, max_le_iff] at hn
  have kLen: L[k].length ≤ n := by
    trans maxLen L
    apply len_le_maxLen
    apply List.getElem_mem
    exact hn
  have lLen: L[l].length ≤ n := by
    trans maxLen L
    apply len_le_maxLen
    apply List.getElem_mem
    exact hn

  have hL: n - L[k].length = n - L[l].length := by
    by_contra hL
    have hLen: n - L[k].length < n - L[l].length ∨ n - L[k].length > n - L[l].length := by
      exact Nat.lt_or_gt_of_ne hL
    have kAddLen: (addZeroes (n - L[k].length) L[k]).length = n := by simp only [addZeroesLength]; omega
    have lAddLen: (addZeroes (n - L[l].length) L[l]).length = n :=  by simp only [addZeroesLength]; omega
    rcases hLen with (hLen | hLen)
    .
      have addl : (addZeroes (n - L[l].length) L[l])[n-L[k].length] = 0 := by
        simp[addZeroes]
        apply List.getElem_of_replicate_append_left
        exact hLen

      have addk : (addZeroes (n - L[k].length) L[k])[n - L[k].length] ≠  0 := by
        simp[addZeroes]
        rw[List.getElem_append_right]
        simp only [List.length_replicate, le_refl, tsub_eq_zero_of_le]
        exact hk
        . simp[*]
        . simp_all only [Fin.getElem_fin, ne_eq, List.length_replicate, le_refl, tsub_eq_zero_of_le]
          exact lenk
      simp_all only [ne_eq, ge_iff_le, not_true_eq_false]

    .
      have addk : (addZeroes (n - L[k].length) L[k])[n-L[l].length] = 0 := by
        simp[addZeroes]
        apply List.getElem_of_replicate_append_left
        exact hLen
      have addl : (addZeroes (n - L[l].length) L[l])[n-L[l].length] ≠  0 := by
        simp only [addZeroes, ne_eq]
        rw[List.getElem_append_right]
        simp only [List.length_replicate, le_refl, tsub_eq_zero_of_le]
        exact hl
        . simp only [List.length_replicate, lt_self_iff_false, not_false_eq_true]
        . simp only [List.length_replicate, le_refl, tsub_eq_zero_of_le, lenl]

      simp_all only [ge_iff_le, ne_eq]
  rw[← hL] at h
  simp only [addZeroes, List.append_cancel_left_eq] at h
  exact h

theorem contra (input : List ℕ) (hl: input.length = l) (m n : Fin l) (h : (stretchLen (mapToBase (b+2) input))[m]'(by simp[stretchLen_length, mapToBase_length, hl]) = (stretchLen (mapToBase (b+2) input))[n]'(by simp[stretchLen_length, mapToBase_length, hl])) (hn: input[n.val] = 0) (hm : input[m.val] ≠ 0) : False := by
  simp[stretchLen, mapToBase, toBase, hn] at h
  have : ∀ x ∈ addZeroes (maxLen (List.map (toBase (b + 2)) input)) [], x = 0 ∨ x ∈ [] := by
    apply addZeroes_elem
  simp only [List.not_mem_nil, or_false] at this
  rw[← h] at this
  have hbm: ∀x ∈ (toBase (b+2) input[m]), x = 0 := by
    intro x hx
    apply this
    simp only [addZeroes, le_add_iff_nonneg_left, zero_le, List.mem_append, List.mem_replicate,
      ne_eq, List.mem_reverse]
    right
    exact List.mem_reverse.mp hx
  have: input[m] > 0 := by exact Nat.zero_lt_of_ne_zero hm
  have hPos := toBase_lead_nonzero (b+2) input[m] (by omega) this
  specialize hbm ((toBase (b+2) input[m])[0]'(by
      apply toBase_len_nonzero <;> omega
  ))
  have hyp : (toBase (b+2) input[m])[0]'(by
  have:= toBase_len_nonzero (b+2) input[m] (by omega) (by omega)
  omega) ∈ toBase (b+2) input[m] := by apply List.getElem_mem
  specialize hbm hyp
  rw[hbm] at hPos
  contradiction

theorem eq_if_stretchLenEq (input : List ℕ) (hl : input.length = l) (m n : Fin l) :
  (stretchLen (mapToBase (b+2) input))[m]'(by simp[stretchLen_length, mapToBase_length, hl]) = (stretchLen (mapToBase (b+2) input))[n]'(by simp[stretchLen_length, mapToBase_length, hl]) → input[m] = input[n] := by
  intro h
  apply equal_if_mapToBaseEq
  by_cases hm: input[m.val] = 0
  . by_cases hn : input[n.val] = 0
    . simp[mapToBase, hn, hm]
    . by_contra; apply contra; exact h.symm; exact hm; exact hn; exact hl
  by_cases hn: input[n.val] = 0
  . by_contra; apply contra; exact h; exact hn; exact hm; exact hl
  apply eq_if_addZeroesEq_nonzero (maxLen (mapToBase (b+2) input)) (mapToBase (b+2) input) ⟨m, by simp[mapToBase, hl]⟩ ⟨n, by simp[mapToBase_length, hl]⟩
  . simp only [ge_iff_le]; rfl
  . simp only [mapToBase, List.map_cons, List.map_nil, List.getElem_cons_zero, ne_eq]
    refine Nat.ne_zero_iff_zero_lt.mpr ?_
    simp only [Fin.getElem_fin, List.getElem_map]
    apply toBase_lead_nonzero
    simp_all only [Fin.getElem_fin, ge_iff_le, le_add_iff_nonneg_left, zero_le]
    . omega
  . simp only [mapToBase, List.map_cons, List.map_nil, List.getElem_cons_zero, ne_eq]
    refine Nat.ne_zero_iff_zero_lt.mpr ?_
    simp only [Fin.getElem_fin, List.getElem_map]
    apply toBase_lead_nonzero
    simp_all only [Fin.getElem_fin, ge_iff_le, le_add_iff_nonneg_left, zero_le]
    . omega
  . simp_all[stretchLen]
  . simp only [mapToBase, Fin.getElem_fin, List.getElem_map]
    apply toBase_len_nonzero <;> omega
  . simp only [mapToBase, Fin.getElem_fin, List.getElem_map]
    apply toBase_len_nonzero <;> omega
  . exact hl




theorem indexEqOfEqZip (m n : Fin l) (b lsLength : ℕ) (lss: List (List ℕ))
      (hlb: ∀ x ∈ lss, ∀ y ∈ x, y < b) (hlss: lss.length = l)
      (hls: ∀ ls ∈ lss, ls.length = lsLength) :
      (∀ f ∈ (zipToAlphabetFin lsLength l lss hlb hlss hls), (f m).val = f n)
      → ∀i, ∀ hi : i < lsLength, lss[m][i]'(by
        have: lss[m] ∈ lss := by
          apply List.getElem_mem
        rw[hls lss[m] this]
        exact hi
      ) = lss[n][i]'(by
        have: lss[n] ∈ lss := by
          apply List.getElem_mem
        rw[hls lss[n] this]
        exact hi
      ) := by
        intro h
        induction lsLength generalizing lss
        case zero => intro i hi; contradiction
        case succ s ih =>
          intro i hi
          simp only [zipToAlphabetFin, Fin.getElem_fin, List.mem_cons, Fin.isValue,
            forall_eq_or_imp, Fin.val_zero, Fin.val_one] at h
          rcases h with ⟨h1, h2⟩
          specialize ih (List.map (fun ls ↦ ls.tail) lss)
          specialize ih (zipTailHlb lss hlb)
          specialize ih (zipTailHlss l lss hlss)
          specialize ih (zipTailHls lss hls)
          specialize ih h2
          simp at ih
          have lss0 : lss[m]'(by omega) ∈ lss := by apply List.getElem_mem lss m _
          have lss1 : lss[n] ∈ lss := by apply List.getElem_mem
          have i0Len : i < lss[m].length := by
            specialize hls lss[m]
            specialize hls lss0
            rwa [hls]
          have i1Len : i < lss[n].length := by
            specialize hls lss[n]
            specialize hls lss1
            rwa [hls]
          match i with
          | 0 => exact h1
          | n + 1 =>
            simp only [add_lt_add_iff_right] at hi
            specialize ih n hi
            -- rw[← tailIndex lss[0] n i0Len]
            -- rw[← tailIndex lss[1] n i1Len]
            simp only [List.getElem_tail, *] at ih
            exact ih

theorem equal_if_eqInput (hl :input.length = l) (m n : Fin l) :
  (∀ f ∈ inputToBase (b+2) (by omega) input hl , (f m).val = f n) → input[m] = input[n] := by
    intro h
    simp only [List.length_cons, List.length_singleton, Nat.reduceAdd, inputToBase, Fin.zero_eta,
      Fin.isValue, Fin.mk_one] at h
    apply eq_if_stretchLenEq (b := b) input hl m n
    .
      have inter := indexEqOfEqZip m n (b+2) (maxLen (mapToBase (b+2) input))  (stretchLen (mapToBase (b+2) input)) (stretchLen_of_mapToBase_lt_base (b+2) input (by omega)) (by simp[stretchLen_length, mapToBase_length, hl])  (fun ls hls ↦ stretchLen_uniform (mapToBase (b+2) input) ls hls)
      specialize inter h

      have:= stretchLen_uniform (mapToBase (b+2) input)
      have len0 : ((stretchLen (mapToBase (b+2) input))[m]'(by simp[stretchLen_length, mapToBase_length, hl])).length = maxLen (mapToBase (b+2) input) := by
        specialize this  ((stretchLen (mapToBase (b+2) input))[m]'(by simp[stretchLen_length, mapToBase_length, hl]))
        have mem0: ((stretchLen (mapToBase (b+2) input))[m]'(by simp[stretchLen_length, mapToBase_length, hl])) ∈ stretchLen (mapToBase (b+2) input) := by apply List.getElem_mem
        exact this mem0
      have len1 : ((stretchLen (mapToBase (b+2) input))[n]'(by simp[stretchLen_length, mapToBase_length, hl])).length = maxLen (mapToBase (b+2) input) := by
        specialize this  ((stretchLen (mapToBase (b+2) input))[n]'(by simp[stretchLen_length, mapToBase_length, hl]))
        have mem1: ((stretchLen (mapToBase (b+2) input))[n]'(by simp[stretchLen_length, mapToBase_length, hl])) ∈ stretchLen (mapToBase (b+2) input) := by apply List.getElem_mem
        exact this mem1
      apply List.ext_getElem
      . subst hl
        simp_all only [Fin.getElem_fin]
      .
        intro _ _ _
        apply inter
        simp_all only [Fin.getElem_fin]

-- Step 2 Complete
theorem eqInput_iff_equal (hl :input.length = l) (m n : Fin l) :
  (∀ f ∈ (inputToBase (b+2) (by omega) input (hl)), (f m).val = f n) ↔ input[m] = input[n] := by
    constructor
    . apply equal_if_eqInput
    . apply eqInput_if_equal

-- Final theorem v1
theorem eqBase_iff_equal_false (b : ℕ) (hb: b > 1) (input : List ℕ) (hl : input.length = l) (m n : Fin l):
  input[m] = input[n] ↔ (eqBase b l m n).eval (inputToBase b (hb) input hl) := by
  constructor
  . intro h
    apply eqBase_iff_eqInput b (inputToBase b hb input hl) |>.mpr
    cases b; contradiction;
    rename_i b
    cases b; contradiction;
    rename_i b
    apply eqInput_iff_equal (b := b) hl m n |>.mpr
    exact h
  . intro h
    cases b; contradiction;
    rename_i b
    cases b; contradiction;
    rename_i b
    apply eqInput_iff_equal (b := b) hl m n |>.mp
    apply eqBase_iff_eqInput (a := m) (b := n) (b+2) (inputToBase (b+2) (hb) input hl) |>.mp
    exact h

-- Final theorem v2
theorem eqBase_iff_equal (b : ℕ) (hb: b > 1) (input : List ℕ) (l : ℕ) (hl : input.length = l) (m n : Fin l):
  input[m] = input[n] ↔ (eqBase b l m n).eval (inputToBase b (hb) input hl) := by
  constructor
  . intro h
    apply eqBase_iff_eqInput b (inputToBase b hb input hl) |>.mpr
    cases b; contradiction;
    rename_i b
    cases b; contradiction;
    rename_i b
    apply eqInput_iff_equal (b := b) hl m n |>.mpr
    exact h
  . intro h
    cases b; contradiction;
    rename_i b
    cases b; contradiction;
    rename_i b
    apply eqInput_iff_equal (b := b) hl m n |>.mp
    apply eqBase_iff_eqInput (a := m) (b := n) (b+2) (inputToBase (b+2) (hb) input hl) |>.mp
    exact h

-- Final theorem v3
theorem eqBase_iff_equal_nat (b : ℕ) (hb: b > 1) (input : List ℕ) (l : ℕ)
(hl : input.length = l) (m n : ℕ) (hm: m < l) (hn: n < l):
  input[m] = input[n] ↔ (eqBase b l ⟨m, hm⟩ ⟨n, hn⟩).eval (inputToBase b (hb) input hl) := by
  constructor
  . intro h
    apply eqBase_iff_eqInput b (inputToBase b hb input hl) |>.mpr
    cases b; contradiction;
    rename_i b
    cases b; contradiction;
    rename_i b
    apply eqInput_iff_equal (b := b) hl ⟨m, hm⟩ ⟨n, hn⟩ |>.mpr
    exact h
  . intro h
    cases b; contradiction;
    rename_i b
    cases b; contradiction;
    rename_i b
    apply eqInput_iff_equal (b := b) hl ⟨m, hm⟩ ⟨n, hn⟩ |>.mp
    apply eqBase_iff_eqInput (a := ⟨m, hm⟩) (b := ⟨n, hn⟩) (b+2) (inputToBase (b+2) (hb) input hl) |>.mp
    exact h

theorem equality_respectZero : (eqBase (b + 2) l m n).respectZero := by
  rw[DFA.respectZero]
  intro x c
  constructor
  intro h
  rw[padZeros]
  rw[DFAO.eval, DFAO.evalFrom, DFAO.transFrom_of_append]
  nth_rw 1 [eqBase]
  simp only [Fin.isValue, beq_iff_eq]
  suffices: (DFAO.transFrom (eqBase (b + 2) l m n) (List.replicate c fun _ ↦ 0) (eqBase (b + 2) l m n).start) = 0
  . rw[this]
    simp[DFAO.eval, DFAO.evalFrom] at h
    nth_rw 1 3 [eqBase] at h
    simp only [Fin.isValue, beq_iff_eq] at h
    exact h
  nth_rw 2 [eqBase]
  simp only [Fin.isValue]
  apply eqBase_transFrom_zero 0 (List.replicate c fun _ ↦ 0) |>.mpr
  constructor
  . rfl
  . intro f a
    simp_all only [List.mem_replicate, ne_eq, Fin.val_zero]
  . intro h
    contrapose h; simp_all only [Bool.not_eq_true]
    rw[padZeros]
    rw[DFAO.eval, DFAO.evalFrom, DFAO.transFrom_of_append]
    nth_rw 1 [eqBase]
    simp only [Fin.isValue, beq_iff_eq]
    suffices: (DFAO.transFrom (eqBase (b + 2) l m n) (List.replicate c fun _ ↦ 0) (eqBase (b + 2) l m n).start) = 0
    . rw[this]
      simp[DFAO.eval, DFAO.evalFrom] at h
      nth_rw 1 3 [eqBase] at h
      simp only [Fin.isValue, beq_iff_eq] at h
      exact h
    nth_rw 2 [eqBase]
    simp only [Fin.isValue]
    apply eqBase_transFrom_zero 0 (List.replicate c fun _ ↦ 0) |>.mpr
    simp_all only [Fin.isValue, List.mem_replicate, ne_eq, Fin.val_zero, and_imp, implies_true, and_self]



-- Demos
--Failed!!!
-- theorem zero_is_zero_fail : 0 = 0 := by
--   apply (eqBase_iff_equal_false 2 (by norm_num) [0, 0] (by norm_num) 0 1).mpr
