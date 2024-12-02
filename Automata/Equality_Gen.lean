import Mathlib.Tactic
import Mathlib.Data.List.Basic
import Automata.DFA
import Automata.NFA
import Automata.Input
import Automata.Boolean
import Automata.Vector
import Automata.Replicate
import Mathlib.Data.Nat.Digits

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

theorem equal_if_mapToBaseEq (input: List ℕ) (m n : Fin input.length) :
  (mapToBase (b+2) input)[m]'(by simp[mapToBase]) = (mapToBase (b+2) input)[n]'(by simp[mapToBase]) → input[m] = input[n] := by
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

theorem contra (input : List ℕ) (m n : Fin input.length) (h : (stretchLen (mapToBase (b+2) input))[m]'(by simp[stretchLen_length, mapToBase_length]) = (stretchLen (mapToBase (b+2) input))[n]'(by simp[stretchLen_length, mapToBase_length])) (hn: input[n.val] = 0) (hm : input[m.val] ≠ 0) : False := by
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

theorem eq_if_stretchLenEq (input : List ℕ) (m n : Fin input.length) :
  (stretchLen (mapToBase (b+2) input))[m]'(by simp[stretchLen_length, mapToBase_length]) = (stretchLen (mapToBase (b+2) input))[n]'(by simp[stretchLen_length, mapToBase_length]) → input[m] = input[n] := by
  intro h
  apply equal_if_mapToBaseEq
  by_cases hm: input[m.val] = 0
  . by_cases hn : input[n.val] = 0
    . simp[mapToBase, hn, hm]
    . by_contra; apply contra; exact h.symm; exact hm; exact hn
  by_cases hn: input[n.val] = 0
  . by_contra; apply contra; exact h; exact hn; exact hm
  apply eq_if_addZeroesEq_nonzero (maxLen (mapToBase (b+2) input)) (mapToBase (b+2) input) ⟨m, by simp[mapToBase]⟩ ⟨n, by simp[mapToBase_length]⟩
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




theorem indexEqOfEqZip (b lsLength : ℕ) (lss: List (List ℕ))
      (hlb: ∀ x ∈ lss, ∀ y ∈ x, y < b) (hlss: lss.length = 2)
      (hls: ∀ ls ∈ lss, ls.length = lsLength) :
      (∀ f ∈ (zipToAlphabetFin lsLength 2 lss hlb hlss hls), (f 0).val = f 1)
      → ∀i, ∀ hi : i < lsLength, lss[0][i]'(by
        have: lss[0] ∈ lss := by
          apply List.getElem_mem
        rw[hls lss[0] this]
        exact hi
      ) = lss[1][i]'(by
        have: lss[1] ∈ lss := by
          apply List.getElem_mem
        rw[hls lss[1] this]
        exact hi
      ) := by
        intro h
        induction lsLength generalizing lss
        case zero => intro i hi; contradiction
        case succ m ih =>
          intro i hi
          simp only [zipToAlphabetFin, Fin.getElem_fin, List.mem_cons, Fin.isValue,
            forall_eq_or_imp, Fin.val_zero, Fin.val_one] at h
          rcases h with ⟨h1, h2⟩
          specialize ih (List.map (fun ls ↦ ls.tail) lss)
          specialize ih (zipTailHlb lss hlb)
          specialize ih (zipTailHlss 2 lss hlss)
          specialize ih (zipTailHls lss hls)
          specialize ih h2
          simp at ih
          have lss0 : lss[0] ∈ lss := by apply List.getElem_mem lss 0 _
          have lss1 : lss[1] ∈ lss := by apply List.getElem_mem
          have i0Len : i < lss[0].length := by
            specialize hls lss[0]
            specialize hls lss0
            rwa [hls]
          have i1Len : i < lss[1].length := by
            specialize hls lss[1]
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

-- theorem equal_if_eqInput
