import Mathlib.Tactic
import Mathlib.Data.List.Basic
import Automata.DFA
import Automata.NFA
import Automata.Input
import Mathlib.Data.Nat.Digits

-- The standard equality checking automata

def eqBase (k: ℕ) : DFA (Fin 2 → Fin k) (Fin 2) := {
  transition := fun f s => match s with
    | 0 => if (f 0).val = f 1 then 0 else 1
    | 1 => 1
  start := 0
  output := fun x => x == 0
}


-- The equality checking automata for two numbers in a long list of inputs.
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
#check List.getElem_tail
-- theorem tailIndex (l: List α) :
--   ∀ i,∀ (hi: i + 1 < l.length), l.tail[i]'(by
--     simp only [List.length_tail]; omega
--   ) = l[i + 1] := by
--     -- intro i hi
--     -- have hl: 0 < l.length := by
--     --   apply lt_trans
--     --   swap
--     --   . exact hi
--     --   . simp
--     induction l
--     case nil =>
--       simp
--     case cons x xs _ =>
--       simp only [List.length_cons, add_lt_add_iff_right, List.tail, List.getElem_cons_succ,
--         implies_true]

--An Auxillary theorem for left to right
theorem eqZipOfIndexEq (lsLength : ℕ) (lss: List (List ℕ))
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
        simp only [zipToAlphabetFin, List.not_mem_nil] at hf
      case succ lsLength ih =>
        simp only [zipToAlphabetFin, Fin.getElem_fin, List.mem_cons] at hf
        rcases hf with hf | hf
        . specialize hIndexEq 0 (by norm_num)
          simp[hf, hIndexEq]
        . apply ih (List.map (fun ls ↦ ls.tail) lss)
          . intro i hi
            simp only [List.getElem_map]
            rw[List.getElem_tail, List.getElem_tail]
            apply hIndexEq
            simp only [add_lt_add_iff_right]
            exact hi
            -- . have : lss[1] ∈ lss := by apply List.getElem_mem lss 1
            --   specialize hls lss[1]
            --   rw[hls this]
            --   simp
            -- . have : lss[0] ∈ lss := by apply List.getElem_mem lss 0
            --   specialize hls lss[0]
            --   rw[hls this]
            --   simp
          . exact hf

theorem mapLen : (mapToBase b [m, n]).length = 2 :=
    mapToBase_length b [m, n]

theorem eqInput_if_equal (m n b : ℕ) (hb : b ≥ 2) :
  m = n →  ∀ f ∈ inputToBase b hb [m, n], (f ⟨0, by simp⟩).val = f ⟨1, by simp⟩ := by
    intro h
    --rw[h] at *
    -- have digitsEq : toBase b m = toBase b n := by rw[h]
    -- have lenEq : (toBase b m).length = (toBase b n).length := by rw[digitsEq]
    -- have mapTo : mapToBase b [m, n] = [toBase b m, toBase b n] := by rfl
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

    have indexValid1 : 1 < (stretchLen (mapToBase b [m, n])).length := by
      simp [stretchLenLen]

    have lenStretchLen0 : (stretchLen (mapToBase b [m, n]))[0].length = maxLen (mapToBase b [m, n]) := by
      apply stretchLen_uniform
      exact List.getElem_mem (stretchLen (mapToBase b [m, n])) 0 indexValid0

    have lenStretchLen1 : (stretchLen (mapToBase b [m, n]))[1].length = maxLen (mapToBase b [m, n]) := by
      apply stretchLen_uniform
      exact List.getElem_mem (stretchLen (mapToBase b [m, n])) 1 indexValid1

    have stretchLenIndexEq (i: ℕ)(hi: i < (maxLen (mapToBase b [m, n]))): (stretchLen (mapToBase b [m, n]))[0][i]'(by
      simp only [lenStretchLen0]
      exact hi
    ) = (stretchLen (mapToBase b [m, n]))[1][i]'(by
      simp[lenStretchLen1]
      exact hi
    ) := by
      simp[stretchLenEq]

    intro f hf
    rw[inputToBase] at hf
    apply eqZipOfIndexEq (maxLen (mapToBase b [m, n])) (stretchLen (mapToBase b [m, n]))
    . apply stretchLenIndexEq
    . exact hf

--Right to left
theorem equal_if_toBaseEq (m n b : ℕ):
  toBase b m = toBase b n → m = n := by
  intro h
  rw[← ofBase_toBase b n, ← ofBase_toBase b m]
  congr

theorem equal_if_mapToBaseEq (m n b : ℕ):
  (mapToBase b [m, n])[0]'(by simp[mapLen]) = (mapToBase b [m, n])[1]'(by simp[mapLen]) → m = n := by
  intro h
  simp only [mapToBase, List.map_cons, List.map_nil, List.getElem_cons_zero,
    List.getElem_cons_succ] at h
  apply equal_if_toBaseEq
  exact h

section

variable (l : List ℕ) (h : 5 < l.length)

set_option pp.notation false in
#check l[5]

end


theorem eq_if_addLeadingZerosEq_nonzero (n: ℕ) (k l: List ℕ) (hn: n ≥ maxLen [k, l])  (lenk :0 < k.length) (hk: k[0] ≠ 0) (lenl :0 < l.length) (hl: l[0] ≠ 0) :
  addLeadingZeros (n - k.length) k = addLeadingZeros (n - l.length) l → k = l := by
  intro h
  simp only [maxLen, zero_le, max_eq_left, ge_iff_le, max_le_iff] at hn
  have kLen: n ≥ k.length := hn.1
  have lLen: n ≥ l.length := hn.2

  have hL: n - k.length = n - l.length := by
    by_contra hL
    have hLen: n - k.length < n - l.length ∨ n - k.length > n - l.length := by
      exact Nat.lt_or_gt_of_ne hL
    have kAddLen: (addLeadingZeros (n - k.length) k).length = n := by simp only [addLeadingZerosLength]; omega
    have lAddLen: (addLeadingZeros (n - l.length) l).length = n :=  by simp only [addLeadingZerosLength]; omega
    rcases hLen with (hLen | hLen)
    . have addl : (addLeadingZeros (n - l.length) l)[n-k.length] = 0 := by

        have: (addLeadingZeros (n - l.length) l)[n-k.length] = (List.replicate (n - l.length) 0)[n - k.length]'(by simp[*]) := by
          simp only [addLeadingZeros]
          rw[List.getElem_append_left]

        rw[this]

        have: (List.replicate (n - l.length) 0)[n - k.length]'(by  simp[*]) = 0 := by
          simp[*]

        exact this

      have addk : (addLeadingZeros (n - k.length) k)[n-k.length] ≠  0 := by
        simp[addLeadingZeros]
        rw[List.getElem_append_right]
        simp only [List.length_replicate, le_refl, tsub_eq_zero_of_le]
        exact hk
        . simp[*]
        . simp[*]
      simp_all

    . have addk : (addLeadingZeros (n - k.length) k)[n-l.length] = 0 := by
        have: (addLeadingZeros (n - k.length) k)[n-l.length] = (List.replicate (n - k.length) 0)[n - l.length]'(by simp[*]) := by
          simp only [addLeadingZeros]
          rw[List.getElem_append_left]

        rw[this]

        have: (List.replicate (n - k.length) 0)[n - l.length]'(by  simp[*]) = 0 := by
          simp[*]

        exact this

      have addl : (addLeadingZeros (n - l.length) l)[n-l.length] ≠  0 := by
        simp[addLeadingZeros]
        rw[List.getElem_append_right]
        simp only [List.length_replicate, le_refl, tsub_eq_zero_of_le]
        exact hl
        . simp only [List.length_replicate, lt_self_iff_false, not_false_eq_true]
        . simp only [List.length_replicate, le_refl, tsub_eq_zero_of_le, lenl]

      simp_all only [ge_iff_le, ne_eq]
  rw[← hL] at h
  simp only [addLeadingZeros, List.append_cancel_left_eq] at h
  exact h


theorem eq_if_stretchLenEq (m n b: ℕ) (hb: b ≥ 2) :
  (stretchLen (mapToBase b [m, n]))[0]'(by simp[stretchLen_length, mapToBase_length]) = (stretchLen (mapToBase b [m, n]))[1]'(by simp[stretchLen_length, mapToBase_length]) → m = n := by
  intro h
  apply equal_if_mapToBaseEq
  by_cases hm: m = 0
  . simp only [stretchLen, addLeadingZeros, maxLen, toBase, hm, Nat.digits_zero, List.reverse_nil,
    List.length_nil, List.length_reverse, zero_le, max_eq_left, max_eq_right, mapToBase,
    List.map_cons, List.map_nil, tsub_zero, List.append_nil, le_refl, tsub_eq_zero_of_le,
    List.replicate_zero, List.nil_append, List.getElem_cons_zero, List.getElem_cons_succ] at h
    have : ∀x ∈ (b.digits n).reverse, x = 0 := by
      intro x hx
      rw[← h] at hx
      simp at hx
      exact hx.2
    have hbn:  ∀x ∈ (b.digits n), x = 0 := by aesop
    by_cases hn : n = 0
    . simp only [mapToBase, hm, hn, List.map_cons, List.map_nil, List.getElem_cons_zero,
      List.getElem_cons_succ]
    . have: n > 0 := by exact Nat.zero_lt_of_ne_zero hn
      have hPos := toBase_lead_nonzero b n hb this
      specialize hbn ((toBase b n)[0]'(by
        simp only [toBase, Nat.digits, List.length_reverse]
        split <;> try simp at hb
        rw[Nat.digitsAux.eq_def]
        split <;> try simp at hn
        simp
      ))
      simp only [toBase, List.getElem_reverse, tsub_zero] at hbn
      have hyp : (b.digits n)[(b.digits n).length - 1]'(by simp[*]) ∈ b.digits n := by apply List.getElem_mem
      specialize hbn hyp
      simp only [toBase, List.getElem_reverse, tsub_zero, gt_iff_lt] at hPos
      rw[hbn] at hPos
      contradiction

  apply eq_if_addLeadingZerosEq_nonzero (maxLen (mapToBase b [m, n]))
  . simp only [ge_iff_le]
    rfl
  . simp only [mapToBase, List.map_cons, List.map_nil, List.getElem_cons_zero, ne_eq]
    refine Nat.ne_zero_iff_zero_lt.mpr ?_
    apply toBase_lead_nonzero
    exact hb
    . omega
  . simp only [mapToBase, List.map_cons, List.map_nil, List.getElem_cons_succ,
    List.getElem_cons_zero, ne_eq]
    by_cases hn: n = 0
    . --simp[toBase, hn]
      --intro h
      simp[stretchLen, mapToBase, toBase, hn, maxLen, addLeadingZeros] at h
      have hbm: ∀x ∈ (b.digits m).reverse, x = 0 := by
        intro x hx
        rw[h] at hx
        simp only [List.mem_replicate, ne_eq, List.length_eq_zero] at hx
        exact hx.2
      have: m > 0 := by exact Nat.zero_lt_of_ne_zero hm
      have hPos := toBase_lead_nonzero b m hb this
      specialize hbm ((toBase b m)[0]'(by
        simp[toBase, Nat.digits]
        split <;> try simp at hb
        rw[Nat.digitsAux.eq_def]
        split <;> try simp at hm
        simp
      ))
      simp[toBase] at hbm
      have hyp : (b.digits m)[(b.digits m).length - 1]'(by simp[*]) ∈ b.digits m := by apply List.getElem_mem
      specialize hbm hyp
      simp only [toBase, List.getElem_reverse, tsub_zero, gt_iff_lt] at hPos
      rw[hbm] at hPos
      contradiction
    . apply Nat.ne_zero_iff_zero_lt.mpr
      apply toBase_lead_nonzero
      exact hb
      exact Nat.zero_lt_of_ne_zero hn
      . by_cases hn: n = 0
        . simp only [stretchLen, addLeadingZeros, maxLen, toBase, List.length_reverse, hn,
          Nat.digits_zero, List.reverse_nil, List.length_nil, max_self, zero_le, max_eq_left,
          mapToBase, List.map_cons, List.map_nil, le_refl, tsub_eq_zero_of_le, List.replicate_zero,
          List.nil_append, tsub_zero, List.append_nil, List.getElem_cons_zero,
          List.getElem_cons_succ] at h
          have hbm: ∀x ∈ (b.digits m).reverse, x = 0 := by
            intro x hx
            rw[h] at hx
            simp at hx
            exact hx.2
          have: m > 0 := by exact Nat.zero_lt_of_ne_zero hm
          have hPos := toBase_lead_nonzero b m hb this
          specialize hbm ((toBase b m)[0]'(by
            simp[toBase, Nat.digits]
            split <;> try simp at hb
            rw[Nat.digitsAux.eq_def]
            split <;> try simp at hm
            simp
          ))
          simp only [toBase, List.getElem_reverse, tsub_zero, List.mem_reverse] at hbm
          have hyp : (b.digits m)[(b.digits m).length - 1]'(by simp[*])
            ∈ b.digits m := by apply List.getElem_mem
          specialize hbm hyp
          simp only [toBase, List.getElem_reverse, tsub_zero, gt_iff_lt] at hPos
          rw[hbm] at hPos
          contradiction
        . simp only [mapToBase, List.map_cons, List.map_nil,
            List.getElem_cons_succ, List.getElem_cons_zero]
          simp[toBase, Nat.digits]
          split <;> try simp at hb
          rw[Nat.digitsAux.eq_def]
          split <;> try simp at hn
          simp
  . exact h
  . simp only [mapToBase, List.map_cons, List.map_nil, List.getElem_cons_zero,
      toBase, Nat.digits]
    split
    . simp only [ge_iff_le, nonpos_iff_eq_zero, OfNat.ofNat_ne_zero] at hb
    . simp only [ge_iff_le, Nat.not_ofNat_le_one] at hb
    rw[Nat.digitsAux.eq_def]
    split <;> try simp only [not_true_eq_false] at hm
    simp only [List.reverse_cons, List.length_append, List.length_reverse, List.length_singleton,
      lt_add_iff_pos_left, add_pos_iff, zero_lt_one, or_true]

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

theorem equal_if_eqInput (m n b : ℕ) (hb : b ≥ 2) :
  (∀ f ∈ inputToBase b hb [m, n], (f ⟨0, by simp⟩).val = f ⟨1, by simp⟩) → m = n := by
    intro h
    simp only [List.length_cons, List.length_singleton, Nat.reduceAdd, inputToBase, Fin.zero_eta,
      Fin.isValue, Fin.mk_one] at h
    apply eq_if_stretchLenEq
    . exact hb
    . have inter := indexEqOfEqZip b (maxLen (mapToBase b [m, n]))  (stretchLen (mapToBase b [m, n])) (stretchLen_of_mapToBase_lt_base b [m, n] hb) (inputToBase.proof_1 b [m, n]) (fun ls hls ↦ stretchLen_uniform (mapToBase b [m, n]) ls hls)
      specialize inter h
      have: 0 < (stretchLen (mapToBase b [m, n])).length := by
        simp[mapToBase_length, stretchLen_length]
      have: 1 < (stretchLen (mapToBase b [m, n])).length := by
        simp[mapToBase_length, stretchLen_length]

      have:= stretchLen_uniform (mapToBase b [m, n])
      have len0 : (stretchLen (mapToBase b [m, n]))[0].length = maxLen (mapToBase b [m, n]) := by
        specialize this  (stretchLen (mapToBase b [m, n]))[0]
        have mem0: (stretchLen (mapToBase b [m, n]))[0] ∈ stretchLen (mapToBase b [m, n]) := by apply List.getElem_mem
        exact this mem0
      have len1 : (stretchLen (mapToBase b [m, n]))[1].length = maxLen (mapToBase b [m, n]) := by
        specialize this  (stretchLen (mapToBase b [m, n]))[1]
        have mem1: (stretchLen (mapToBase b [m, n]))[1] ∈ stretchLen (mapToBase b [m, n]) := by apply List.getElem_mem
        exact this mem1
      apply List.ext_getElem
      . simp only [len0, len1]
      . aesop

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

-- End of correcteness proof
theorem zero_is_zero : 0 = 0 := by
  apply (eqBase_iff_equal 0 0 2 (by norm_num)).mpr
  rfl

theorem ten_is_ten : 10 = 10 := by
  apply (eqBase_iff_equal 10 10 2 (by norm_num)).mpr
  rfl

#print axioms ten_is_ten

theorem foo : 100000 = 100000 := by
  apply (eqBase_iff_equal 100000 100000 2 (by norm_num)).mpr
  native_decide

#print axioms foo

theorem neqBase_iff_neq : a ≠ b ↔ (eqBase 2).negate.eval (inputToBase 2 (by norm_num) [a, b]) := by
  constructor
  . simp only [DFA.negate_eval]
    by_contra h
    simp at h
    rcases h with ⟨h1, h2⟩
    apply h1
    exact (eqBase_iff_equal a b 2 (by norm_num)).mpr h2
  . simp only [DFA.negate_eval]
    intro h
    by_contra h1
    have h2 := (eqBase_iff_equal a b 2 (by norm_num)).mp h1
    simp_all
