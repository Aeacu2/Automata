import Mathlib.Tactic
import Mathlib.Data.List.Basic
import Automata.DFA
import Automata.Input
import Automata.Boolean
import Automata.Replicate
import Automata.LeadingZeros

-- The equality checking automata for two numbers in a long tuple of inputs.
def eqBase (b m: ℕ) (i j : Fin m): DFA (Fin m → Fin (b + 2)) (Fin 2) := {
  transition := fun v s => match s with
    | 0 => if (v i).val  == v j then 0 else 1
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
theorem eqBase_if_equal_aux (input: List (Fin n → Fin (k+2))):
  (∀ f ∈ input, (f a).val = f b) → (eqBase k n a b).evalFrom input 0 := by
  intro h
  induction input
  case nil =>
    simp[eqBase, DFAO.evalFrom, DFAO.transFrom]
  case cons f fs ih =>
    have h1 := h f
    simp only [List.mem_cons, true_or, true_implies] at h1
    simp only [DFAO.evalFrom, DFAO.transFrom, Fin.isValue]
    have: ((eqBase k n a b).transition f 0) = 0 := by
      simp only [eqBase, Fin.isValue, beq_iff_eq, h1, ↓reduceIte]
    rw[this]
    apply ih
    intro f' hf'
    apply h
    simp only [List.mem_cons, or_true, hf']


-- Left to right, much harder
theorem eqBase_trans_zero (state : Fin 2) (f : Fin n → Fin (k+2)) :
  (eqBase k n a b).transition f state = 0 ↔ state = 0 ∧ (f a).val = f b := by
  simp only [eqBase, Fin.isValue, beq_iff_eq]
  split <;> simp


theorem eqBase_transFrom_zero (state: Fin 2) (l : List (Fin n → Fin (k+2))) :
  (eqBase k n a b).transFrom l state = 0 ↔ state = 0 ∧ ∀ f ∈ l, (f a).val = f b := by
  induction l generalizing state
  case nil =>
    simp [DFAO.transFrom]
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

theorem eqInput_if_eqBase_aux (input: List (Fin n → Fin (k+2))):
  (eqBase k n a b).transFrom input 0 = 0 → (∀ f ∈ input, (f a).val = f b) := by
  intro h
  exact (eqBase_transFrom_zero 0 input).mp h |>.2

theorem eqInput_if_eqBase (input: List (Fin n → Fin (k+2))):
  (eqBase k n a b).evalFrom input 0 → (∀ f ∈ input, (f a).val = f b) := by
  intro h
  have:= eqInput_if_eqBase_aux (b := b) (a := a) input
  apply this
  -- simp[DFAO.evalFrom, eqBase] at h
  simp_all only [DFAO.evalFrom, eqBase, beq_iff_eq, true_implies]

-- End of Left to right, final step 1 statement:
theorem eqBase_iff_eqInput (k : ℕ) (input: List (Fin n → Fin (k+2))):
  (eqBase k n a b).eval input ↔ (∀ f ∈ input, (f a).val = f b) := by
  constructor
  . apply eqInput_if_eqBase input
  . apply eqBase_if_equal_aux input


--An Auxillary theorem for left to right
theorem eqZipOfIndexEq (lsLength : ℕ) (lss: Fin l → (List ℕ))
      (hlb: ∀ x : Fin l, ∀ ls ∈ lss x, ls < k+2 ) (m n : Fin l)
      (hls: ∀ x : Fin l, (lss x).length = lsLength) (hIndexEq: ∀i, ∀ (hi : i < lsLength), (lss m)[i]'(by
        specialize hls m
        exact Nat.lt_of_lt_of_eq hi (id (Eq.symm hls))
      ) = (lss n)[i]'(by
        specialize hls n
        exact Nat.lt_of_lt_of_eq hi (id (Eq.symm hls))
      )): ∀ f ∈ (@zip l k lsLength lss hlb hls), (f m).val = f n:= by
      intro f hf
      induction lsLength generalizing lss
      case zero =>
        simp only [zip, List.not_mem_nil] at hf
      case succ lsLength ih =>
        simp only [zip, List.mem_cons] at hf
        rcases hf with hf | hf
        . specialize hIndexEq 0 (by norm_num)
          simp[hf, hIndexEq]
        . apply ih (fun i ↦ (lss i).tail)
          . intro i hi
            rw[List.getElem_tail, List.getElem_tail]
            apply hIndexEq
            simp only [add_lt_add_iff_right]
            exact hi
          . exact hf

theorem eqInput_if_equal (input : Fin l → ℕ) (m n : Fin l) :
  input m = input n →  ∀ f ∈ toWord input k, (f m).val = (f n) := by
    intro h

    have stretchLenEq: (stretchLen (mapToBase (k+2) input)) m =
    (stretchLen (mapToBase (k+2) input)) n := by
      simp_all [stretchLen, mapToBase]

    have lenStretchLen0 : ((stretchLen (mapToBase (k+2) input)) m).length = maxLenFin (mapToBase (k+2) input) := by
      apply stretchLen_uniform

    have lenStretchLen1 : ((stretchLen (mapToBase (k+2) input)) n).length = maxLenFin (mapToBase (k+2) input) := by
      apply stretchLen_uniform

    have stretchLenIndexEq (i: ℕ)(hi: i < (maxLenFin (mapToBase (k+2) input))): (stretchLen (mapToBase (k+2) input) m)[i] = (stretchLen (mapToBase (k+2) input) n)[i] := by
      simp only [stretchLenEq]

    intro f hf
    rw[toWord] at hf
    apply eqZipOfIndexEq (maxLenFin (mapToBase (k+2) input)) (stretchLen (mapToBase (k+2) input))
    . apply stretchLenIndexEq
    . exact hf

--Right to left
theorem equal_if_toBaseEq: toBase b m = toBase b n → m = n := by
  intro h
  rw[← ofBase_toBase b n, ← ofBase_toBase b m]
  congr

theorem equal_if_mapToBaseEq (input: Fin l → ℕ) (m n : Fin l) :
  (mapToBase (k+2) input m) = (mapToBase (k+2) input n) → input m = input n := by
  intro h
  simp only [mapToBase] at h
  apply equal_if_toBaseEq
  exact h

theorem eq_if_addZeroesEq_nonzero (n: ℕ) (L: Fin l → (List ℕ)) (k p: Fin l) (hn: n ≥ maxLenFin L)  (lenk :0 < (L k).length) (hk: (L k)[0] ≠ 0) (lenp :0 < (L p).length) (hp: (L p)[0] ≠ 0) :
  addZeroes (n - (L k).length) (L k) = addZeroes (n - (L p).length) (L p) → (L k) = (L p):= by
  intro h
  simp only [ge_iff_le] at hn
  have kLen: (L k).length ≤ n := by
    trans maxLenFin L
    apply len_le_maxLen
    refine (List.mem_ofFn).mpr ?_
    exact exists_apply_eq_apply L k
    exact hn
  have pLen : (L p).length ≤ n := by
    trans maxLenFin L
    apply len_le_maxLen
    refine (List.mem_ofFn).mpr ?_
    exact exists_apply_eq_apply L p
    exact hn

  have hL: n - (L k).length = n - (L p).length := by
    by_contra hL
    have hLen: n - (L k).length < n - (L p).length ∨ n - (L k).length > n - (L p).length := by
      exact Nat.lt_or_gt_of_ne hL
    have kAddLen: (addZeroes (n - (L k).length) (L k)).length = n := by simp only [addZeroesLength]; omega
    have lAddLen: (addZeroes (n - (L p).length) (L p)).length = n :=  by simp only [addZeroesLength]; omega
    rcases hLen with (hLen | hLen)
    .
      have addl : (addZeroes (n - (L p).length) (L p))[n-(L k).length] = 0 := by
        simp[addZeroes]
        apply List.getElem_of_replicate_append_left
        exact hLen

      have addk : (addZeroes (n - (L k).length) (L k))[n - (L k).length] ≠  0 := by
        simp only [addZeroes]
        rw[List.getElem_append_right]
        simp only [List.length_replicate, le_refl, tsub_eq_zero_of_le]
        exact hk
        . simp[*]
      simp_all only [ne_eq, not_true_eq_false]
    .
      have addk : (addZeroes (n - (L k).length) (L k))[n-(L p).length] = 0 := by
        simp[addZeroes]
        apply List.getElem_of_replicate_append_left
        exact hLen
      have addl : (addZeroes (n - (L p).length) (L p))[n-(L p).length] ≠  0 := by
        simp only [addZeroes, ne_eq]
        rw[List.getElem_append_right]
        simp only [List.length_replicate, le_refl, tsub_eq_zero_of_le]
        exact hp
        . simp
      simp_all only [ne_eq]
  rw[← hL] at h
  simp only [addZeroes, List.append_cancel_left_eq] at h
  exact h

theorem contra (input : Fin l → ℕ) (m n : Fin l) (h : (stretchLen (mapToBase (k+2) input) m) = (stretchLen (mapToBase (k+2) input) n)) (hn: input n = 0) (hm : input m ≠ 0) : False := by
  simp[stretchLen, mapToBase, toBase, hn] at h
  have : ∀ x ∈ addZeroes (maxLenFin (mapToBase (k+2) input)) [], x = 0 ∨ x ∈ [] := by
    apply addZeroes_elem
  simp only [List.not_mem_nil, or_false] at this
  rw[← h] at this
  have hbm: ∀x ∈ (toBase (k+2) (input m)), x = 0 := by
    intro x hx
    apply this
    simp only [addZeroes, List.mem_append, List.mem_replicate,
      ne_eq, List.mem_reverse]
    right
    exact List.mem_reverse.mp hx
  have: input m > 0 := by exact Nat.zero_lt_of_ne_zero hm
  have hPos := toBase_lead_nonzero (k+2) (input m) (by omega) this
  specialize hbm ((toBase (k+2) (input m))[0]'(by
      apply toBase_len_nonzero <;> omega
  ))
  have hyp : (toBase (k+2) (input m))[0]'(by
  have:= toBase_len_nonzero (k+2) (input m) (by omega) (by omega)
  omega) ∈ toBase (k+2) (input m) := by apply List.getElem_mem
  specialize hbm hyp
  rw[hbm] at hPos
  contradiction

theorem eq_if_stretchLenEq (input : Fin l → ℕ)  (m n : Fin l) :
  (stretchLen (mapToBase (k+2) input) m) = (stretchLen (mapToBase (k+2) input) n) → input m = input n := by
  intro h
  apply equal_if_mapToBaseEq
  by_cases hm: input m = 0
  . by_cases hn : input n = 0
    . simp[mapToBase, hn, hm]
    . by_contra; apply contra; exact h.symm; exact hm; exact hn
  by_cases hn: input n = 0
  . by_contra; apply contra; exact h; exact hn; exact hm
  apply eq_if_addZeroesEq_nonzero (maxLenFin (mapToBase (k+2) input)) (mapToBase (k+2) input) m n
  . simp only [ge_iff_le]; rfl
  . simp only [mapToBase, ne_eq]
    refine Nat.ne_zero_iff_zero_lt.mpr ?_
    apply toBase_lead_nonzero
    simp_all only [ge_iff_le, le_add_iff_nonneg_left, zero_le]
    . omega
  . simp only [mapToBase, ne_eq]
    refine Nat.ne_zero_iff_zero_lt.mpr ?_
    apply toBase_lead_nonzero
    simp_all only [ge_iff_le, le_add_iff_nonneg_left, zero_le]
    . omega
  . simp_all[stretchLen]
  . simp only [mapToBase]
    apply toBase_len_nonzero <;> omega
  . simp only [mapToBase]
    apply toBase_len_nonzero <;> omega

theorem indexEqOfEqZip (lsLength : ℕ) (lss: Fin l → (List ℕ))
      (hlb: ∀ x : Fin l, ∀ ls ∈ lss x, ls < k+2 ) (m n : Fin l)
      (hls: ∀ x : Fin l, (lss x).length = lsLength) :
      (∀f ∈ (@zip l k lsLength lss hlb hls), (f m).val = f n)
      → ∀i, ∀ (hi : i < lsLength), (lss m)[i]'(by
        specialize hls m
        exact Nat.lt_of_lt_of_eq hi (id (Eq.symm hls))
      ) = (lss n)[i]'(by
        specialize hls n
        exact Nat.lt_of_lt_of_eq hi (id (Eq.symm hls))
      ) := by
        intro h
        induction lsLength generalizing lss
        case zero => intro i hi; contradiction
        case succ s ih =>
          intro i hi
          simp [zip, List.mem_cons,
            forall_eq_or_imp] at h
          rcases h with ⟨h1, h2⟩
          specialize ih (fun i ↦ (lss i).tail)
          specialize ih (zipTailHlb lss hlb)
          specialize ih (zipTailHls lss hls)
          specialize ih h2
          simp only [List.getElem_tail] at ih
          match i with
          | 0 => exact h1
          | n + 1 =>
            simp only [add_lt_add_iff_right] at hi
            specialize ih n hi
            exact ih

theorem equal_if_eqInput (input : Fin l → ℕ) (m n : Fin l) :
  (∀ f ∈ toWord input k, (f m).val = (f n)) → input m = input n := by
    intro h
    simp only [toWord] at h
    apply @eq_if_stretchLenEq l k input m n
    .
      have inter := indexEqOfEqZip (maxLenFin (mapToBase (k+2) input))  (stretchLen (mapToBase (k+2) input)) (stretchLen_of_mapToBase_lt_base (k+2) input (by omega)) m n (by exact fun x ↦ stretchLen_uniform (mapToBase (k + 2) input) x)
      specialize inter h
      have:= stretchLen_uniform (mapToBase (k+2) input)
      have len0 : ((stretchLen (mapToBase (k+2) input) m)).length = maxLenFin (mapToBase (k+2) input) := by
        exact this m
      have len1 : ((stretchLen (mapToBase (k+2) input) n)).length = maxLenFin (mapToBase (k+2) input) := by
        exact this n
      apply List.ext_getElem
      . simp_all only
      . intro _ _ _
        apply inter
        simp_all only

-- Step 2 Complete
theorem eqInput_iff_equal (input : Fin l → ℕ) (m n : Fin l) :
  (∀ f ∈ toWord input k, (f m).val = (f n)) ↔ input m = input n := by
    constructor
    . apply equal_if_eqInput
    . apply eqInput_if_equal

-- Final theorem
    theorem eqBase_iff (b m: ℕ) (v : Fin m → ℕ) (i j : Fin m):
  (eqBase b m i j).eval (toWord v b) ↔ v i = v j  := by
  constructor
  . intro h
    rw[← eqInput_iff_equal]
    exact fun f a ↦ eqInput_if_eqBase (toWord v b) h f a
  . intro h
    refine (eqBase_iff_eqInput b (toWord v b)).mpr ?_
    exact fun f a ↦ eqInput_if_equal v i j h f a


theorem equality_respectZero : (eqBase b l m n).respectZero := by
  rw[DFA.respectZero]
  intro x c
  constructor
  intro h
  rw[padZeros]
  rw[DFAO.eval, DFAO.evalFrom, DFAO.transFrom_of_append]
  nth_rw 1 [eqBase]
  simp only [Fin.isValue, beq_iff_eq]
  suffices: (DFAO.transFrom (eqBase b l m n) (List.replicate c fun _ ↦ 0) (eqBase b l m n).start) = 0
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
    simp only [Fin.isValue]
    suffices: (DFAO.transFrom (eqBase b l m n) (List.replicate c fun _ ↦ 0) (eqBase b l m n).start) = 0
    . rw[this]
      simp[DFAO.eval, DFAO.evalFrom] at h
      nth_rw 1 3 [eqBase] at h
      simp only [Fin.isValue] at h
      exact h
    nth_rw 2 [eqBase]
    simp only [Fin.isValue]
    apply eqBase_transFrom_zero 0 (List.replicate c fun _ ↦ 0) |>.mpr
    simp_all only [Fin.isValue, List.mem_replicate, ne_eq, Fin.val_zero, implies_true, and_self]
