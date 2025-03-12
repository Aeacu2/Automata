import Mathlib.Tactic
import Mathlib.Data.List.Basic
import Mathlib.Data.List.Lemmas
import Mathlib.Data.Nat.Digits
import Init.Data.List.Lemmas
import Automata.Replicate
import Automata.LeadingZeros

/-
Major function: inputToBase

Idea: Given a vector of natural numbers 'l',

Step 1: Convert each number to base b, get 'ls' : Fin (m + 1) -> (List ℕ)

Functions involved: toBase, mapToBase
Theorems involved: digits_end_nonzero, toBase_lead_nonzero,
toBase_lt_base, mapToBase_lt_base, mapToBase_length

Step 2: Stretch each list to uniform length by adding leading zeros, get 'lss' : Fin (m + 1) -> (List ℕ)

Functions involved: addZeroes, stretchLen
Theorems involved: addZeroes_elem, addZeroesLength, stretchLen_length, stretchLen_uniform

Step 3: Zip the lists together, giving less than base proofs to turn Nats into Fin bs, to get the input to automatas: List (Fin (l.length) → Fin b)

Functions involved: zipToAlphabetFin
Theorems involved: zipTailHlb, zipTailHlss, zipTailHls, zipToAlphabetFin_length
-/

def toBase (b : ℕ) (n : ℕ): List ℕ :=
  (Nat.digits b n).reverse

theorem digits_end_nonzero (b: ℕ) (n: ℕ) (hb: b ≥ 2) (hn : n > 0) :
  (Nat.digits b n)[(Nat.digits b n).length - 1]'(by
  simp[Nat.digits]
  split <;> try simp at hb
  rename_i x y
  rw[Nat.digitsAux.eq_def]
  split <;> try simp at hn
  simp
  ) > 0 := by
  have:= Nat.digits_of_two_le_of_pos hb hn
  induction' n using Nat.strong_induction_on with n ih
  simp[this]
  have h1: n / b < n := Nat.div_lt_self hn hb
  by_cases hnb : n / b ≠ 0
  have: n / b > 0 := by exact Nat.zero_lt_of_ne_zero hnb
  specialize ih (n / b) h1 this
  have := Nat.digits_of_two_le_of_pos hb this
  specialize ih this
  aesop
  . simp only [ne_eq, Decidable.not_not] at hnb
    have: b.digits (n / b) = [] := by
      rw[hnb]
      apply Nat.digits_zero
    simp[this]
    have: n = b * (n / b) + n % b := by
      exact Eq.symm (Nat.div_add_mod n b)
    simp[hnb] at this
    rw[← this]
    exact hn

theorem toBase_len_nonzero (b: ℕ) (n: ℕ) (hb: b ≥ 2) (hn : n > 0) :
  0 < (toBase b n).length := by
  simp only [toBase, Nat.digits, List.length_reverse]
  split <;> try simp at hb
  rw[Nat.digitsAux.eq_def]
  split <;> try simp at hn
  simp

theorem toBase_lead_nonzero (b: ℕ) (n: ℕ) (hb: b ≥ 2) (hn : n > 0) :
  (toBase b n)[0]'(by apply toBase_len_nonzero<;> assumption) > 0 := by
  simp[toBase]
  exact digits_end_nonzero b n hb hn

theorem toBase_lt_base (b: ℕ) (n: ℕ) (hb: b ≥ 2) :
  x ∈ (toBase b n) → x < b := by
  intro h
  simp only [toBase] at h
  have h1: x ∈ Nat.digits b n := List.mem_reverse.mp h
  apply Nat.digits_lt_base
  exact hb
  exact h1

def ofBase (b : ℕ) (l : List ℕ) : ℕ :=
  l.foldl (fun x y => y + b * x) 0

theorem ofBase_toBase (b: ℕ) (n: ℕ) : ofBase b (toBase b n) = n := by
  simp only [toBase, ofBase, List.foldl_reverse, add_comm, mul_comm]
  have h: Nat.ofDigits b (b.digits n) = n := Nat.ofDigits_digits b n
  nth_rewrite 2 [← h]
  rw [Nat.ofDigits_eq_foldr]
  rfl

theorem toBase_ofBase' (b: ℕ) (l: List ℕ) (hb: 1 < b) (hlb : ∀ x ∈ l, x < b) (hlen : l.length > 0) (hlead : l[0] > 0) :
  toBase b (ofBase b l) = l := by
  have := Nat.digits_ofDigits b hb l.reverse
  specialize this (by simp_all)
  specialize this (by
    intro h
    simp[List.getLast]
    suffices : ¬ l[0] = 0
    . convert this
      apply List.head_eq_getElem l
    exact Nat.not_eq_zero_of_lt hlead
  )
  rw[toBase, ofBase]
  rw[Nat.ofDigits_eq_foldr] at this
  simp_all only [gt_iff_lt, Nat.cast_id, List.foldr_reverse, List.reverse_reverse]


def addZeroes (n: ℕ) (l: List ℕ): List ℕ :=
  (List.replicate n 0) ++ l

theorem addZeroes_elem :
  x ∈ (addZeroes n l) → x = 0 ∨ x ∈ l := by
  intro h
  simp only [addZeroes, List.mem_append, List.replicate] at h
  rcases h with (h | h)
  . left
    have : x ∈ [0] := List.replicate_subset_singleton n 0 h
    exact Finset.mem_zero.mp this
  . right
    exact h

theorem addZeroesLength (n: ℕ) (l: List ℕ) :
  (addZeroes n l).length = n + l.length :=
  by simp only [addZeroes, List.length_append, List.length_replicate]

theorem addZeroes_zero (n: ℕ) (l: List ℕ) (hi : i < n):
  (addZeroes n l)[i]'(by simp[addZeroesLength]; omega) = 0 := by
  simp only [addZeroes]
  apply List.getElem_of_replicate_append_left
  exact hi

theorem ofBase_addZeroes (b: ℕ) (n: ℕ) (l: List ℕ) :
  ofBase b (addZeroes n l) = ofBase b l := by
  simp only [ofBase, addZeroes]
  induction n
  case zero => simp
  case succ n ih =>
    simp [addZeroes, List.replicate, List.foldl, ih]

def List.remLeadZero (l: List ℕ) : List ℕ :=
  match l with
  | [] => []
  | x :: xs => if x = 0 then xs.remLeadZero else l

def List.splitLeadZero (l: List ℕ) : (List ℕ) × (List ℕ) :=
  match l with
  | [] => ⟨[], []⟩
  | x :: xs => if x = 0 then let ⟨ys, zs⟩ := xs.splitLeadZero
   ⟨0 :: ys, zs⟩ else ⟨[], l⟩

theorem splitLeadZero_append (l: List ℕ) :
  let ⟨ys, zs⟩ := l.splitLeadZero; ys ++ zs = l := by
  induction l
  case nil => simp[List.splitLeadZero]
  case cons x xs ih =>
    simp[List.splitLeadZero]
    by_cases hx: x = 0
    . simp only [hx, ↓reduceIte, List.cons_append, List.cons.injEq, true_and]
      rw[ih]
    . simp[List.splitLeadZero, hx]

theorem splitLeadZero_left (l: List ℕ) :
  let ⟨ys, _⟩ := l.splitLeadZero; ∀ x ∈ ys, x = 0 := by
  induction l
  case nil => simp[List.splitLeadZero]
  case cons x xs ih =>
    simp[List.splitLeadZero]
    by_cases hx: x = 0
    . simp only [hx, ↓reduceIte, List.mem_cons, forall_eq_or_imp, true_and]
      exact ih
    . simp[List.splitLeadZero, hx]

theorem splitLeadZero_left_replicate (l: List ℕ) :
  let ⟨ys, _⟩ := l.splitLeadZero; ys = List.replicate ys.length 0 := by
  induction l
  case nil => simp[List.splitLeadZero]
  case cons x xs ih =>
    simp[List.splitLeadZero]
    by_cases hx: x = 0
    . simp only [hx, ↓reduceIte, List.length_cons, List.replicate, List.cons.injEq, true_and]
      exact ih
    . simp[List.splitLeadZero, hx]

theorem splitLeadZero_right (l: List ℕ) :
  let ⟨_, zs⟩ := l.splitLeadZero; zs = l.remLeadZero := by
  induction l
  case nil => simp[List.splitLeadZero, List.remLeadZero]
  case cons x xs ih =>
    simp[List.splitLeadZero]
    by_cases hx: x = 0
    . simp[List.splitLeadZero, hx, List.remLeadZero]
      rw[ih]
    . simp[List.splitLeadZero, hx, List.remLeadZero]

theorem remLeadZero_mem (l : List ℕ) (x : ℕ) : x ∈ l.remLeadZero → x ∈ l := by
  intro h
  induction l
  case nil => simp_all[List.remLeadZero]
  case cons y ys ih =>
    simp[List.remLeadZero] at h
    aesop

theorem remLeadZero_head (l : List ℕ)
  (h : l.remLeadZero.length > 0) :
  l.remLeadZero[0] > 0 := by
  induction l
  case nil => simp[List.remLeadZero] at h
  case cons x xs ih =>
    simp[List.remLeadZero] at h
    by_cases hx: x = 0
    . simp[List.remLeadZero, hx]
      apply ih
    . simp[List.remLeadZero, hx]
      omega

theorem remLeadZero_addZeroes (n: ℕ) (l: List ℕ) :
  (addZeroes n l).remLeadZero = l.remLeadZero := by
  simp only [addZeroes, List.remLeadZero, List.replicate]
  induction n
  case zero => simp
  case succ n ih =>
    rw[List.remLeadZero.eq_def]
    simp[List.replicate]
    exact ih

theorem splitLeadZero_addZeroes (l : List ℕ):
  addZeroes (l.length - l.remLeadZero.length) (l.remLeadZero) = l := by
  nth_rw 4 [← splitLeadZero_append l]
  rw[splitLeadZero_right, splitLeadZero_left_replicate]
  simp[addZeroes, List.replicate]
  rw[← splitLeadZero_right]
  have: l = l.splitLeadZero.1 ++ l.splitLeadZero.2 := by
    rw[splitLeadZero_append]
  nth_rw 1 [this]
  simp


theorem toBase_ofBase'' (b: ℕ) (l: List ℕ) (hb: 1 < b) (hlb : ∀ x ∈ l, x < b) :
  (toBase b (ofBase b l)) = l.remLeadZero := by
  nth_rw 1 [← splitLeadZero_addZeroes l]
  simp[ofBase_addZeroes, remLeadZero_addZeroes]
  by_cases h: l.remLeadZero.length = 0
  . simp_all[ofBase, toBase]
  . have := remLeadZero_head l (by omega)
    apply toBase_ofBase'
    . exact hb
    . intro x hx
      apply hlb
      apply remLeadZero_mem
      exact hx
    . exact this

theorem toBase_ofBase (b: ℕ) (l: List ℕ) (hb: 1 < b) (hlb : ∀ x ∈ l, x < b) :
  ∃ k, addZeroes k (toBase b (ofBase b l)) = l := by
  use (l.length - l.remLeadZero.length)
  rw[toBase_ofBase'' b l hb hlb]
  exact splitLeadZero_addZeroes l

def maxLen : (l: List (List α)) → ℕ
  | [] => 0
  | x :: xs => max x.length (maxLen xs)

theorem cons_lt_maxLen (l: List α) (ls: List (List α)) :
  l.length ≤ maxLen (l :: ls) := by
  induction ls generalizing l with
  | nil => simp[maxLen]
  | cons head tail _ =>
    simp [maxLen]

theorem len_le_maxLen (l: List α) (ls: List (List α)) :
  l ∈ ls → l.length ≤ maxLen ls := by
  intro h
  induction ls generalizing l with
  | nil => simp only [List.not_mem_nil] at h
  | cons head tail ih =>
    have h1: l = head ∨ l ∈ tail := List.eq_or_mem_of_mem_cons h
    rcases h1 with (rfl | h1)
    . apply cons_lt_maxLen
    . simp[maxLen]
      right
      exact ih l h1

def maxLenFin (v: (Fin (m + 1) → List ℕ)) : ℕ :=
  maxLen (List.ofFn v)

theorem len_le_maxLenFin (v: (Fin (m + 1) → List ℕ)) (i: Fin (m + 1)) :
  (v i).length ≤ maxLenFin v := by
  apply len_le_maxLen
  refine (List.mem_ofFn v (v i)).mpr ?_
  exact Set.mem_range_self i

def mapToBase (b: ℕ) (v : Fin (m + 1) → ℕ) : Fin (m + 1) → List ℕ :=
  fun i => toBase b (v i)

theorem mapToBase_lt_base (b: ℕ) (v : Fin (m + 1) → ℕ) (hb: b > 1) (i : Fin (m + 1)) :
  ∀ x ∈ (mapToBase b v) i, x < b  := by
  intro x h
  simp only [mapToBase] at h
  apply toBase_lt_base
  omega
  exact h

def stretchLen (ls: Fin (m + 1) → (List ℕ)) : Fin (m + 1) → (List ℕ) :=
  fun i => addZeroes (maxLenFin ls - (ls i).length) (ls i)

theorem stretchLen_uniform (ls: Fin (m + 1) → (List ℕ)) (i : Fin (m + 1)) :
  (stretchLen ls i).length = maxLenFin ls:= by
  simp only [stretchLen, addZeroes, List.length_append, List.length_replicate]
  have := len_le_maxLenFin ls i
  omega

theorem stretchLen_of_mapToBase_lt_base (b: ℕ) (v: Fin (m + 1) → ℕ) (hb: b > 1) (i : Fin (m + 1)) :
  ∀ x ∈ (stretchLen (mapToBase b v)) i, x < b := by
  intro x h
  simp only [stretchLen, addZeroes] at h
  have h1 := addZeroes_elem h
  rcases h1 with (rfl | h1)
  . omega
  apply mapToBase_lt_base
  . exact hb
  . exact h1

theorem zipTailHlb (ls: Fin (m + 1) → (List ℕ)) (hlb: ∀ i, ∀ x ∈ ls i, x < b) :
  ∀ i, ∀ x ∈ (ls i).tail, x < b := by
  intro i x h
  specialize hlb i
  apply hlb
  . apply List.mem_of_mem_tail h

theorem zipTailHls (ls: Fin (m + 1) → (List ℕ)) (hls : ∀ i, (ls i).length = l + 1) :
  ∀ i, (ls i).tail.length = l := by
  intro i
  have h := List.length_tail (ls i)
  rw[hls] at h
  exact h

def zip (ls: Fin (m + 1) → (List ℕ)) (hlb: ∀ i, ∀ x ∈ ls i, x < (b + 2)) (hls : ∀ i, (ls i).length = (ls 0).length) : List (Fin (m + 1) → Fin (b + 2))  :=
  match hh:(ls 0).length with
  | 0 => []
  | l+1 =>
     (fun i =>
       have : 0 < (ls i).length := by
         rw[hls]
         omega
       ⟨(ls i)[0], by apply hlb; exact List.getElem_mem this⟩) :: (zip (fun i => (ls i).tail)
        (by apply zipTailHlb; exact hlb)
        (by apply zipTailHls; intro i; rw[hls]; simp; omega))

def toWord (v: Fin (m + 1) → ℕ) (b: ℕ) : List (Fin (m + 1) → Fin (b + 2)) :=
  zip (stretchLen (mapToBase (b + 2) v)) (by
    apply stretchLen_of_mapToBase_lt_base
    omega
  ) (by
    intro i
    apply stretchLen_uniform
  )

/-- Hello, Aeacus! -/
def getDigits {b : ℕ} (ls : List (Fin (m + 1) → Fin (b + 2))) : Fin (m + 1) → List ℕ :=
  fun i => List.map (fun f => f i) ls

theorem getDigits_uniform (ls : List (Fin (m + 1) → Fin (b + 2))) (i : Fin (m + 1)) :
  (getDigits ls i).length = ls.length := by
  simp only [getDigits, List.length_map]

theorem getDigits_lt_base (ls : List (Fin (m + 1) → Fin (b + 2))) (i : Fin (m + 1)) :
  ∀ x ∈ getDigits ls i, x < b + 2 := by
  intro x h
  simp only [getDigits, List.mem_map] at h
  rcases h with ⟨f, hf, rfl⟩
  exact (f i).isLt

theorem getDigits_of_nil (i : Fin (m + 1)) :
  @getDigits m b [] i = [] := by
  simp[getDigits]

theorem getDigits_of_zip' (ls: Fin (m + 1) → (List ℕ)) (hlb: ∀ i, ∀ x ∈ ls i, x < (b + 2)) (hls : ∀ i, (ls i).length = (l + 1)) :
  getDigits (zip ls hlb hls) = ls := by
  funext i
  simp only [getDigits, zip]
  have h1: 0 < (ls i).length := by
    rw[hls]
    omega
  have h2: (ls i).length = l + 1 := by
    rw[hls]
  simp only [List.map, zip]
  induction l generalizing ls
  case zero =>
    simp[zip]
    exact Eq.symm (List.eq_of_length_one (ls i) (hls i))
  case succ l ih =>
    specialize ih (fun i => (ls i).tail)
    specialize ih (by apply zipTailHlb; exact hlb)
    specialize ih (by apply zipTailHls; exact hls)
    specialize ih (by aesop) (by aesop)
    suffices : List.map (fun f ↦ ↑(f i)) (zip (fun i ↦ (ls i).tail) _ _) = (ls i).tail
    . rw[this]
      have := @List.cons_head?_tail ℕ (ls i)
      apply this
      simp [List.getElem_zero]
      rw [← @List.head?_eq_head]
    simp only [List.map, zip]
    exact ih

theorem getDigits_of_zip (ls: Fin (m + 1) → (List ℕ)) (hlb: ∀ i, ∀ x ∈ ls i, x < (b + 2)) (hls : ∀ i, (ls i).length = l) :
  getDigits (zip ls hlb hls) = ls := by
  induction l generalizing ls with
  | zero =>
    simp only [zip]
    funext i
    rw[getDigits_of_nil]
    simp_all only [List.length_eq_zero]
  | succ l ih =>
    exact getDigits_of_zip' ls hlb hls

theorem zip_of_getDigits (ls: List (Fin (m + 1) → Fin (b + 2))) :
  ls = @zip m b ls.length (getDigits ls) (fun i x a ↦ getDigits_lt_base ls i x a) (fun i ↦ getDigits_uniform ls i) := by
  induction ls with
  | nil => simp[zip]
  | cons head tail ih =>
    simp[zip, getDigits]
    nth_rw 1 [ih]
    congr

theorem getDigits_length (ls : List (Fin (m + 1) → Fin (b + 2))) (i : Fin (m + 1)) : (getDigits ls i).length = ls.length := by
  simp only [getDigits, List.length_map]

def toNat_aux (b : ℕ) (Digits : Fin (m + 1) → List ℕ) : Fin (m + 1) → ℕ :=
  fun i => ofBase (b + 2) (Digits i)

theorem toNat_aux_of_mapToBase (b: ℕ) (v: Fin (m + 1) → ℕ) :
  toNat_aux b (mapToBase (b + 2) v) = v := by
  funext i
  simp[toNat_aux, mapToBase, ofBase_toBase]

theorem toNat_aux_of_stretchLen (b: ℕ) (v: Fin (m + 1) → ℕ) :
  toNat_aux b (stretchLen (mapToBase (b + 2) v)) = v := by
  funext i
  simp[toNat_aux, stretchLen, ofBase_addZeroes, ofBase_toBase, mapToBase]

def toNat (ls : List (Fin (m + 1) → Fin (b + 2))) : Fin (m + 1) → ℕ :=
  toNat_aux b (getDigits ls)

theorem toWord_of_toNat' (ls : List (Fin (m + 1) → Fin (b + 2))) (hLen: ls.length > 0) (hHead : ls[0] ≠ fun _ => 0) :
  ls = toWord (toNat ls) b := by
  simp[toWord, toNat, mapToBase]
  have : (stretchLen (mapToBase (b + 2) (toNat_aux b (getDigits ls)))) = (getDigits ls) := by
      sorry

  simp_rw[this]
  have step := zip_of_getDigits ls
  nth_rw 1 [step]
  congr
  sorry







theorem toWord_of_toNat (ls : List (Fin (m + 1) → Fin (b + 2))) :
  ∃ (k : ℕ), ls = padZeros k (toWord (toNat ls) b) := by
  sorry

theorem toNat_of_toWord (v: Fin (m + 1) → ℕ) (b: ℕ) :
  toNat (toWord v b) = v := by
  simp[toNat, toNat_aux, getDigits, toWord, zip, stretchLen, addZeroes, mapToBase, toBase]
  have : (getDigits (zip (stretchLen (mapToBase (b + 2) v)) (stretchLen_of_mapToBase_lt_base (b + 2) v (by omega)) (stretchLen_uniform (mapToBase (b + 2) v))) = stretchLen (mapToBase (b + 2) v)) := by

    have : ∀ (i : Fin (m + 1)), ∀ x ∈ stretchLen (mapToBase (b + 2) v) i, x < b + 2 := by
      apply stretchLen_of_mapToBase_lt_base
      omega
    let l := maxLenFin (mapToBase (b + 2) v)
    convert getDigits_of_zip (l := l) (stretchLen (mapToBase (b + 2) v)) this ?_
  rw[this]
  exact toNat_aux_of_stretchLen b v


/- USELESS CODES
def digits' (b: ℕ) (n: ℕ) (h: b > 1) : List (Fin b) :=
  (Nat.digits b n).attach.map (fun x => ⟨x.1, Nat.digits_lt_base h x.2⟩)

def zipToAlphabet (n : ℕ) (l : ℕ) (lss: List (List ℕ)) (hlss: lss.length = l) (hls : ∀ ls ∈ lss, ls.length = n) : List (Fin l → ℕ) :=
  match n with
  | 0 => []
  | m+1 =>
     (fun i =>
       have : 0 < lss[i].length := by
         rw[hls]
         omega
         refine List.mem_iff_get.mpr ?_
         subst hlss
         use i
         rfl

       lss[i][0]) :: (zipToAlphabet m l (lss.map (fun ls => ls.tail))
        (by simp only [List.length_map, hlss]) (fun
          | .nil => by
            simp only [List.mem_map, List.length_nil, forall_exists_index, and_imp]
            intro x hx
            specialize hls x hx
            rcases x
            . simp only [List.length_nil, self_eq_add_left, AddLeftCancelMonoid.add_eq_zero,
              one_ne_zero, and_false] at hls
            . simp only [List.length_cons, add_left_inj] at hls
              simp only [List.tail_cons]
              intro h
              simp only [h, List.length_nil] at hls
              assumption
          | .cons head tail => by
            simp only [List.mem_map, List.length_cons, forall_exists_index, and_imp]
            intro x hx h
            specialize hls x hx
            have : x.tail.length = m := by
              have: x.length - 1 = m := by
                omega
              rw[← this]
              apply tailLen x
            rw[← this, h]
            have hxtail := tailLen x.tail
            rw[h, List.tail] at hxtail
            have: (head :: tail).length > 0 := by simp
            omega
            ))

def toBaseZip (b : ℕ) (l: List ℕ) : (List (Fin l.length → ℕ)) :=
  let ls := mapToBase b l
  let n := maxLen ls
  let lss := stretchLen (ls)
  zipToAlphabet n l.length lss (by simp only [mapToBase_length b l, stretchLen_length ls]) (by
    intro ls hls
    apply stretchLen_uniform
    assumption)
-/
