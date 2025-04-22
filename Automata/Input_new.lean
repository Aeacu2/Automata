import Mathlib.Tactic
import Mathlib.Data.List.Basic
import Mathlib.Data.List.Lemmas
import Mathlib.Data.Nat.Digits
import Init.Data.List.Lemmas
import Automata.Replicate
import Automata.LeadingZeros
import Automata.Fin

/-
Major function: inputToBase

Idea: Given a vector of natural numbers 'l',

Step 1: Convert each number to base b, get 'ls' : Fin m -> (List ℕ)

Functions involved: toBase, mapToBase
Theorems involved: digits_end_nonzero, toBase_lead_nonzero,
toBase_lt_base, mapToBase_lt_base, mapToBase_length

Step 2: Stretch each list to uniform length by adding leading zeros, get 'lss' : Fin m -> (List ℕ)

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

theorem addZeroes_succ (n: ℕ) (l: List ℕ) :
  addZeroes (n+1) l = 0 :: addZeroes n l := by
  simp only [addZeroes, List.replicate, List.cons_append]

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

theorem addZeroes_addZeroes (n m: ℕ) (l: List ℕ) :
  addZeroes n (addZeroes m l) = addZeroes (n + m) l := by
  simp[addZeroes, List.replicate, ← List.append_assoc]

theorem ofBase_addZeroes (b: ℕ) (n: ℕ) (l: List ℕ) :
  ofBase b (addZeroes n l) = ofBase b l := by
  simp only [ofBase, addZeroes]
  induction n
  case zero => simp
  case succ n ih =>
    simp [addZeroes, List.replicate, List.foldl, ih]

def List.remAddZero (l: List ℕ) : List ℕ :=
  match l with
  | [] => []
  | x :: xs => if x = 0 then xs.remAddZero else l

def List.splitAddZero (l: List ℕ) : (List ℕ) × (List ℕ) :=
  match l with
  | [] => ⟨[], []⟩
  | x :: xs => if x = 0 then let ⟨ys, zs⟩ := xs.splitAddZero
   ⟨0 :: ys, zs⟩ else ⟨[], l⟩

theorem splitAddZero_append (l: List ℕ) :
  let ⟨ys, zs⟩ := l.splitAddZero; ys ++ zs = l := by
  induction l
  case nil => simp[List.splitAddZero]
  case cons x xs ih =>
    simp[List.splitAddZero]
    by_cases hx: x = 0
    . simp only [hx, ↓reduceIte, List.cons_append, List.cons.injEq, true_and]
      rw[ih]
    . simp[List.splitAddZero, hx]

theorem splitAddZero_left (l: List ℕ) :
  let ⟨ys, _⟩ := l.splitAddZero; ∀ x ∈ ys, x = 0 := by
  induction l
  case nil => simp[List.splitAddZero]
  case cons x xs ih =>
    simp[List.splitAddZero]
    by_cases hx: x = 0
    . simp only [hx, ↓reduceIte, List.mem_cons, forall_eq_or_imp, true_and]
      exact ih
    . simp[List.splitAddZero, hx]

theorem splitAddZero_left_replicate (l: List ℕ) :
  let ⟨ys, _⟩ := l.splitAddZero; ys = List.replicate ys.length 0 := by
  induction l
  case nil => simp[List.splitAddZero]
  case cons x xs ih =>
    simp[List.splitAddZero]
    by_cases hx: x = 0
    . simp only [hx, ↓reduceIte, List.length_cons, List.replicate, List.cons.injEq, true_and]
      exact ih
    . simp[List.splitAddZero, hx]

theorem splitAddZero_right (l: List ℕ) :
  let ⟨_, zs⟩ := l.splitAddZero; zs = l.remAddZero := by
  induction l
  case nil => simp[List.splitAddZero, List.remAddZero]
  case cons x xs ih =>
    simp[List.splitAddZero]
    by_cases hx: x = 0
    . simp[List.splitAddZero, hx, List.remAddZero]
      rw[ih]
    . simp[List.splitAddZero, hx, List.remAddZero]

theorem remAddZero.length (l: List ℕ) :
  l.remAddZero.length ≤ l.length := by
  induction l
  case nil => simp[List.remAddZero]
  case cons x xs ih =>
    simp[List.remAddZero]
    by_cases hx: x = 0
    . simp only [hx, ↓reduceIte]
      exact Nat.le_add_right_of_le ih
    . simp[List.remAddZero, hx]

theorem remAddZero_nonZero (l: List ℕ) (hLen: l.length > 0) (hHead : l[0] ≠ 0) :
  l.remAddZero = l := by
  induction l
  case nil => simp at hLen
  case cons x xs ih =>
    simp[List.remAddZero]
    by_cases hx: x = 0
    . simp[List.remAddZero, hx]
      exact False.elim (hHead hx)
    . simp[hx]

theorem remAddZero_mem (l : List ℕ) (x : ℕ) : x ∈ l.remAddZero → x ∈ l := by
  intro h
  induction l
  case nil => simp_all[List.remAddZero]
  case cons y ys ih =>
    simp[List.remAddZero] at h
    aesop

theorem remAddZero_head (l : List ℕ)
  (h : l.remAddZero.length > 0) :
  l.remAddZero[0] > 0 := by
  induction l
  case nil => simp[List.remAddZero] at h
  case cons x xs ih =>
    simp[List.remAddZero] at h
    by_cases hx: x = 0
    . simp[List.remAddZero, hx]
      apply ih
    . simp[List.remAddZero, hx]
      omega

theorem remAddZero_addZeroes (n: ℕ) (l: List ℕ) :
  (addZeroes n l).remAddZero = l.remAddZero := by
  simp only [addZeroes, List.remAddZero, List.replicate]
  induction n
  case zero => simp
  case succ n ih =>
    rw[List.remAddZero.eq_def]
    simp[List.replicate]
    exact ih

theorem splitAddZero_addZeroes (l : List ℕ):
  addZeroes (l.length - l.remAddZero.length) (l.remAddZero) = l := by
  nth_rw 4 [← splitAddZero_append l]
  rw[splitAddZero_right, splitAddZero_left_replicate]
  simp[addZeroes, List.replicate]
  rw[← splitAddZero_right]
  have: l = l.splitAddZero.1 ++ l.splitAddZero.2 := by
    rw[splitAddZero_append]
  nth_rw 1 [this]
  simp


theorem toBase_ofBase'' (b: ℕ) (l: List ℕ) (hb: 1 < b) (hlb : ∀ x ∈ l, x < b) :
  (toBase b (ofBase b l)) = l.remAddZero := by
  nth_rw 1 [← splitAddZero_addZeroes l]
  simp[ofBase_addZeroes, remAddZero_addZeroes]
  by_cases h: l.remAddZero.length = 0
  . simp_all[ofBase, toBase]
  . have := remAddZero_head l (by omega)
    apply toBase_ofBase'
    . exact hb
    . intro x hx
      apply hlb
      apply remAddZero_mem
      exact hx
    . exact this

-- theorem toBase_ofBase (b: ℕ) (l: List ℕ) (hb: 1 < b) (hlb : ∀ x ∈ l, x < b) :
--   ∃ k, addZeroes k (toBase b (ofBase b l)) = l := by
--   use (l.length - l.remAddZero.length)
--   rw[toBase_ofBase'' b l hb hlb]
--   exact splitAddZero_addZeroes l

theorem toBase_ofBase (b: ℕ) (l: List ℕ) (hb: 1 < b) (hlb : ∀ x ∈ l, x < b) :
  addZeroes (l.length - l.remAddZero.length) (toBase b (ofBase b l)) = l := by
  rw[toBase_ofBase'' b l hb hlb]
  exact splitAddZero_addZeroes l

def maxLen : (l: List (List α)) → ℕ
  | [] => 0
  | x :: xs => max x.length (maxLen xs)

theorem maxLen_exist (l: List (List α)) (hl: l.length > 0) :
  ∃ x ∈ l, maxLen l = x.length := by
  induction l
  case nil => simp at hl
  case cons x xs ih =>
    by_cases h: xs.length = 0
    . rw[h] at ih
      use x
      constructor
      . simp
      . simp[maxLen]
        have : xs = [] := by
          exact List.eq_nil_of_length_eq_zero h
        simp_all[maxLen]
    . have : xs.length > 0 := by omega
      specialize ih this
      rcases ih with ⟨y, hy, hlen⟩
      have h1: maxLen (x :: xs) = max x.length y.length := by
        simp only [maxLen]
        rw[hlen]
      by_cases h2: x.length ≥ y.length
      . use x
        constructor
        . simp
        . simp[h1, h2]
      . use y
        constructor
        . exact List.mem_cons_of_mem x hy
        . simp only [h1, sup_eq_right]
          omega

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

theorem maxLen_replicate (n: ℕ) (x: List α) :
  maxLen (List.replicate (n+1) x) = x.length := by
  induction n
  case zero =>
    simp[List.replicate, maxLen]
  case succ n ih =>
    simp[List.replicate, maxLen]
    rw[← ih, List.replicate, maxLen]
    exact Nat.le_max_right x.length (maxLen (List.replicate n x))

def maxLenFin (v: (Fin m → List ℕ)) : ℕ :=
  maxLen (List.ofFn v)

theorem len_le_maxLenFin (v: (Fin m → List ℕ)) (i: Fin m) :
  (v i).length ≤ maxLenFin v := by
  apply len_le_maxLen
  refine (List.mem_ofFn v (v i)).mpr ?_
  exact Set.mem_range_self i

theorem maxLenFin_exist (v: (Fin m → List ℕ)) (hm: m > 0) :
  ∃ i, (v i).length = maxLenFin v := by
  have := maxLen_exist (List.ofFn v) (by simp; omega)
  rcases this with ⟨x, hx, hlen⟩
  have := (List.mem_ofFn v x).mp hx
  rcases this with ⟨i, hi⟩
  use i
  rw[hi, ← hlen, maxLenFin]

theorem maxLenFin_le (v: (Fin m → List ℕ)) (n: ℕ) :
  (∀ i, (v i).length ≤ n) → maxLenFin v ≤ n := by
  intro h
  by_cases hm: m > 0
  . rcases maxLenFin_exist v hm with ⟨i, hi⟩
    rw[← hi]
    exact h i
  . have : m = 0 := by omega
    have : List.ofFn v = [] := by
      aesop
    rw[maxLenFin, this, maxLen]
    omega

def mapToBase (b: ℕ) (v : Fin m → ℕ) : Fin m → List ℕ :=
  fun i => toBase b (v i)

theorem mapToBase_lt_base (b: ℕ) (v : Fin m → ℕ) (hb: b > 1) (i : Fin m) :
  ∀ x ∈ (mapToBase b v) i, x < b  := by
  intro x h
  simp only [mapToBase] at h
  apply toBase_lt_base
  omega
  exact h

def stretchLen (ls: Fin m → (List ℕ)) : Fin m → (List ℕ) :=
  fun i => addZeroes (maxLenFin ls - (ls i).length) (ls i)

theorem stretchLen_uniform (ls: Fin m → (List ℕ)) (i : Fin m) :
  (stretchLen ls i).length = maxLenFin ls:= by
  simp only [stretchLen, addZeroes, List.length_append, List.length_replicate]
  have := len_le_maxLenFin ls i
  omega

theorem stretchLen_of_mapToBase_lt_base (b: ℕ) (v: Fin m → ℕ) (hb: b > 1) (i : Fin m) :
  ∀ x ∈ (stretchLen (mapToBase b v)) i, x < b := by
  intro x h
  simp only [stretchLen, addZeroes] at h
  have h1 := addZeroes_elem h
  rcases h1 with (rfl | h1)
  . omega
  apply mapToBase_lt_base
  . exact hb
  . exact h1

theorem zipTailHlb (ls: Fin m → (List ℕ)) (hlb: ∀ i, ∀ x ∈ ls i, x < b) :
  ∀ i, ∀ x ∈ (ls i).tail, x < b := by
  intro i x h
  specialize hlb i
  apply hlb
  . apply List.mem_of_mem_tail h

theorem zipTailHls (ls: Fin m → (List ℕ)) (hls : ∀ i, (ls i).length = l + 1) :
  ∀ i, (ls i).tail.length = l := by
  intro i
  have h := List.length_tail (ls i)
  rw[hls] at h
  exact h

def zip (ls: Fin m → (List ℕ)) (hlb: ∀ i, ∀ x ∈ ls i, x < (b + 2)) (hls : ∀ i, (ls i).length = l) : List (Fin m → Fin (b + 2))  :=
  match l with
  | 0 => []
  | m+1 =>
     (fun i =>
       have : 0 < (ls i).length := by
         rw[hls]
         omega
       ⟨(ls i)[0], by apply hlb; exact List.getElem_mem this⟩) :: (zip (fun i => (ls i).tail)
        (by apply zipTailHlb; exact hlb)
        (by apply zipTailHls; exact hls))

theorem zip_cons (ls: Fin m → (List ℕ)) (hlb: ∀ i, ∀ x ∈ ls i, x < (b + 2)) (hls : ∀ i, (ls i).length = l + 1) :
  zip ls hlb hls = (fun i => ⟨(ls i)[0]'(by specialize hls i; omega), by apply hlb; exact List.getElem_mem (by rw[hls]; omega)⟩) :: zip (fun i => (ls i).tail)
    (by apply zipTailHlb; exact hlb)
    (by apply zipTailHls; exact hls) := by
  simp[zip]

theorem zip_nil (ls: Fin m → (List ℕ)) (hlb: ∀ i, ∀ x ∈ ls i, x < (b + 2)) (hls : ∀ i, (ls i).length = 0) :
  zip ls hlb hls = [] := by
  simp[zip]

theorem padZeros_zip (ls: Fin m → (List ℕ)) (hlb: ∀ i, ∀ x ∈ ls i, x < (b + 2)) (hls : ∀ i, (ls i).length = l) :
  padZeros k (zip ls hlb hls) = @zip m b (l+k) (fun i => (addZeroes k) (ls i)) (by
    intro i x hx
    simp only at hx
    rcases addZeroes_elem hx
    . omega
    . apply hlb
      assumption
  ) (by
    intro i
    simp only
    rw[addZeroesLength]
    specialize hls i
    omega
  ) := by
  induction k
  case zero => simp[padZeros, addZeroes]
  case succ k ih =>
    simp_rw[addZeroes_succ, padZeros_succ]
    simp only [zip, List.getElem_cons_zero, Fin.zero_eta, Nat.add_eq, List.tail_cons, List.cons.injEq, true_and]
    exact ih

def toWord (v: Fin m → ℕ) (b: ℕ) : List (Fin m → Fin (b + 2)) :=
  zip (stretchLen (mapToBase (b + 2) v)) (by
    apply stretchLen_of_mapToBase_lt_base
    omega
  ) (by
    intro i
    apply stretchLen_uniform
  )

/-- Hello, Aeacus! -/
def getDigits {b : ℕ} (ls : List (Fin m → Fin (b + 2))) : Fin m → List ℕ :=
  fun i => List.map (fun f => f i) ls

theorem getDigits_uniform (ls : List (Fin m → Fin (b + 2))) (i : Fin m) :
  (getDigits ls i).length = ls.length := by
  simp only [getDigits, List.length_map]

theorem getDigits_lt_base (ls : List (Fin m → Fin (b + 2))) (i : Fin m) :
  ∀ x ∈ getDigits ls i, x < b + 2 := by
  intro x h
  simp only [getDigits, List.mem_map] at h
  rcases h with ⟨f, hf, rfl⟩
  exact (f i).isLt

theorem getDigits_of_nil (i : Fin m) :
  @getDigits m b [] i = [] := by
  simp[getDigits]

theorem getDigits_of_zip' (ls: Fin m → (List ℕ)) (hlb: ∀ i, ∀ x ∈ ls i, x < (b + 2)) (hls : ∀ i, (ls i).length = (l + 1)) :
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

theorem getDigits_of_zip (ls: Fin m → (List ℕ)) (hlb: ∀ i, ∀ x ∈ ls i, x < (b + 2)) (hls : ∀ i, (ls i).length = l) :
  getDigits (zip ls hlb hls) = ls := by
  induction l generalizing ls with
  | zero =>
    simp only [zip]
    funext i
    rw[getDigits_of_nil]
    simp_all only [List.length_eq_zero]
  | succ l ih =>
    exact getDigits_of_zip' ls hlb hls

theorem zip_of_getDigits (ls: List (Fin m → Fin (b + 2))) :
  ls = @zip m b ls.length (getDigits ls) (fun i x a ↦ getDigits_lt_base ls i x a) (fun i ↦ getDigits_uniform ls i) := by
  induction ls with
  | nil => simp[zip]
  | cons head tail ih =>
    simp[zip, getDigits]
    nth_rw 1 [ih]
    congr

theorem getDigits_length (ls : List (Fin m → Fin (b + 2))) (i : Fin m) : (getDigits ls i).length = ls.length := by
  simp only [getDigits, List.length_map]

def toNat_aux (b : ℕ) (Digits : Fin m → List ℕ) : Fin m → ℕ :=
  fun i => ofBase (b + 2) (Digits i)

theorem toNat_aux_of_nil (b: ℕ) : @toNat_aux m b (fun _ => []) = fun _ => 0 := by

  funext i
  simp[toNat_aux, ofBase]

theorem toNat_aux_of_mapToBase (b: ℕ) (v: Fin m → ℕ) :
  toNat_aux b (mapToBase (b + 2) v) = v := by
  funext i
  simp[toNat_aux, mapToBase, ofBase_toBase]

theorem toNat_aux_of_stretchLen (b: ℕ) (v: Fin m → ℕ) :
  toNat_aux b (stretchLen (mapToBase (b + 2) v)) = v := by
  funext i
  simp[toNat_aux, stretchLen, ofBase_addZeroes, ofBase_toBase, mapToBase]

def toNat (ls : List (Fin m → Fin (b + 2))) : Fin m → ℕ :=
  toNat_aux b (getDigits ls)

theorem length_aux (ls : List (Fin m → Fin (b + 2))) (i : Fin m) :
  ((mapToBase (b + 2) (toNat_aux b (getDigits ls))) i) = (getDigits ls i).remAddZero := by
  simp only [mapToBase, toNat_aux, getDigits]
  rw[toBase_ofBase'' (b+2) (List.map (fun f ↦ ↑(f i)) ls) (by omega) (by exact fun x a ↦getDigits_lt_base ls i x a)]

theorem toWord_toNat' (ls : List (Fin m → Fin (b + 2))) (hLen: ls.length > 0) (hHead : ls[0] ≠ fun _ => 0) :
  ls = toWord (toNat ls) b := by
  simp only [toWord, toNat]
  have hi : ∃ i : Fin m, ls[0] i ≠ 0 := by
    exact Function.ne_iff.mp hHead
  have length : ls.length = maxLenFin (mapToBase (b + 2) (toNat_aux b (getDigits ls))) := by
    rcases hi with ⟨i, hi⟩
    rw[← getDigits_length ls i]
    apply le_antisymm
    . have := len_le_maxLenFin (mapToBase (b + 2) (toNat_aux b (getDigits ls))) i
      apply le_trans
      swap
      exact this
      simp[mapToBase, toNat_aux]
      rw[toBase_ofBase'' (b+2) (getDigits ls i) (by omega) (by exact fun x a ↦getDigits_lt_base ls i x a)]
      rw[remAddZero_nonZero (getDigits ls i) (by rw[getDigits_length]; assumption) (by
      simp only [getDigits, List.getElem_map, ne_eq];
      contrapose! hi
      exact Fin.eq_of_val_eq (hi))]
    . apply maxLenFin_le
      intro i'
      rw[mapToBase, toNat_aux, toBase_ofBase'' (b + 2) (getDigits ls i') (by omega) (by exact fun x a ↦ getDigits_lt_base ls i' x a)]
      have : (getDigits ls i').length = (getDigits ls i).length := by
        rw[getDigits_length ls i']
        rw[getDigits_length ls i]
      rw[← this]
      exact remAddZero.length (getDigits ls i')
  have : (stretchLen (mapToBase (b + 2) (toNat_aux b (getDigits ls)))) = (getDigits ls) := by
      funext i
      simp[getDigits, stretchLen, toNat_aux, mapToBase]
      rw[toBase_ofBase'' (b+2) (List.map (fun f ↦ ↑(f i)) ls) (by omega) (by exact fun x a ↦getDigits_lt_base ls i x a)]
      nth_rw 3 [← toBase_ofBase (b + 2) (List.map (fun f ↦ ↑(f i)) ls) (by omega) (by exact fun x a ↦getDigits_lt_base ls i x a)]
      congr
      swap
      rw[toBase_ofBase'' (b+2) (List.map (fun f ↦ ↑(f i)) ls) (by omega) (by exact fun x a ↦getDigits_lt_base ls i x a)]
      rw[← length]
      simp only [List.length_map]
  simp_rw[this]
  nth_rw 1 [zip_of_getDigits ls]
  congr

def List.splitLeadZeros (ls : List (Fin m → Fin (b + 2)))  : List (Fin m → Fin (b + 2)) × List (Fin m → Fin (b + 2)) :=
  match ls with
  | [] => ([], [])
  | x :: xs =>
    if x = fun _ => 0 then let ⟨ys, zs⟩ := splitLeadZeros xs
      ⟨x :: ys, zs⟩ else ⟨[], ls⟩

theorem List.splitLeadZeros_append (ls : List (Fin m → Fin (b + 2))) :
  let ⟨ys, zs⟩ := ls.splitLeadZeros; ys ++ zs = ls := by
  induction ls
  case nil => simp[List.splitLeadZeros]
  case cons x xs ih =>
    simp[List.splitLeadZeros]
    by_cases hx: x = fun _ => 0
    . simp only [hx, ↓reduceIte, List.cons_append, List.cons.injEq, true_and]
      rw[ih]
    . simp[List.splitLeadZeros, hx]

theorem splitLeadZeros_left (ls : List (Fin m → Fin (b + 2))) :
  let ⟨ys, _⟩ := ls.splitLeadZeros; ∀ x ∈ ys, x = fun _ => 0 := by
  induction ls
  case nil => simp[List.splitLeadZeros]
  case cons x xs ih =>
    simp[List.splitLeadZeros]
    by_cases hx: x = fun _ => 0
    . simp only [hx, ↓reduceIte, List.mem_cons, forall_eq_or_imp, true_and]
      exact ih
    . simp[List.splitLeadZeros, hx]

theorem splitLEadZeros_right (ls : List (Fin m → Fin (b + 2))) :
  let ⟨_, zs⟩ := ls.splitLeadZeros; (h: zs.length > 0) →  zs[0] ≠ fun _ => 0 := by
  induction ls
  case nil => simp[List.splitLeadZeros]
  case cons x xs ih =>
    simp[List.splitLeadZeros]
    by_cases hx: x = fun _ => 0
    . simp[List.splitLeadZeros, hx]
      intro h
      subst hx
      simp_all only [gt_iff_lt, ne_eq, forall_true_left, not_false_eq_true]
    . simp[List.splitLeadZeros, hx]

theorem splitLeadZeros_left_replicate (ls : List (Fin m → Fin (b + 2))) :
  let ⟨ys, _⟩ := ls.splitLeadZeros; ys = List.replicate ys.length (fun _ => 0) := by
  induction ls
  case nil => simp[List.splitLeadZeros]
  case cons x xs ih =>
    simp[List.splitLeadZeros]
    by_cases hx: x = fun _ => 0
    . simp only [hx, ↓reduceIte, List.length_cons, List.replicate, List.cons.injEq, true_and]
      exact ih
    . simp[List.splitLeadZeros, hx]

theorem splitLeadZeros_padZeros (ls : List (Fin m → Fin (b + 2))) :
  let ⟨ys, xs⟩ := ls.splitLeadZeros; ls = padZeros ys.length xs := by
  induction ls
  case nil => simp[List.splitLeadZeros, padZeros]
  case cons x xs ih =>
    simp[List.splitLeadZeros]
    by_cases hx: x = fun _ => 0
    . simp[hx, padZeros, List.replicate]
      exact ih
    . simp[hx, padZeros]

theorem toWord_toNat_aux (ls : List (Fin m → Fin (b + 2))) :
  ls = padZeros ls.splitLeadZeros.1.length (toWord (toNat ls.splitLeadZeros.2) b) := by
  nth_rw 1 [splitLeadZeros_padZeros ls]
  congr
  by_cases h : ls.splitLeadZeros.2.length = 0
  . simp_all[toWord, toNat, padZeros, List.length_nil]
    have : (@toNat_aux m b (@getDigits m b [])) = fun _ => 0 := by
      apply toNat_aux_of_nil
    simp only [this]
    have: @mapToBase m (b + 2) (fun x ↦ 0) = fun x ↦ [] := by
      funext i
      simp[mapToBase, toBase]
    simp only [this]
    have : @stretchLen m (fun x ↦ []) = fun x ↦ [] := by
      funext i
      simp[stretchLen, addZeroes, maxLenFin]
      induction m with
      | zero =>
        have := i.2
        contradiction
      | succ m ih =>
        rw[maxLen_replicate]
        rfl
    simp only [this]
    have := @zip_nil m b (fun x ↦ []) (by
      intro i x h
      simp_all
    ) (by simp)
    simp_rw[← this]
    congr
    simp only [maxLenFin, List.ofFn_const]
    induction m with
    | zero => simp[maxLen]
    | succ m ih =>
      rw[maxLen_replicate]
      rfl
  . have len : ls.splitLeadZeros.2.length > 0 := by omega
    have : ls.splitLeadZeros.2[0] ≠ fun _ => 0 := by
      apply splitLEadZeros_right
    exact toWord_toNat' ls.splitLeadZeros.2 len this

theorem toWord_toNat_exist (ls : List (Fin m → Fin (b + 2))) :
  ∃ k, ls = padZeros k (toWord (toNat ls) b) := by
  use ls.splitLeadZeros.1.length
  have := toWord_toNat_aux ls
  nth_rw 1 [this]
  congr
  rw[toNat, toNat]
  nth_rw 2 [← ls.splitLeadZeros_append]
  rw[splitLeadZeros_left_replicate]
  ext i
  simp[toNat_aux, getDigits]
  rw[← addZeroes]
  exact
    Eq.symm
      (ofBase_addZeroes (b + 2) ls.splitLeadZeros.1.length
        (List.map (fun f ↦ ↑(f i)) ls.splitLeadZeros.2))

theorem toNat_toWord (v: Fin m → ℕ) (b: ℕ) :
  toNat (toWord v b) = v := by
  simp[toNat, toNat_aux, getDigits, toWord, zip, stretchLen, addZeroes, mapToBase, toBase]
  have : (getDigits (zip (stretchLen (mapToBase (b + 2) v)) (stretchLen_of_mapToBase_lt_base (b + 2) v (by omega)) (stretchLen_uniform (mapToBase (b + 2) v))) = stretchLen (mapToBase (b + 2) v)) := by

    have : ∀ (i : Fin m), ∀ x ∈ stretchLen (mapToBase (b + 2) v) i, x < b + 2 := by
      apply stretchLen_of_mapToBase_lt_base
      omega
    let l := maxLenFin (mapToBase (b + 2) v)
    convert getDigits_of_zip (l := l) (stretchLen (mapToBase (b + 2) v)) this ?_
  rw[this]
  exact toNat_aux_of_stretchLen b v
