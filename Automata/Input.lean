import Mathlib.Tactic
import Mathlib.Data.List.Basic
import Mathlib.Data.List.Lemmas
import Mathlib.Data.Nat.Digits
import Init.Data.List.Lemmas
import Automata.Replicate
import Automata.LeadingZeros

/-
Major function: inputToBase

Idea: Given a list of natural numbers 'l',

Step 1: Convert each number to base b, get 'ls' : List (List ℕ)

Functions involved: toBase, mapToBase
Theorems involved: digits_end_nonzero, toBase_lead_nonzero,
toBase_lt_base, mapToBase_lt_base, mapToBase_length

Step 2: Stretch each list to uniform length by adding leading zeros, get 'lss' : List (List ℕ)

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
  . simp at hnb
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
  l.foldl (fun x y => x * b + y) 0

theorem ofBase_toBase (b: ℕ) (n: ℕ) : ofBase b (toBase b n) = n := by
  simp only [toBase, ofBase, List.foldl_reverse, add_comm, mul_comm]
  have h: Nat.ofDigits b (b.digits n) = n := Nat.ofDigits_digits b n
  nth_rewrite 2 [← h]
  rw [Nat.ofDigits_eq_foldr]
  rfl

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

theorem ofBase_addZeroes (b: ℕ)(n: ℕ) (l: List ℕ) :
  ofBase b (addZeroes n l) = ofBase b l := by
  simp only [ofBase, addZeroes]
  induction n
  case zero => simp
  case succ n ih =>
    simp [addZeroes, List.replicate, List.foldl, ih]

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

def mapToBase (b: ℕ) (l: List ℕ) : List (List ℕ) :=
  l.map (toBase b)

theorem mapToBase_lt_base (b: ℕ) (l: List ℕ) (hb: b > 1) :
  ∀ x ∈ (mapToBase b l), ∀ y ∈ x, y < b  := by
  intro x hx y hy
  simp only [mapToBase, List.mem_map] at hx
  rcases hx with ⟨z, _, rfl⟩
  apply toBase_lt_base
  exact hb
  exact hy

theorem mapToBase_length (b: ℕ) (l: List ℕ) : (mapToBase b l).length = l.length := by
  simp only [mapToBase, List.length_map]

def stretchLen (ls: List (List ℕ)) : List (List ℕ) :=
  ls.map (fun l => addZeroes (maxLen ls - l.length) l)

theorem stretchLen_length (ls: List (List ℕ)) : (stretchLen ls).length = ls.length := by
  simp only [stretchLen, List.length_map]

theorem stretchLen_uniform (ls: List (List ℕ)) :
  ∀ l ∈ stretchLen ls,  l.length = maxLen ls:= by
  intro l h
  simp only [stretchLen, List.mem_map] at h
  rcases h with ⟨x, hx, rfl⟩
  simp only [addZeroesLength]
  have: x.length ≤ maxLen ls := len_le_maxLen x ls hx
  omega

theorem stretchLen_of_mapToBase_lt_base (b: ℕ) (l: List ℕ) (hb: b > 1) :
  ∀ x ∈ (stretchLen (mapToBase b l)), ∀ y ∈ x, y < b := by
  intro x hx y hy
  simp only [stretchLen, List.mem_map] at hx
  rcases hx with ⟨z, left, rfl⟩
  have h := addZeroes_elem hy
  rcases h with (rfl | h)
  . omega
  apply mapToBase_lt_base
  . exact hb
  . simp only [addZeroes, List.replicate] at hy
    exact left
  . exact h

theorem zipTailHlb (lss: List (List ℕ))
(hlb: ∀ x ∈ lss, ∀ y ∈ x, y < b): ∀ x ∈ List.map (fun ls ↦ ls.tail) lss, ∀ y ∈ x, y < b := by
  intro x hx
  simp only [List.mem_map] at hx
  rcases hx with ⟨s, hs, rfl⟩
  intro y hy
  specialize hlb s hs
  apply hlb
  exact List.mem_of_mem_tail hy

theorem zipTailHlss (l : ℕ) (lss: List (List ℕ)) (hlss: lss.length = l)
 : (List.map (fun ls ↦ ls.tail) lss).length = l := by
  simp only [List.length_map, hlss]

theorem zipTailHls (lss: List (List ℕ)) (hls : ∀ ls ∈ lss, ls.length = m + 1) :
∀ ls ∈ List.map (fun ls ↦ ls.tail) lss, ls.length = m
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
      apply List.length_tail x
    rw[← this, h]
    have hxtail := List.length_tail x.tail
    rw[h, List.tail] at hxtail
    have: (head :: tail).length > 0 := by simp
    omega

def zipToAlphabetFin (n : ℕ) (l : ℕ) (lss: List (List ℕ))
(hlb: ∀ x ∈ lss, ∀ y ∈ x, y < b) (hlss: lss.length = l)
(hls : ∀ ls ∈ lss, ls.length = n) : List (Fin l → Fin b) :=
  match n with
  | 0 => []
  | m+1 =>
     (fun i =>
      -- prove index valid
       have : 0 < lss[i].length := by
         rw[hls]
         omega
         refine List.mem_iff_get.mpr ?_
         subst hlss
         use i
         rfl

       ⟨lss[i][0], (by
       -- giving Fin b proof
          apply hlb lss[i]
          . apply List.mem_iff_getElem.mpr
            simp only [Fin.getElem_fin, hlss]
            use i, i.isLt
          . apply List.mem_iff_getElem.mpr
            use 0, this)⟩
        ) :: (zipToAlphabetFin m l (lss.map (fun ls => ls.tail))
        (by apply zipTailHlb; exact hlb)
        (by apply zipTailHlss; exact hlss)
        (by apply zipTailHls; exact hls))

-- def zipToAlphabetByFin (n : ℕ) (l : ℕ) (lss: List (List ℕ))
-- (hlb: ∀ x ∈ lss, ∀ y ∈ x, y < b) (hlss: lss.length = l)
-- (hls : ∀ ls ∈ lss, ls.length = n) : List (Fin l → Fin b) :=
--   match n with
--   | 0 => []
--   | m+1 =>
--      (fun i =>
--       -- prove index valid
--        have : 0 < lss[i].length := by
--          rw[hls]
--          omega
--          refine List.mem_iff_get.mpr ?_
--          subst hlss
--          use i
--          rfl

--        ⟨lss[i][0], (by
--        -- giving Fin b proof
--           apply hlb lss[i]
--           . apply List.mem_iff_getElem.mpr
--             simp only [Fin.getElem_fin, hlss]
--             use i, i.isLt
--           . apply List.mem_iff_getElem.mpr
--             use 0, this)⟩
--         ) :: (zipToAlphabetFin m l (lss.map (fun ls => ls.tail))
--         (by apply zipTailHlb; exact hlb)
--         (by apply zipTailHlss; exact hlss)
--         (by apply zipTailHls; exact hls))

theorem zipToAlphabetFin_length (n : ℕ) (l : ℕ) (lss: List (List ℕ))
(hlb: ∀ x ∈ lss, ∀ y ∈ x, y < b) (hlss: lss.length = l)
(hls : ∀ ls ∈ lss, ls.length = n) :
  (zipToAlphabetFin n l lss hlb hlss hls).length = n := by
  induction n generalizing l lss
  case zero =>
    simp only [List.length_eq_zero, zipToAlphabetFin]
  case succ n ih =>
    simp only [zipToAlphabetFin, add_left_inj, List.length_cons]
    apply ih

def inputToBase (b : ℕ) (hb: b > 1) (l: List ℕ) (hm : l.length = m) : List (Fin m → Fin b) :=
  let ls := mapToBase b l
  let n := maxLen ls
  let lss := stretchLen (ls)
  zipToAlphabetFin n m lss (by
    apply stretchLen_of_mapToBase_lt_base
    exact hb
  ) (by simp only [mapToBase_length b l, stretchLen_length ls]; exact hm) (by
    intro ls hls
    apply stretchLen_uniform
    assumption)

def getDigits (lis : List (Fin m → Fin b)) : Fin m → List ℕ :=
  fun i => List.map (fun f => f i) lis

def reverseInput_aux (b : ℕ) (Digits : Fin m → List ℕ) : Fin m → ℕ :=
  fun i => ofBase b (Digits i)

def reverseInput (lis : List (Fin m → Fin b)) : List ℕ :=
  List.ofFn (reverseInput_aux b (getDigits lis))

theorem reverseInput_length (lis : List (Fin m → Fin b)) : (reverseInput lis).length = m := by
  simp only [reverseInput, List.length_ofFn]

theorem inputToBase_of_reverseInput (lis : List (Fin m → Fin (b + 2))) :
  ∃ (k : ℕ), lis = padZeros k (inputToBase (b + 2) (by omega) (reverseInput lis) (reverseInput_length lis)) := by
  sorry

theorem reverseInput_of_inputToBase (b : ℕ) (hb: b > 1) (l: List ℕ) (hm : l.length = m) :
  reverseInput (inputToBase b hb l hm) = l := by
  sorry

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
