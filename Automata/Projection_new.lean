import Mathlib.Tactic
import Mathlib.Data.List.Basic
import Mathlib.Data.FinEnum
import Batteries.Data.List.Basic
import Automata.DFA
import Automata.NFA_new
import Automata.Pumping_new
import Automata.Input_new
import Automata.LeadingZeros_new
import Automata.Fin

def project  (dfa : DFA (Fin (n+1) → Fin (b+2)) state) [LinearOrder state] :
  NFA (Fin n → Fin (b+2)) state := {
  transition :=
  fun a q => ⟨⟨(List.map (fun (x : Fin (b+2)) => dfa.transition (Matrix.vecCons x a) q)
    (FinEnum.toList (Fin (b+2)))).dedup.mergeSort, by simp only [List.nodup_mergeSort, List.nodup_dedup]⟩, by apply List.sorted_mergeSort'⟩
  start := ⟨⟨[dfa.start], List.nodup_singleton dfa.start⟩,
    List.sorted_singleton dfa.start⟩
  output := dfa.output
}

-- theorem transition_project' [LinearOrder state](dfa : DFA (Fin (n + 1) → Fin (b+2)) state) (m : Fin (n + 1)) (f : (Fin (n+1) → Fin (b+2))) (p q : state) : dfa.transition f p = q → q ∈ ((project dfa).transition (Matrix.vecTail f) p).val.val := by
--   simp only [project, List.mem_dedup, List.mem_map, FinEnum.mem_toList, true_and]
--   intro h
--   use f m
--   simp[Fin.insertNth, insert_remove]
--   exact h

theorem transition_project [LinearOrder state](dfa : DFA (Fin (n + 1) → Fin (b+2)) state) (f : (Fin (n+1) → Fin (b+2))) (p : state) : dfa.transition f p ∈ ((project dfa).transition (Matrix.vecTail f) p).val.val := by
  simp only [project, List.mem_mergeSort, List.mem_dedup, List.mem_map, FinEnum.mem_toList,
    true_and]
  use Matrix.vecHead f
  simp only [Matrix.cons_head_tail]

theorem transFrom_project [LinearOrder state](dfa : DFA (Fin (n + 1) → Fin (b+2)) state) (l : List (Fin (n+1) → Fin (b+2))) (p q : state) : dfa.transFrom l p = q → q ∈ ((project dfa).transFrom (l.map (fun f => Matrix.vecTail f)) ⟨⟨[p], List.nodup_singleton p⟩, List.sorted_singleton p⟩).val.val := by
  intro h
  induction l generalizing p
  case nil =>
    simp_all only [List.map_nil]
    simp only [DFAO.transFrom] at h
    simp only [NFA.transFrom, List.mem_singleton]
    exact h.symm
  case cons f fs ih =>
    simp[DFAO.transFrom] at h
    simp[NFA.transFrom, NFA.transList]
    specialize ih (dfa.transition f p) h
    have := NFA.transFrom_sublist (ps := ⟨⟨[dfa.transition f p], List.nodup_singleton (dfa.transition f p)⟩, List.sorted_singleton (dfa.transition f p)⟩) (project dfa) (List.map (fun f ↦ Matrix.vecTail f) fs) ⟨⟨(((project dfa).transition (Matrix.vecTail f) p).val.val).dedup.mergeSort, by simp[List.nodup_mergeSort, List.nodup_dedup]⟩, by apply List.sorted_mergeSort'⟩
    apply this
    . simp only [List.cons_subset, List.mem_mergeSort, List.mem_dedup, List.nil_subset, and_true]
      apply transition_project
    . assumption

theorem evalFrom_project [LinearOrder state](dfa : DFA (Fin (n + 1) → Fin (b+2)) state) (l : List (Fin (n+1) → Fin (b+2))) (p : state) : dfa.evalFrom l p → (project dfa).evalFrom (l.map (fun f => Matrix.vecTail f)) ⟨⟨[p], List.nodup_singleton p⟩, List.sorted_singleton p⟩ := by
  simp[NFA.evalFrom, DFAO.evalFrom]
  intro h
  use (DFAO.transFrom dfa l p)
  constructor
  . apply transFrom_project
    rfl
  . simp only [project]
    exact h

theorem eval_project [LinearOrder state](dfa : DFA (Fin (n + 1) → Fin (b+2)) state) (l : List (Fin (n+1) → Fin (b+2))) : dfa.eval l → (project dfa).eval (l.map (fun f => Matrix.vecTail f)) := by
  simp[NFA.eval, DFAO.eval]
  exact evalFrom_project dfa l dfa.start

-- theorem project_transition' [LinearOrder state](dfa : DFA (Fin (n + 1) → Fin (b+2)) state) (m : Fin (n + 1)) (f : (Fin n → Fin (b+2))) (p q : state) : q ∈ ((project dfa).transition f p).val.val → ∃ f₁, f = Matrix.vecTail f₁ ∧ dfa.transition f₁ p = q := by
--   simp only [project, List.mem_dedup, List.mem_map, FinEnum.mem_toList, true_and]
--   intro h
--   rcases h with ⟨a, h'⟩
--   use Matrix.vecCons a f
--   constructor
--   . simp only [Fin.insertNth, remove_insert]
--   . exact h'

theorem project_transition [LinearOrder state](dfa : DFA (Fin (n + 1) → Fin (b+2)) state) (f : (Fin n → Fin (b+2))) (p q : state) : q ∈ ((project dfa).transition f p).val.val → ∃ a, dfa.transition (Matrix.vecCons a f) p = q := by
  simp[project]

theorem project_transFrom [LinearOrder state](dfa : DFA (Fin (n + 1) → Fin (b+2)) state) (l : List (Fin n → Fin (b+2))) (q : state) (states : ListSND state) : q ∈ ((project dfa).transFrom l states).val.val → ∃ p ∈ states.val.val, ∃ (l₁ : List (Fin (n+1) → Fin (b+2))) , l = l₁.map (Matrix.vecTail) ∧ dfa.transFrom l₁ p = q:= by
  intro h
  induction l generalizing states
  case nil =>
    simp only [NFA.transFrom] at h
    simp_all only [List.nil_eq, List.map_eq_nil_iff, exists_eq_left]
    use q
    simp only [h, DFAO.transFrom, and_self]
  case cons f fs ih =>
    simp [NFA.transFrom] at h
    specialize ih ((project dfa).transList f states)
    specialize ih h
    rcases ih with ⟨p, h₁, l₁, h₂, h₃⟩
    -- Need to obtain a p' ∈ states.val.val from h₁. so p ∈ NFA.transList implies exists p', p  is in transitions.
    have h₄ := NFA.transList_backtrack (project dfa) f p states h₁
    rcases h₄ with ⟨p', h₅, h₆⟩
    use p'
    constructor
    . exact h₅
    . have h₇ := project_transition dfa f p' p h₆
      rcases h₇ with ⟨a, h₈⟩
      use (Matrix.vecCons a f) :: l₁
      constructor
      . simp only [h₂, Nat.succ_eq_add_one, List.map_cons, Matrix.tail_cons]
      . subst h₂ h₃ h₈
        simp_all only [Nat.succ_eq_add_one]
        obtain ⟨val, property⟩ := states
        simp_all only
        rfl

theorem project_evalFrom [LinearOrder state](dfa : DFA (Fin (n + 1) → Fin (b+2)) state) (l : List (Fin n → Fin (b+2))) (states : ListSND state) : (project dfa).evalFrom l states → ∃ p ∈ states.val.val, ∃ (l₁ : List (Fin (n+1) → Fin (b+2))) , l = l₁.map (Matrix.vecTail) ∧ dfa.evalFrom l₁ p:= by
  intro h
  simp_all [NFA.evalFrom, DFAO.evalFrom]
  rcases h with ⟨p, h₁, h₂⟩
  have h₃ := project_transFrom dfa l p states h₁
  rcases h₃ with ⟨p', h₄, h₅, h₆, h₇⟩
  use p'
  constructor
  . exact h₄
  . use h₅
    constructor
    . exact h₆
    . simp only [project] at h₂
      simp only [h₇, h₂]

theorem project_eval [LinearOrder state](dfa : DFA (Fin (n + 1) → Fin (b+2)) state) (l : List (Fin n → Fin (b+2))) : (project dfa).eval l → ∃ (l₁ : List (Fin (n+1) → Fin (b+2))) , l = l₁.map (Matrix.vecTail) ∧ dfa.eval l₁ := by
  simp[NFA.eval, DFAO.eval]
  have h := project_evalFrom dfa l (project dfa).start
  intro h₁
  specialize h h₁
  rcases h with ⟨p, h₂, l', h₄⟩
  simp[project] at h₂
  aesop

theorem project_eval_iff [LinearOrder state](dfa : DFA (Fin (n + 1) → Fin (b+2)) state) (l : List (Fin n → Fin (b+2))) : (project dfa).eval l ↔ ∃ (l₁ : List (Fin (n+1) → Fin (b+2))) , l = l₁.map (Matrix.vecTail) ∧ dfa.eval l₁ := by
  constructor
  . exact project_eval dfa l
  . intro h
    rcases h with ⟨l₁, h₁, h₂⟩
    have h₃ := eval_project dfa l₁ h₂
    subst h₁
    simp_all only [Nat.succ_eq_add_one]


theorem project_acceptZero [LinearOrder state] (dfa : DFA (Fin (n + 1) → Fin (b+2)) state) (h: DFA.acceptZero dfa) : NFA.acceptZero (project dfa) := by
  simp[NFA.acceptZero]
  intro l h'
  have h₁ := project_eval_iff dfa l
  have h₂ := h₁.mp h'
  rcases h₂ with ⟨l₁, h₃, h₄⟩
  rw[DFA.acceptZero] at h
  specialize h l₁ h₄
  intro k
  specialize h k
  have h₅ := project_eval_iff dfa (padZeros k l)
  apply h₅.mpr
  use (padZeros k l₁)
  constructor
  . simp only [padZeros, List.map_append, List.map_replicate]
    have: List.replicate k (Matrix.vecTail (fun _ ↦ 0 : Fin (n+1) → Fin (b+2))) ++ List.map (Matrix.vecTail) l₁ = List.replicate k (fun _ ↦ 0) ++ List.map (Matrix.vecTail) l₁ := by
      simp only [List.append_cancel_right_eq, List.replicate_inj, true_and]
      right
      rfl
    simp only [h₃, this]
  . exact h

theorem project_fix_acceptZero [Fintype state][LinearOrder state] (dfa : DFA (Fin (n + 1) → Fin (b+2)) state) (h: dfa.acceptZero) : (project dfa).fixLeadingZeros.acceptZero := by
  have: (project dfa).acceptZero := project_acceptZero dfa h
  exact NFA.fixLeadingZeroes.acceptZero (project dfa) this

theorem project_fix_respectZero [Fintype state][LinearOrder state] (dfa : DFA (Fin (n + 1) → Fin (b+2)) state) (h: dfa.respectZero) : (project dfa).fixLeadingZeros.respectZero := by
  rw[NFA.respectZero]
  intro l k
  constructor
  . have := project_fix_acceptZero dfa
    have dfa_zero := dfa.acceptZero_of_respectZero h
    have := this dfa_zero
    rw[NFA.acceptZero] at this
    intro a
    simp_all only [true_implies]
  . intro h'
    rw[NFA.fixLeadingZeros_eval, padZeros_add] at h'
    have dfa_zero := dfa.acceptZero_of_respectZero h
    have := project_acceptZero dfa dfa_zero
    have := (project dfa).bounded_accept l this (padZeros (Fintype.card (ListSND state) + k) l)
    rw[NFA.fixLeadingZeros_eval]
    apply this
    constructor
    . use (Fintype.card (ListSND state) + k)
    . exact h'

theorem project_fix_toDFA_respectZero [Fintype state][LinearOrder state] (dfa : DFA (Fin (n + 1) → Fin (b+2)) state) (h: dfa.respectZero) : (project dfa).fixLeadingZeros.toDFA.respectZero := by
  have := project_fix_respectZero dfa h
  intro v m
  rw[NFA.toDFA_eval, NFA.toDFA_eval]
  exact this v m

theorem word_project_aux' (b : ℕ) (ls : Fin (m+1) → List ℕ) (hls : ∀ i, (ls i).length = l) (hlb: ∀ i, ∀ x ∈ ls i, x < b+2) : (List.map (fun f ↦ Matrix.vecTail f) (zip ls hlb hls)) = zip (Matrix.vecTail (ls)) (by
    intro j x hx
    simp only [Matrix.vecTail, Nat.succ_eq_add_one, Function.comp_apply] at hx
    apply hlb
    exact hx
  ) (by
    intro i
    apply hls
  ):= by
  induction' l with l ih generalizing ls
  .
    have : ls = fun j ↦ [] := by
      funext j
      exact List.length_eq_zero_iff.mp (hls j)
    simp_all only [zip_nil, List.map_nil]
  . simp only [Nat.succ_eq_add_one, zip, List.map_cons, List.cons.injEq]
    constructor
    swap
    . have hls' : ∀ i, ((fun j => (ls j).tail) i).length = l:= by
        exact fun i ↦ zipTailHls ls hls i
      specialize ih (fun j => (ls j).tail) hls'
      have hlb' : ∀ i, ∀ x ∈ (ls i).tail, x < b+2 := by
        intro i x hx
        simp only at hx
        apply hlb
        exact List.mem_of_mem_tail hx
      specialize ih hlb'
      exact ih
    . simp only [Matrix.vecTail, Nat.succ_eq_add_one, Function.comp_apply]
      constructor

theorem word_project_aux (x b : ℕ) (v : Fin m → ℕ)  : (List.map (fun f ↦ Matrix.vecTail f) (toWord (Matrix.vecCons x v) b)) = zip (Matrix.vecTail (stretchLen (mapToBase (b + 2) (Matrix.vecCons x v)))) (by
    intro j
    apply stretchLen_of_mapToBase_lt_base
    norm_num
  ) (by
    intro i
    apply stretchLen_uniform
  ):= by
  simp only [toWord]
  apply word_project_aux'

theorem maxLenFin_cons (x b : ℕ)  (v : Fin m → ℕ): maxLenFin (mapToBase (b + 2) v) ≤ maxLenFin (mapToBase (b + 2) (Matrix.vecCons x v)) := by
  apply maxLenFin_le
  intro j
  rw[maxLenFin]
  apply len_le_maxLen
  simp only [List.mem_ofFn, mapToBase]
  use ⟨j+1, by omega⟩
  simp


theorem word_project (x b : ℕ)  (v : Fin m → ℕ) : ∃ k, (List.map (fun f ↦ Matrix.vecTail f) (toWord (Matrix.vecCons x v) b)) = padZeros k (toWord v b) := by
  use maxLenFin (mapToBase (b + 2) (Matrix.vecCons x v)) - maxLenFin (mapToBase (b + 2) v)
  rw[word_project_aux, toWord]
  rw[padZeros_zip]
  have len := maxLenFin_cons x b v
  congr
  . omega
  . funext j
    simp[stretchLen, addZeroes_addZeroes]
    have := len_le_maxLenFin (mapToBase (b + 2) v) j
    have : (maxLenFin (mapToBase (b + 2) (Matrix.vecCons x v)) - maxLenFin (mapToBase (b + 2) v) +
      (maxLenFin (mapToBase (b + 2) v) - (mapToBase (b + 2) v j).length)) = maxLenFin (mapToBase (b + 2) (Matrix.vecCons x v)) - (mapToBase (b + 2) v j).length := by omega
    rw[this]
    congr

theorem correct_project [Fintype state] [LinearOrder state] (v : Fin l → ℕ) (dfa : DFA (Fin (l+1) → Fin (b+2)) state) (hres: dfa.respectZero):
  (∃ (x : ℕ), dfa.eval (toWord (Matrix.vecCons x v) b)) → (project dfa).fixLeadingZeros.eval (toWord v b) := by
  rw[NFA.fixLeadingZeros_eval]
  intro h
  rcases h with ⟨x, h⟩
  have := eval_project dfa (toWord (Matrix.vecCons x v) b) h

  have lis := word_project x b v
  rcases lis with ⟨k, h₁⟩
  rw[h₁] at this
  apply (project dfa).bounded_accept _
  .
    apply project_acceptZero dfa

    exact DFA.acceptZero_of_respectZero dfa hres

  swap
  . exact padZeros k (toWord v b)
  . constructor
    . use k
    . exact this

theorem project_word (w: List (Fin (l+1) → Fin (b+2))) : (toNat (List.map (Matrix.vecTail) w)) = Matrix.vecTail (toNat w) := by
  funext j
  simp only [toNat, toNat_aux, getDigits, Nat.succ_eq_add_one, List.map_map]
  rfl

theorem project_correct [Fintype state] [LinearOrder state] (v : Fin l → ℕ) (dfa : DFA (Fin (l+1) → Fin (b+2)) state) (hres: dfa.respectZero):
  (project dfa).fixLeadingZeros.eval (toWord v b) → (∃ (x : ℕ), dfa.eval (toWord (Matrix.vecCons x v) b)) := by
  intro h
  rw[NFA.fixLeadingZeros_eval] at h
  rw[project_eval_iff] at h
  rcases h with ⟨w, hlis, hdfa⟩
  have : dfa.eval (toWord (toNat w) b) := by
    have := toWord_toNat_exist w
    rcases this with ⟨k, h⟩
    rw[h] at hdfa
    rw[DFA.respectZero] at hres
    specialize hres (toWord (toNat w) b) k
    apply hres.mpr
    exact hdfa
  use Matrix.vecHead (toNat w)
  have htoNat: toNat (padZeros (Fintype.card (ListSND state)) (toWord v b)) = toNat (List.map (Matrix.vecTail) w) := by
    rw[hlis]
  simp only [toNat, toWord, padZeros_zip, stretchLen, addZeroes_addZeroes,
    getDigits_of_zip] at htoNat
  have htoNatAddZero : (toNat_aux b fun i => addZeroes (Fintype.card (ListSND state) + (maxLenFin (mapToBase (b + 2) v) - (mapToBase (b + 2) v i).length)) (mapToBase (b + 2) v i)) = v := by
    funext i
    simp only [toNat_aux, mapToBase, ofBase_addZeroes, ofBase_toBase]
  rw[htoNatAddZero, ← toNat] at htoNat
  clear htoNatAddZero
  have h₁ : (Matrix.vecCons (Matrix.vecHead (toNat w)) v) = toNat w := by
    funext j
    rw[htoNat, project_word]
    simp only [Nat.succ_eq_add_one, Matrix.cons_head_tail]
  simp_rw[h₁]
  exact this

theorem project_iff [Fintype state] [LinearOrder state] (v : Fin l → ℕ) (dfa : DFA (Fin (l+1) → Fin (b+2)) state) (hres: dfa.respectZero):
  (project dfa).fixLeadingZeros.toDFA.eval (toWord v b) ↔ (∃ (x : ℕ), dfa.eval (toWord (Matrix.vecCons x v) b)) := by
  constructor
  . intro h
    apply project_correct
    . exact hres
    . rw[← NFA.toDFA_eval]
      exact h
  . intro h
    have := correct_project v dfa hres h
    rwa [NFA.toDFA_eval]
