import Mathlib.Tactic
import Mathlib.Data.List.Basic
import Batteries.Data.List.Basic
import Mathlib.Data.Nat.Digits
import Automata.DFA
import Automata.NFA
import Automata.Pumping
import Automata.Input
import Automata.LeadingZeros
import Automata.Fin

def project (m : Fin (n+1)) (dfa : DFA (Fin (n+1) → Fin (b+2)) state) [DecidableEq state] :
  NFA (Fin n → Fin (b+2)) state := {
  transition :=
  fun a q => ⟨(List.map (fun (x : Fin (b+2)) => dfa.transition (Fin.insertNth m x a) q)
    (FinEnum.toList (Fin (b+2)))).dedup, by apply List.nodup_dedup⟩
  start := ⟨[dfa.start], List.nodup_singleton dfa.start⟩
  output := dfa.output
}

-- theorem transition_project' [DecidableEq state](dfa : DFA (Fin (n + 1) → Fin (b+2)) state) (m : Fin (n + 1)) (f : (Fin (n+1) → Fin (b+2))) (p q : state) : dfa.transition f p = q → q ∈ ((project m dfa).transition (Fin.removeNth m f) p).val := by
--   simp only [project, List.mem_dedup, List.mem_map, FinEnum.mem_toList, true_and]
--   intro h
--   use f m
--   simp[Fin.insertNth, insert_remove]
--   exact h

theorem transition_project [DecidableEq state](dfa : DFA (Fin (n + 1) → Fin (b+2)) state) (m : Fin (n + 1)) (f : (Fin (n+1) → Fin (b+2))) (p : state) : dfa.transition f p ∈ ((project m dfa).transition (Fin.removeNth m f) p).val := by
  simp only [project, List.mem_dedup, List.mem_map, FinEnum.mem_toList, true_and]
  use f m
  simp[Fin.insertNth, ]

theorem transFrom_project [DecidableEq state](dfa : DFA (Fin (n + 1) → Fin (b+2)) state) (m : Fin (n + 1)) (l : List (Fin (n+1) → Fin (b+2))) (p q : state) : dfa.transFrom l p = q → q ∈ ((project m dfa).transFrom (l.map (fun f => Fin.removeNth m f)) ⟨[p], by exact List.nodup_singleton p⟩).val := by
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
    have := NFA.transFrom_sublist (ps := ⟨[dfa.transition f p], by exact List.nodup_singleton (dfa.transition f p)⟩) (project m dfa) (List.map (fun f ↦ Fin.removeNth m f) fs) ⟨(((project m dfa).transition (Fin.removeNth m f) p).val).dedup, by apply List.nodup_dedup⟩
    apply this
    . simp only [List.cons_subset, List.mem_dedup, List.nil_subset, and_true]
      apply transition_project
    . assumption

theorem evalFrom_project [DecidableEq state](dfa : DFA (Fin (n + 1) → Fin (b+2)) state) (m : Fin (n + 1)) (l : List (Fin (n+1) → Fin (b+2))) (p : state) : dfa.evalFrom l p → (project m dfa).evalFrom (l.map (fun f => Fin.removeNth m f)) ⟨[p], by exact List.nodup_singleton p⟩ := by
  simp[NFA.evalFrom, DFAO.evalFrom]
  intro h
  use (DFAO.transFrom dfa l p)
  constructor
  . apply transFrom_project
    rfl
  . simp only [project]
    exact h

theorem eval_project [DecidableEq state](dfa : DFA (Fin (n + 1) → Fin (b+2)) state) (m : Fin (n + 1)) (l : List (Fin (n+1) → Fin (b+2))) : dfa.eval l → (project m dfa).eval (l.map (fun f => Fin.removeNth m f)) := by
  simp[NFA.eval, DFAO.eval]
  exact evalFrom_project dfa m l dfa.start

-- theorem project_transition' [DecidableEq state](dfa : DFA (Fin (n + 1) → Fin (b+2)) state) (m : Fin (n + 1)) (f : (Fin n → Fin (b+2))) (p q : state) : q ∈ ((project m dfa).transition f p).val → ∃ f₁, f = Fin.removeNth m f₁ ∧ dfa.transition f₁ p = q := by
--   simp only [project, List.mem_dedup, List.mem_map, FinEnum.mem_toList, true_and]
--   intro h
--   rcases h with ⟨a, h'⟩
--   use Fin.insertNth m a f
--   constructor
--   . simp only [Fin.insertNth, remove_insert]
--   . exact h'

theorem project_transition [DecidableEq state](dfa : DFA (Fin (n + 1) → Fin (b+2)) state) (m : Fin (n + 1)) (f : (Fin n → Fin (b+2))) (p q : state) : q ∈ ((project m dfa).transition f p).val → ∃ a, dfa.transition (Fin.insertNth m a f) p = q := by
  simp only [project, List.mem_dedup, List.mem_map, FinEnum.mem_toList, true_and, imp_self]

theorem project_transFrom [DecidableEq state](dfa : DFA (Fin (n + 1) → Fin (b+2)) state) (m : Fin (n + 1)) (l : List (Fin n → Fin (b+2))) (q : state) (states : ListND state) : q ∈ ((project m dfa).transFrom l states).val → ∃ p ∈ states.val, ∃ (l₁ : List (Fin (n+1) → Fin (b+2))) , l = l₁.map (Fin.removeNth m) ∧ dfa.transFrom l₁ p = q:= by
  intro h
  induction l generalizing states
  case nil =>
    simp only [NFA.transFrom, List.mem_singleton] at h
    simp_all only [List.nil_eq, List.map_eq_nil_iff, exists_eq_left]
    use q
    simp only [h, DFAO.transFrom, and_self]
  case cons f fs ih =>
    simp [NFA.transFrom] at h
    specialize ih ((project m dfa).transList f states)
    specialize ih h
    rcases ih with ⟨p, h₁, l₁, h₂, h₃⟩
    -- Need to obtain a p' ∈ states.val from h₁. so p ∈ NFA.transList implies exists p', p  is in transitions.
    have h₄ := NFA.transList_backtrack (project m dfa) f p states h₁
    rcases h₄ with ⟨p', h₅, h₆⟩
    use p'
    constructor
    . exact h₅
    . have h₇ := project_transition dfa m f p' p h₆
      rcases h₇ with ⟨a, h₈⟩
      use (Fin.insertNth m a f) :: l₁
      constructor
      . simp only [List.map_cons, Fin.removeNth_insertNth, List.cons.injEq, true_and]
        simp only [h₂, Fin.removeNth]
      . aesop

theorem project_evalFrom [DecidableEq state](dfa : DFA (Fin (n + 1) → Fin (b+2)) state) (m : Fin (n + 1)) (l : List (Fin n → Fin (b+2))) (states : ListND state) : (project m dfa).evalFrom l states → ∃ p ∈ states.val, ∃ (l₁ : List (Fin (n+1) → Fin (b+2))) , l = l₁.map (Fin.removeNth m) ∧ dfa.evalFrom l₁ p:= by
  intro h
  simp_all [NFA.evalFrom, DFAO.evalFrom]
  rcases h with ⟨p, h₁, h₂⟩
  have h₃ := project_transFrom dfa m l p states h₁
  rcases h₃ with ⟨p', h₄, h₅, h₆, h₇⟩
  use p'
  constructor
  . exact h₄
  . use h₅
    constructor
    . exact h₆
    . simp only [project] at h₂
      simp only [h₇, h₂]

theorem project_eval [DecidableEq state](dfa : DFA (Fin (n + 1) → Fin (b+2)) state) (m : Fin (n + 1)) (l : List (Fin n → Fin (b+2))) : (project m dfa).eval l → ∃ (l₁ : List (Fin (n+1) → Fin (b+2))) , l = l₁.map (Fin.removeNth m) ∧ dfa.eval l₁ := by
  simp[NFA.eval, DFAO.eval]
  have h := project_evalFrom dfa m l (project m dfa).start
  intro h₁
  specialize h h₁
  rcases h with ⟨p, h₂, l', h₄⟩
  simp[project] at h₂
  aesop

theorem project_eval_iff [DecidableEq state](dfa : DFA (Fin (n + 1) → Fin (b+2)) state) (m : Fin (n + 1)) (l : List (Fin n → Fin (b+2))) : (project m dfa).eval l ↔ ∃ (l₁ : List (Fin (n+1) → Fin (b+2))) , l = l₁.map (Fin.removeNth m) ∧ dfa.eval l₁ := by
  constructor
  . exact project_eval dfa m l
  . intro h
    rcases h with ⟨l₁, h₁, h₂⟩
    have h₃ := eval_project dfa m l₁ h₂
    aesop


theorem project_acceptZero [DecidableEq state] (dfa : DFA (Fin (n + 1) → Fin (b+2)) state) (h: DFA.acceptZero dfa) (m : Fin (n + 1)) : NFA.acceptZero (project m dfa) := by
  simp[NFA.acceptZero]
  intro l h'
  have h₁ := project_eval_iff dfa m l
  have h₂ := h₁.mp h'
  rcases h₂ with ⟨l₁, h₃, h₄⟩
  rw[DFA.acceptZero] at h
  specialize h l₁ h₄
  intro k
  specialize h k
  have h₅ := project_eval_iff dfa m (padZeros k l)
  apply h₅.mpr
  use (padZeros k l₁)
  constructor
  . simp only [padZeros, List.map_append, List.map_replicate]
    have: List.replicate k (Fin.removeNth m (fun _ ↦ 0 : Fin (n+1) → Fin (b+2))) ++ List.map (Fin.removeNth m) l₁ = List.replicate k (fun _ ↦ 0) ++ List.map (Fin.removeNth m) l₁ := by
      simp only [List.append_cancel_right_eq, List.replicate_inj, true_and]
      right
      rfl
    simp only [h₃, this]
  . exact h

theorem project_fix_acceptZero [Fintype state][DecidableEq state] (dfa : DFA (Fin (n + 1) → Fin (b+2)) state) (m : Fin (n + 1)) (h: dfa.acceptZero) : (project m dfa).fixLeadingZeros.acceptZero := by
  have: (project m dfa).acceptZero := project_acceptZero dfa h m
  exact NFA.fixLeadingZeroes.acceptZero (project m dfa) this

theorem project_fix_respectZero [Fintype state][DecidableEq state] (dfa : DFA (Fin (n + 1) → Fin (b+2)) state) (m : Fin (n + 1)) (h: dfa.respectZero) : (project m dfa).fixLeadingZeros.respectZero := by
  rw[NFA.respectZero]
  intro l k
  constructor
  . have := project_fix_acceptZero dfa
    have dfa_zero := dfa.acceptZero_of_respectZero h
    have := this m dfa_zero
    rw[NFA.acceptZero] at this
    intro a
    simp_all only [true_implies]
  . intro h'
    rw[NFA.fixLeadingZeros_eval, padZeros_add] at h'
    have dfa_zero := dfa.acceptZero_of_respectZero h
    have := project_acceptZero dfa dfa_zero m
    have := (project m dfa).bounded_accept l this (padZeros (Fintype.card (ListND state) + k) l)
    rw[NFA.fixLeadingZeros_eval]
    apply this
    constructor
    . use (Fintype.card (ListND state) + k)
    . exact h'

theorem word_project_aux' (b : ℕ) (ls : Fin (m+1) → List ℕ) (i : Fin (m + 1)) (hls : ∀ i, (ls i).length = l) (hlb: ∀ i, ∀ x ∈ ls i, x < b+2) : (List.map (fun f ↦ Fin.removeNth i f) (zip ls hlb hls)) = zip (Fin.removeNth i (ls)) (by
    intro j x hx
    simp[Fin.removeNth, Fin.removeNth] at hx
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
      exact List.length_eq_zero.mp (hls j)
    simp_all only [Fin.removeNth, zip_nil, List.map_nil]
  . simp[zip]
    constructor
    swap
    . have hls' : ∀ i, ((fun j => (ls j).tail) i).length = l:= by
        exact fun i ↦ zipTailHls ls hls i
      specialize ih (fun j => (ls j).tail) hls'
      have hlb' : ∀ i, ∀ x ∈ (ls i).tail, x < b+2 := by
        intro i x hx
        simp[Fin.removeNth, Fin.removeNth] at hx
        apply hlb
        exact List.mem_of_mem_tail hx
      specialize ih hlb'
      exact ih
    . simp[Fin.removeNth, Fin.removeNth]
      constructor

theorem word_project_aux (x b : ℕ) (v : Fin m → ℕ) (i : Fin (m + 1)) : (List.map (fun f ↦ Fin.removeNth i f) (toWord (Fin.insertNth i x v) b)) = zip (Fin.removeNth i (stretchLen (mapToBase (b + 2) (Fin.insertNth i x v)))) (by
    intro j
    apply stretchLen_of_mapToBase_lt_base
    norm_num
  ) (by
    intro i
    apply stretchLen_uniform
  ):= by
  simp[toWord]
  exact
    word_project_aux' b (stretchLen (mapToBase (b + 2) (Fin.insertNth i x v))) i
      (toWord.proof_2 (Fin.insertNth i x v) b) (toWord.proof_1 (Fin.insertNth i x v) b)

theorem maxLenFin_recover (x b : ℕ)  (v : Fin m → ℕ) (i : Fin (m + 1)) : maxLenFin (mapToBase (b + 2) v) ≤ maxLenFin (mapToBase (b + 2) (Fin.insertNth i x v)) := by
  apply maxLenFin_le
  intro j
  rw[maxLenFin]
  apply len_le_maxLen
  simp only [List.mem_ofFn, mapToBase]
  by_cases h: j.val < i.val
  . use j
    congr
    simp only [Fin.insertNth, Fin.insert, Fin.insertNth, Fin.succAboveCases, Fin.coe_eq_castSucc,
      Fin.castSucc, Fin.castAdd, Fin.castLE, eq_rec_constant, Fin.is_lt, Fin.castPred_mk, Fin.eta]
    split
    . rename_i h'
      have: j.val = i.val := by
        exact Fin.mk.inj_iff.mp h'
      simp_all only [lt_self_iff_false]
    . split
      . rfl
      . rename_i h'
        have: ¬ j.val < i.val := by
          exact h'
        contradiction
  . use ⟨j.val + 1, by omega⟩
    simp only [not_lt] at h
    congr
    simp only [Fin.insertNth, Fin.insert, Fin.insertNth, Fin.succAboveCases, Int.reduceNeg, id_eq,
      Int.Nat.cast_ofNat_Int, eq_rec_constant]
    split
    . rename_i h'
      have: j.val + 1 = i.val := by
        exact Eq.symm (Fin.mk.inj_iff.mp (id (Eq.symm h')))
      omega
    . split
      . rename_i h'
        have: j.val + 1 < i.val := by
          exact h'
        omega
      . simp only [Fin.pred, Fin.subNat_mk, add_tsub_cancel_right, Fin.eta]

theorem word_project (x b : ℕ)  (v : Fin m → ℕ) (i : Fin (m + 1)) : ∃ k, (List.map (fun f ↦ Fin.removeNth i f) (toWord (Fin.insertNth i x v) b)) = padZeros k (toWord v b) := by
  use maxLenFin (mapToBase (b + 2) (Fin.insertNth i x v)) - maxLenFin (mapToBase (b + 2) v)
  rw[word_project_aux, toWord]
  rw[padZeros_zip]
  have len := maxLenFin_recover x b v i
  congr
  . omega
  . funext j
    simp[stretchLen, addZeroes_addZeroes]
    have := len_le_maxLenFin (mapToBase (b + 2) v) j
    have : (maxLenFin (mapToBase (b + 2) (Fin.insertNth i x v)) - maxLenFin (mapToBase (b + 2) v) +
      (maxLenFin (mapToBase (b + 2) v) - (mapToBase (b + 2) v j).length)) = maxLenFin (mapToBase (b + 2) (Fin.insertNth i x v)) - (mapToBase (b + 2) v j).length := by omega
    rw[this]
    clear this; clear this
    simp only [Fin.removeNth, Fin.removeNth, stretchLen, mapToBase]
    congr
    . simp only [Fin.insertNth_apply_succAbove]
    . simp only [Fin.insertNth_apply_succAbove]

theorem correct_project [Fintype state] [DecidableEq state] (v : Fin l → ℕ) (i : Fin (l + 1)) (dfa : DFA (Fin (l+1) → Fin (b+2)) state) (hres: dfa.respectZero):
  (∃ (x : ℕ), dfa.eval (toWord (Fin.insertNth i x v) b)) → (project i dfa).fixLeadingZeros.eval (toWord v b) := by
  rw[NFA.fixLeadingZeros_eval]
  intro h
  rcases h with ⟨x, h⟩
  have := eval_project dfa i (toWord (Fin.insertNth i x v) b) h

  have lis := word_project x b v i
  rcases lis with ⟨k, h₁⟩
  rw[h₁] at this
  apply (project i dfa).bounded_accept _
  . apply project_acceptZero
    exact DFA.acceptZero_of_respectZero dfa hres
  swap
  . exact padZeros k (toWord v b)
  . constructor
    . use k
    . exact this

theorem project_word (w: List (Fin (l+1) → Fin (b+2))) (i : Fin (l + 1)) : (toNat (List.map (Fin.removeNth i) w)) = Fin.removeNth i (toNat w) := by
  funext j
  simp only [toNat, toNat_aux, getDigits, Fin.removeNth, List.map_map, Fin.removeNth]
  rfl

theorem project_correct [Fintype state] [DecidableEq state] (v : Fin l → ℕ) (i : Fin (l + 1)) (dfa : DFA (Fin (l+1) → Fin (b+2)) state) (hres: dfa.respectZero):
  (project i dfa).fixLeadingZeros.eval (toWord v b) → (∃ (x : ℕ), dfa.eval (toWord (Fin.insertNth i x v) b)) := by
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
  use (toNat w) i
  have htoNat: toNat (padZeros (Fintype.card (ListND state)) (toWord v b)) = toNat (List.map (Fin.removeNth i) w) := by
    rw[hlis]
  simp only [toNat, toWord, padZeros_zip, stretchLen, addZeroes_addZeroes,
    getDigits_of_zip] at htoNat
  have htoNatAddZero : (toNat_aux b fun i => addZeroes (Fintype.card (ListND state) + (maxLenFin (mapToBase (b + 2) v) - (mapToBase (b + 2) v i).length)) (mapToBase (b + 2) v i)) = v := by
    funext i
    simp only [toNat_aux, mapToBase, ofBase_addZeroes, ofBase_toBase]
  rw[htoNatAddZero, ← toNat] at htoNat
  clear htoNatAddZero
  have h₁ : (Fin.insertNth i ((toNat w) i) v) = toNat w := by
    funext j
    rw[htoNat, project_word]
    simp only [Fin.insertNth, Fin.insert, Fin.removeNth, Fin.insertNth_removeNth,
      Function.update_eq_self]
    simp only [Fin.succAbove_cases_eq_insertNth, Fin.insertNth_removeNth, Function.update_eq_self]
  simp_rw[h₁]
  exact this

theorem project_iff [Fintype state] [DecidableEq state] (v : Fin l → ℕ) (i : Fin (l + 1)) (dfa : DFA (Fin (l+1) → Fin (b+2)) state) (hres: dfa.respectZero):
  (project i dfa).fixLeadingZeros.eval (toWord v b) ↔ (∃ (x : ℕ), dfa.eval (toWord (Fin.insertNth i x v) b)) := by
  constructor
  . exact fun a ↦ project_correct v i dfa hres a
  . exact fun a ↦ correct_project v i dfa hres a
