import Mathlib.Tactic
import Automata.DFA
import Automata.NFA_new
import Mathlib.Computability.Language

open Computability

-- The following theorems and proofs until the pumping lemmas are based on Mathlib's Computability.DFA
theorem DFAO.transFrom_of_append (dfao: DFAO α state out)(start : state) (x y : List α) :
    dfao.transFrom (x ++ y) start = dfao.transFrom y (dfao.transFrom x start) := by
  induction x generalizing start with
  | nil => rfl
  | cons a x ih =>
    simp only [DFAO.transFrom]

    specialize ih (dfao.transition a start)
    simp[DFAO.transFrom, ih]

theorem NFA.transFrom_of_append [LinearOrder state] (nfa : NFA α state) (start : ListSND state) (x y : List α) :
    nfa.transFrom (x ++ y) start = nfa.transFrom y (nfa.transFrom x start) := by
  induction x generalizing start with
  | nil => rfl
  | cons a x ih =>
    simp only [NFA.transFrom]
    exact ih (nfa.transList a start)

theorem DFAO.transFrom_split [Fintype state] {dfao : DFAO α state out} {x : List α} {s t : state} (hlen : Fintype.card state ≤ x.length)
    (hx : dfao.transFrom x s = t) :
    ∃ q a b c,
      x = a ++ b ++ c ∧
        a.length + b.length ≤ Fintype.card state ∧
          b ≠ [] ∧ dfao.transFrom a s = q ∧ dfao.transFrom b q = q ∧ dfao.transFrom c q = t := by
  obtain ⟨n, m, hneq, heq⟩ :=
    Fintype.exists_ne_map_eq_of_card_lt
      (fun n : Fin (Fintype.card state + 1) => dfao.transFrom (x.take n) s) (by norm_num)
  wlog hle : (n : ℕ) ≤ m generalizing n m
  · exact this m n hneq.symm heq.symm (le_of_not_ge hle)
  have hm : (m : ℕ) ≤ Fintype.card state := Fin.is_le m
  refine
    ⟨dfao.transFrom ((x.take m).take n) s, (x.take m).take n, (x.take m).drop n,
                    x.drop m, ?_, ?_, ?_, by rfl, ?_⟩
  · rw [List.take_append_drop, List.take_append_drop]
  · simp only [List.length_drop, List.length_take]
    rw [min_eq_left (hm.trans hlen), min_eq_left hle, add_tsub_cancel_of_le hle]
    exact hm
  · intro h
    have hlen' := congr_arg List.length h
    simp only [List.length_drop, List.length, List.length_take] at hlen'
    rw [min_eq_left, tsub_eq_zero_iff_le] at hlen'
    · apply hneq
      apply le_antisymm
      assumption'
    exact hm.trans hlen
  have hq : dfao.transFrom ((x.take m).drop n) (dfao.transFrom ((x.take m).take n) s) =
      dfao.transFrom ((x.take m).take n) s := by
    rw [List.take_take, min_eq_left hle, ← transFrom_of_append, heq, ← min_eq_left hle, ←
      List.take_take, min_eq_left hle, List.take_append_drop]
  use hq
  rwa [← hq, ← transFrom_of_append, ← transFrom_of_append, ← List.append_assoc,
    List.take_append_drop, List.take_append_drop]

theorem DFAO.transFrom_of_pow {dfao : DFAO α state out} {x y : List α} {s : state} (hx : dfao.transFrom x s = s)
    (hy : y ∈ ({x} : Language α)∗) : dfao.transFrom y s = s := by
  rw [Language.mem_kstar] at hy
  rcases hy with ⟨S, rfl, hS⟩
  induction' S with a S ih
  · rfl
  · have ha := hS a List.mem_cons_self
    rw [Set.mem_singleton_iff] at ha
    rw [List.flatten, DFAO.transFrom_of_append, ha, hx]
    apply ih
    intro z hz
    exact hS z (List.mem_cons_of_mem a hz)

theorem DFAO.pumping_lemma_trans [Fintype state] {dfao : DFAO α state out} {x : List α} {s t : state} (hx : dfao.transFrom x s = t)(hlen : Fintype.card state ≤ x.length) :
    ∃ a b c, x = a ++ b ++ c ∧ a.length + b.length ≤ Fintype.card state ∧ b ≠ []
      ∧ ∀ y ∈ ({a} * {b}∗ * {c} : Language α), dfao.transFrom y s = t := by
  obtain ⟨q, a, b, c, h, hlen', hne, ha, hb, hc⟩ := dfao.transFrom_split hlen hx
  use a, b, c
  constructor
  . exact h
  constructor
  . exact hlen'
  constructor
  . exact hne
  . intro y hy
    simp [Language.mem_mul] at hy
    rcases hy with ⟨i, hi, j, hj, k, hk, hy⟩
    rw[Set.mem_singleton_iff] at hi
    rw[Set.mem_singleton_iff] at hk
    rw[← hy, DFAO.transFrom_of_append, hi, ha, DFAO.transFrom_of_append, hk, DFAO.transFrom_of_pow hb]
    exact hc
    exact hj

theorem DFAO.evalFrom_of_append (dfao : DFAO α state out) (x y : List α) (q : state) :
  dfao.evalFrom (x ++ y) q = dfao.evalFrom y (dfao.transFrom x q) := by
  simp[DFAO.evalFrom, DFAO.transFrom_of_append]

theorem DFAO.pumping_lemma_evalFrom [Fintype state] {dfao : DFAO α state out} {x : List α} {s : state} {o : out} (hx : dfao.evalFrom x s = o)(hlen : Fintype.card state ≤ x.length) :
    ∃ a b c, x = a ++ b ++ c ∧ a.length + b.length ≤ Fintype.card state ∧ b ≠ []
      ∧ ∀ y ∈ ({a} * {b}∗ * {c} : Language α), dfao.evalFrom y s = o := by
  let t := dfao.transFrom x s
  have hx' : dfao.transFrom x s = t := by rfl
  obtain ⟨a, b, c, h, hablen, hne, hy⟩ := dfao.pumping_lemma_trans hx' hlen
  use a, b, c
  constructor
  . exact h
  constructor
  . exact hablen
  constructor
  . exact hne
  . intro y hy'
    specialize hy y hy'
    simp only [evalFrom] at hx
    simp_all only [evalFrom]


theorem DFAO.pumping_lemma_eval [Fintype state] {dfao : DFAO α state out} {x : List α} {o : out} (hx : dfao.eval x = o)(hlen : Fintype.card state ≤ x.length) :
    ∃ a b c, x = a ++ b ++ c ∧ a.length + b.length ≤ Fintype.card state ∧ b ≠ []
      ∧ ∀ y ∈ ({a} * {b}∗ * {c} : Language α), dfao.eval y = o := by
  exact dfao.pumping_lemma_evalFrom hx hlen

theorem NFA.pumping_lemma_evalFrom [Fintype state] [LinearOrder state] {nfa : NFA α state} {x : List α} {qs : ListSND state}(hx : nfa.evalFrom x qs)(hlen : Fintype.card (ListSND state) ≤ x.length) :
    ∃ a b c, x = a ++ b ++ c ∧ a.length + b.length ≤ Fintype.card (ListSND state) ∧ b ≠ []
      ∧ ∀ y ∈ ({a} * {b}∗ * {c} : Language α), nfa.evalFrom y qs := by
  rw [← toDFA_evalFrom] at hx
  obtain ⟨a, b, c, hxabc, hablen, hne, hy⟩ := nfa.toDFA.pumping_lemma_evalFrom hx hlen
  use a, b, c
  constructor
  . exact hxabc
  constructor
  . exact hablen
  constructor
  . exact hne
  intro y h
  specialize hy y h
  rwa [← toDFA_evalFrom nfa y qs]

theorem NFA.pumping_lemma_eval [Fintype state] [LinearOrder state] {nfa : NFA α state} {x : List α}(hx : nfa.eval x)(hlen : Fintype.card (ListSND state) ≤ x.length) :
    ∃ a b c, x = a ++ b ++ c ∧ a.length + b.length ≤ Fintype.card (ListSND state) ∧ b ≠ []
      ∧ ∀ y ∈ ({a} * {b}∗ * {c} : Language α), nfa.eval y := by
  exact pumping_lemma_evalFrom hx hlen
