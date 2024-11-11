import Mathlib.Tactic
import Mathlib.Computability.Language

open Computability

structure DFAO (α state out: Type):=
  (transition : α → state → state)
  (start : state)
  (output : state → out)

variable {α state out : Type}

def DFAO.transFrom (dfao : DFAO α state out) (x : List α) (s : state) : state :=
  match x with
    | [] => s
    | a::as => DFAO.transFrom dfao as (dfao.transition a s)

-- The following theorems and proofs until the pumping lemmas are based on Mathlib's Computability.DFA
theorem DFAO.transFrom_of_append (dfao: DFAO α state out)(start : state) (x y : List α) :
    dfao.transFrom (x ++ y) start = dfao.transFrom y (dfao.transFrom x start) := by
  induction x generalizing start with
  | nil => rfl
  | cons a x ih =>
    simp only [List.append, DFAO.transFrom]
    specialize ih (dfao.transition a start)
    simp only [List.append_eq, ih]

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
  · exact this m n hneq.symm heq.symm (le_of_not_le hle)
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

-- Question: Languages use Sets, should we use them, or just do exist n?
theorem DFAO.transFrom_of_pow {dfao : DFAO α state out} {x y : List α} {s : state} (hx : dfao.transFrom x s = s)
    (hy : y ∈ ({x} : Language α)∗) : dfao.transFrom y s = s := by
  rw [Language.mem_kstar] at hy
  rcases hy with ⟨S, rfl, hS⟩
  induction' S with a S ih
  · rfl
  · have ha := hS a (List.mem_cons_self _ _)
    rw [Set.mem_singleton_iff] at ha
    rw [List.join, DFAO.transFrom_of_append, ha, hx]
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

def DFAO.evalFrom (dfao : DFAO α state out) (x : List α) (q : state) : out :=
  dfao.output (DFAO.transFrom dfao x q)

def DFAO.eval (dfao : DFAO α state out) (x : List α) : out :=
  DFAO.evalFrom dfao x dfao.start

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
    simp only [evalFrom, hy, hx]

theorem DFAO.pumping_lemma_eval [Fintype state] {dfao : DFAO α state out} {x : List α} {o : out} (hx : dfao.eval x = o)(hlen : Fintype.card state ≤ x.length) :
    ∃ a b c, x = a ++ b ++ c ∧ a.length + b.length ≤ Fintype.card state ∧ b ≠ []
      ∧ ∀ y ∈ ({a} * {b}∗ * {c} : Language α), dfao.eval y = o := by
  exact dfao.pumping_lemma_evalFrom hx hlen

-- A DFA is a DFAO where the output is a boolean
abbrev DFA (α state : Type) := DFAO α state Bool

def DFAO.toDFA (dfao : DFAO α state out) (o: out) [BEq out]: DFA α state := {
  transition := dfao.transition,
  start := dfao.start,
  output := fun s => (dfao.output s) == o
}

def DFAO.toDFA_evalFrom (dfao : DFAO α state out)
  (o: out) (s : List α) (q : state) [BEq out] :
    (dfao.toDFA o).evalFrom s q = ((dfao.evalFrom s q) == o) := by
  induction s generalizing q with
  | nil => rfl
  | cons x xs ih =>
    simp only [DFAO.evalFrom, DFAO.toDFA]
    exact ih (dfao.transition x q)

def DFAO.toDFA_eval (dfao : DFAO α state out)
  (o: out) (s : List α) [BEq out] :
    (dfao.toDFA o).eval s = (dfao.eval s == o) := by
  exact DFAO.toDFA_evalFrom dfao o s dfao.start

-- Operations on DFAs: negation, intersection, union
def DFA.negate (dfa: DFA α state) : DFA α state := {
  transition := dfa.transition
  start := dfa.start
  output := fun x =>  ! dfa.output x
}

def DFA.intersection (dfa1 : DFA α state1) (dfa2 : DFA α state2) : DFA (α ) (state1 × state2) := {
  transition := fun a q => ⟨dfa1.transition a q.1, dfa2.transition a q.2⟩,
  start := (dfa1.start, dfa2.start),
  output := fun (q1, q2) => dfa1.output q1 && dfa2.output q2
}

def DFA.union  (dfa1 : DFA α state1) (dfa2 : DFA α state2) : DFA (α) (state1 × state2) := {
  transition := fun a q => ⟨dfa1.transition a q.1, dfa2.transition a q.2⟩,
  start := (dfa1.start, dfa2.start),
  output := fun (q1, q2) => dfa1.output q1 || dfa2.output q2
}

theorem DFA.negate_output (dfa : DFA α state) (q : state) :
  (dfa.negate).output q = ! dfa.output q := by rfl

theorem DFA.negate_transition (dfa : DFA α state) :
  (dfa.negate).transition = dfa.transition := by rfl

theorem DFA.negate_transFrom (dfa : DFA α state) (s : List α) (q : state) :
  (dfa.negate).transFrom s q = dfa.transFrom s q := by
  induction s generalizing q
  case nil => rfl
  case cons a s ih =>
    rw [DFAO.transFrom, DFAO.transFrom, DFA.negate_transition, ih]

theorem DFA.negate_evalFrom (dfa : DFA α state) (s : List α) (q : state) :
  (dfa.negate).evalFrom s q = ! dfa.evalFrom s q := by
  simp[DFAO.evalFrom, DFA.negate_transFrom, DFA.negate_output]

theorem DFA.negate_eval (dfa : DFA α state) (s : List α) :
  (dfa.negate).eval s = ! dfa.eval s := by
  exact DFA.negate_evalFrom dfa s dfa.start

theorem DFA.intersection_output (dfa1 : DFA α state1) (dfa2 : DFA α state2) (q1 : state1) (q2 : state2) :
  (dfa1.intersection dfa2).output (q1, q2) = (dfa1.output q1 && dfa2.output q2) := by rfl

theorem DFA.intersection_transition (dfa1 : DFA α state1) (dfa2 : DFA α state2) :
  (dfa1.intersection dfa2).transition = fun a q => ⟨dfa1.transition a q.1, dfa2.transition a q.2⟩ := by rfl

theorem DFA.intersection_transFrom (dfa1 : DFA α state1) (dfa2 : DFA α state2) (s : List α) (q1 : state1) (q2 : state2) :
  (dfa1.intersection dfa2).transFrom s (q1, q2) = (dfa1.transFrom s q1, dfa2.transFrom s q2) := by
  induction s generalizing q1 q2
  case nil => rfl
  case cons a s ih =>
    simp [DFAO.transFrom, DFA.intersection_transition, ih]

theorem DFA.intersection_evalFrom (dfa1 : DFA α state1) (dfa2 : DFA α state2) (s : List α) (q1 : state1) (q2 : state2) :
  (dfa1.intersection dfa2).evalFrom s (q1, q2) = (dfa1.evalFrom s q1 && dfa2.evalFrom s q2) := by
  simp[DFAO.evalFrom, DFA.intersection_transFrom, DFA.intersection_output]

theorem DFA.intersection_eval (dfa1 : DFA α state1) (dfa2 : DFA α state2)
  (s : List α) : (dfa1.intersection dfa2).eval s = (dfa1.eval s && dfa2.eval s) := by
  exact DFA.intersection_evalFrom dfa1 dfa2 s dfa1.start dfa2.start

theorem DFA.union_output (dfa1 : DFA α state1) (dfa2 : DFA α state2) (q1 : state1) (q2 : state2) :
  (dfa1.union dfa2).output (q1, q2) = (dfa1.output q1 || dfa2.output q2) := by rfl

theorem DFA.union_transition (dfa1 : DFA α state1) (dfa2 : DFA α state2) :
  (dfa1.union dfa2).transition = fun a q => ⟨dfa1.transition a q.1, dfa2.transition a q.2⟩ := by rfl

theorem DFA.union_transFrom (dfa1 : DFA α state1) (dfa2 : DFA α state2) (s : List α) (q1 : state1) (q2 : state2) :
  (dfa1.union dfa2).transFrom s (q1, q2) = (dfa1.transFrom s q1, dfa2.transFrom s q2) := by
  induction s generalizing q1 q2
  case nil => rfl
  case cons a s ih =>
    simp [DFAO.transFrom, DFA.union_transition, ih]

theorem DFA.union_evalFrom (dfa1 : DFA α state1) (dfa2 : DFA α state2) (s : List α) (q1 : state1) (q2 : state2) :
  (dfa1.union dfa2).evalFrom s (q1, q2) = (dfa1.evalFrom s q1 || dfa2.evalFrom s q2) := by
  simp[DFAO.evalFrom, DFA.union_transFrom, DFA.union_output]

theorem DFA.union_eval (dfa1 : DFA α state1) (dfa2 : DFA α state2)
  (s : List α) : (dfa1.union dfa2).eval s = (dfa1.eval s || dfa2.eval s) := by
  exact DFA.union_evalFrom dfa1 dfa2 s dfa1.start dfa2.start
