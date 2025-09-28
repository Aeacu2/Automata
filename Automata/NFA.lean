import Mathlib.Tactic
import Mathlib.Data.List.Basic
import Automata.DFA
import Mathlib.Data.List.Defs
import Mathlib.Data.FinEnum

/-- A type for Lists with no duplicates, for synthesizing [Fintype ListND] state from [Fintype state] -/
abbrev ListND (α : Type) := {l : List α // l.Nodup}

structure NFA (α state : Type) where
  (transition : α → state → ListND state)
  (start : ListND state)
  (output : state → Bool)

def NFA.transList (nfa : NFA α state) (a : α) (qs : ListND state) [DecidableEq state] : ListND state :=
  ⟨(qs.val.flatMap fun q => nfa.transition a q).dedup, (by apply List.nodup_dedup)⟩

theorem NFA.transList_backtrack (nfa : NFA α state) (a : α) (p : state) (states : ListND state) [DecidableEq state] : p ∈ (nfa.transList a states).val → ∃ q ∈ states.val, p ∈ (nfa.transition a q).val := by
  simp only [transList, List.mem_dedup, List.mem_flatMap, imp_self]

theorem NFA.transList_sublist (nfa : NFA α state) (a : α) (qs : ListND state) [DecidableEq state] : ps.val ⊆ qs.val → (nfa.transList a ps).val ⊆ (nfa.transList a qs) := by
  simp only [transList]
  intro h p hp
  -- aesop
  simp_all only [List.mem_dedup, List.mem_flatMap]
  obtain ⟨val, property⟩ := ps
  obtain ⟨val_1, property_1⟩ := qs
  obtain ⟨w, h_1⟩ := hp
  obtain ⟨left, right⟩ := h_1
  simp_all only
  apply Exists.intro
  · apply And.intro
    apply h
    on_goal 2 => {exact right
    }
    simp_all only

def NFA.transFrom (nfa : NFA α state) (s : List α) (qs : ListND state) [DecidableEq state] : ListND state :=
  match s with
    | [] => qs
    | a::as => NFA.transFrom nfa as (NFA.transList nfa a qs)

theorem NFA.transFrom_nil (nfa : NFA α state) (qs : ListND state) [DecidableEq state] : nfa.transFrom [] qs = qs := by rfl

theorem NFA.transFrom_sublist (nfa : NFA α state) (s : List α) (qs : ListND state) [DecidableEq state] : ps.val ⊆ qs.val → (nfa.transFrom s ps).val ⊆ (nfa.transFrom s qs).val := by
  induction s generalizing ps qs
  case nil =>
    simp[NFA.transFrom]
  case cons a as ih =>
    simp[NFA.transFrom]
    intro h
    specialize ih (ps := (nfa.transList a ps)) (qs := (nfa.transList a qs))
    exact ih (by apply NFA.transList_sublist; exact h)

def NFA.evalFrom (nfa : NFA α state) (s : List α) (qs : ListND state) [DecidableEq state] : Bool :=
  (nfa.transFrom s qs).val.any nfa.output

def NFA.eval (nfa : NFA α state) (s : List α) [DecidableEq state] : Bool :=
  NFA.evalFrom nfa s nfa.start

def NFA.toDFA (nfa : NFA α state) [DecidableEq state] : DFA α (ListND state) where
  transition := fun a qs => NFA.transList nfa a qs
  start := nfa.start
  output := fun qs => qs.val.any nfa.output

theorem NFA.toDFA_transition (nfa : NFA α state) (a : α) (qs : ListND state) [DecidableEq state]:
  (nfa.toDFA).transition a qs = NFA.transList nfa a qs := by rfl

theorem NFA.toDFA_evalFrom (nfa : NFA α state) (x : List α) (qs: ListND state) [DecidableEq state]:
  (nfa.toDFA).evalFrom x qs = nfa.evalFrom x qs := by
  induction x generalizing qs
  case nil =>
    simp [NFA.evalFrom, DFAO.evalFrom, DFAO.transFrom, NFA.toDFA]
    obtain ⟨val, property⟩ := qs
    simp_all only
    rfl
  case cons y ys ih =>
    simp only [NFA.evalFrom, DFAO.evalFrom]
    exact ih (nfa.transList y qs)

theorem NFA.toDFA_eval (nfa : NFA α state) (s : List α) [DecidableEq state]
  : (nfa.toDFA).eval s = nfa.eval s := NFA.toDFA_evalFrom nfa s nfa.start
