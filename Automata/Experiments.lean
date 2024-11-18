import Mathlib.Tactic
import Mathlib.Data.List.Basic
import Automata.DFA
import Automata.NFA
import Automata.Input
import Automata.Projection
import Automata.Addition

/- Discuss:
NFA, ListND

Replicate, Projection

Fin
-/

def Fin.func_res (f: Fin (n + 1) → α) : Fin n → α :=
  fun i => f i

def Fin.func_move (f: Fin (n+1) → α) : Fin n → α :=
  fun i => f (i+1)

def DFAO.transFrom' (dfa : DFAO α state out) (x : Fin n → α) (s : state) : state :=
  match n with
    | 0 => s
    | i+1 => dfa.transition (x i) (dfa.transFrom' (Fin.func_res x) s)

def DFAO.transFrom'' (dfa : DFAO α state out) (x : Fin n → α) (s : state) : state :=
  match n with
    | 0 => s
    | _ + 1 => dfa.transFrom'' (Fin.func_move x) (dfa.transition (x 0) s)

def DFAO.evalFrom' (dfa : DFAO α state out) (x : Fin n → α) (q : state) : out := dfa.output (dfa.transFrom' x q)

def DFAO.evalFrom'' (dfa : DFAO α state out) (x : Fin n → α) (q : state) : out := dfa.output (dfa.transFrom'' x q)

def DFAO.eval' (dfa : DFAO α state out) (x : Fin n → α) : out := dfa.evalFrom' x dfa.start

def DFAO.eval'' (dfa : DFAO α state out) (x : Fin n → α) : out := dfa.evalFrom'' x dfa.start

def NFA.transFrom' (nfa : NFA α state) (x : Fin n → α) (qs : ListND state) [DecidableEq state] : ListND state :=
  match n with
    | 0 => qs
    | i+1 => nfa.transList (x i) (NFA.transFrom' nfa (Fin.func_res x) qs)

def NFA.transFrom'' (nfa : NFA α state) (x : Fin n → α) (qs : ListND state) [DecidableEq state] : ListND state :=
  match n with
    | 0 => qs
    | _ + 1 => nfa.transFrom'' (Fin.func_move x) (nfa.transList (x 0) qs)

def NFA.evalFrom' (nfa : NFA α state) (x : Fin n → α) (qs : ListND state) [DecidableEq state] : Bool := (nfa.transFrom' x qs).val.any nfa.output

def NFA.evalFrom'' (nfa : NFA α state) (x : Fin n → α) (qs : ListND state) [DecidableEq state] : Bool := (nfa.transFrom'' x qs).val.any nfa.output

def NFA.eval' (nfa : NFA α state) (x : Fin n → α) [DecidableEq state]: Bool := nfa.evalFrom' x nfa.start

def NFA.eval'' (nfa : NFA α state) (x : Fin n → α) [DecidableEq state]: Bool := nfa.evalFrom'' x nfa.start

def toBase' (b: ℕ) (n: ℕ) (h : b ≥ 2): List (Fin b) :=
  (toBase b n).attach.map (fun x => ⟨x.1, (by apply toBase_lt_base b n (by omega); obtain ⟨val, property⟩ := x; simp_all only)⟩)

def toBaseFin (b n: ℕ) (h : b ≥ 2): Fin (toBase' b n h).length → Fin b :=
  fun i => (toBase' b n h)[i]

def stretchFin (m: ℕ) (h : b ≥ 2) (f : Fin n → Fin b) : Fin (m + n) → Fin b :=
  fun i => if h1: i.val < m then ⟨0, by omega⟩ else f ⟨i.val - m, (by omega)⟩

def stretchFinTo (m: ℕ) (h : b ≥ 2) (f : Fin n → Fin b) (hmn : m ≥ n) : Fin m → Fin b :=
  fun i => if h1: i.val < m - n then ⟨0, by omega⟩ else f ⟨i.val - (m - n), (by omega)⟩

def maxFin (b: ℕ) (l: List ℕ) (h: b ≥ 2) : ℕ :=
  match l with
    | [] => 0
    | x::xs => max ((toBase' b x h).length) (maxFin b xs h)

theorem maxFin_max (b: ℕ) (l: List ℕ) (h: b ≥ 2) : ∀ i, i ∈ l → maxFin b l h ≥ (toBase' b i h).length := by
  intro i hi
  induction l with
    | nil => contradiction
    | cons x xs ih =>
      rcases hi with hi | hi
      . simp only [maxFin, le_max_iff, le_refl, true_or]
      . simp only [maxFin, le_max_iff]
        right
        rename_i a
        apply ih
        exact a

-- def mapToBaseFin' (b: ℕ) (l: List ℕ) (h: b ≥ 2): Fin l.length → (Fin (maxFin b l h) → Fin b) :=
--   have : ∀ i, ∀ (hi: i < l.length), (maxFin b l h - (toBase' b l[i] h).length + (toBase' b l[i] h).length) = maxFin b l h := by
--     intro i hi
--     have := maxFin_max b l h l[i] (by apply List.getElem_mem)
--     omega
--   fun i => (stretchFin (maxFin b l h - (toBase' b l[i] h).length) h (toBaseFin b l[i] h) : Fin (maxFin b l h) → Fin b)

def mapToBaseFin (b: ℕ) (l: List ℕ) (h: b ≥ 2): Fin l.length → Fin (maxFin b l h) → Fin b :=
  fun i => (stretchFinTo (maxFin b l h) h (toBaseFin b l[i] h) (by apply maxFin_max; apply List.getElem_mem) : Fin (maxFin b l h) → Fin b)

def toInputFin (b: ℕ) (l: List ℕ) (h: b ≥ 2): Fin (maxFin b l h) → Fin l.length → Fin b :=
  fun i => fun j => mapToBaseFin b l h j i

def padZero (k : ℕ) (f : Fin m → Fin n → Fin b) (h : b ≥ 2) : Fin (k + m) → Fin n → Fin b :=
  fun i => fun j => if h: i.val < k then ⟨0, by omega⟩ else f ⟨i.val - k, (by omega)⟩ j

def toInputList (f: Fin m → Fin n → Fin b) : List (Fin n → Fin b) :=
  List.ofFn f

set_option trace.profiler true

def l' := (toInputList (toInputFin 2 [10^100, 10000] (by exact Nat.one_lt_two)))

#eval l'

def l := inputToBase 2 (by exact Nat.one_lt_two) [10^100, 10000]

#eval l

#eval (project 2 (addBase 2)).toDFA.eval' (toInputFin 2 [10^100, 10000] (by exact Nat.one_lt_two))

#eval (project 2 (addBase 2)).toDFA.eval (inputToBase 2 (by exact Nat.one_lt_two) [10^100, 10000])

#eval (project 2 (addBase 2)).toDFA.eval'' (toInputFin 2 [10^100, 10000] (by exact Nat.one_lt_two))

#eval (project 2 (addBase 2)).toDFA.eval l

#eval (project 2 (addBase 2)).toDFA.eval l'

#eval l


