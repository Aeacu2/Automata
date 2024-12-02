import Mathlib.Tactic
import Mathlib.Data.Nat.Digits

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

theorem toBase_lead_nonzero (b: ℕ) (n: ℕ) (hb: b ≥ 2) (hn : n > 0) :
  (toBase b n)[0]'(by
  simp[toBase, Nat.digits]
  split <;> try simp at hb
  rw[Nat.digitsAux.eq_def]
  split <;> try simp at hn
  simp
  ) > 0 := by
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

def mapToBaseFin (b: ℕ) (l: List ℕ) (h: b ≥ 2): Fin l.length → Fin (maxFin b l h) → Fin b :=
  fun i => (stretchFinTo (maxFin b l h) h (toBaseFin b l[i] h) (by apply maxFin_max; apply List.getElem_mem) : Fin (maxFin b l h) → Fin b)

def toInputFin (b: ℕ) (l: List ℕ) (h: b ≥ 2): Fin (maxFin b l h) → Fin l.length → Fin b :=
  fun i => fun j => mapToBaseFin b l h j i

def padZero (k : ℕ) (f : Fin m → Fin n → Fin b) (h : b ≥ 2) : Fin (k + m) → Fin n → Fin b :=
  fun i => fun j => if h: i.val < k then ⟨0, by omega⟩ else f ⟨i.val - k, (by omega)⟩ j
