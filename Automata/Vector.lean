import Mathlib.Logic.Basic
import Mathlib.Data.Sigma.Basic
import Mathlib.Tactic.GeneralizeProofs

-- By Wojciech Nawrocki

/-!
Repurposing some ideas from *Heq: a Coq library for Heterogeneous Equality*
(https://sf.snu.ac.kr/publications/heq.pdf)
for Lean.
-/

/-! ## Sigma-equality and indexed cast -/

/-- When manipulating elements `x : β a`, `y : β b` of a type family `α ⊢ β type`
with propositionally equal indices `a b : α`,
it is better to state an equality between dependent pairs `@Eq (Sigma β) ⟨a, x⟩ ⟨b, y⟩`
than a heterogeneous equality `HEq x y`.
This is because the latter implies `β a = β b`,
but type constructors are not provably injective
(in fact, injectivity of type constructors is inconsistent with excluded middle:
https://lists.chalmers.se/pipermail/agda/2010/001522.html).
In contrast, an equality of dependent pairs directly entails `a = b`.
Hypothesis: this is about as general as `HEq`,
as most (all?) nontrivial type equalities arise from index equality. -/
notation:50 x:51 " =[" β "]= " y:51 => @Eq (Sigma β) ⟨_, x⟩ ⟨_, y⟩

/-- Like `cast` but stores a proof of equality of indices. See `SEq` for motivation.
In Rocq this is known as `eq_rect`. -/
@[macro_inline]
def dcast {α : Type u} {a b : α} {β : α → Type v} : a = b → β a → β b :=
  -- `ndrecOn` is an abbrev that simps to `Eq.rec`,
  -- but we do not want to simp `dcast` to `Eq.rec` (.. or do we?).
  Eq.ndrecOn

@[simp]
theorem dcast_rfl {α : Type u} {a : α} {β : α → Type v} (h : a = a) (x : β a) :
    dcast h x = x := by
  rfl

@[simp]
theorem dcast_dcast {α : Type u} {β : α → Type v} (a b c : α) (h : a = b) (h' : b = c) (x : β a) :
    dcast h' (dcast h x) = dcast (h.trans h') x := by
  cases h
  simp

theorem SEq_iff {α : Type u} {a b : α} {β : α → Type v} {x : β a} {y : β b} :
    x =[ β ]= y ↔ ∃ (h : a = b), dcast h x = y := by
  constructor
  . intro h
    have ⟨h, h'⟩ := Sigma.mk.inj_iff.mp h
    refine ⟨h, by cases h; simpa using h⟩
  . intro ⟨h, h'⟩
    cases h
    simpa using h'

theorem SEq_iff' {α : Type u} {a b : α} {β : α → Type v} {x : β a} {y : β b} :
    x =[ β ]= y ↔ ∃ (h : b = a), x = dcast h y := by
  constructor
  . intro h
    have ⟨h, h'⟩ := Sigma.mk.inj_iff.mp h
    refine ⟨h.symm, by cases h; simpa using h'⟩
  . intro ⟨h, h'⟩
    cases h
    simpa using h'

theorem SEq_idx_eq {α : Type u} {a b : α} {β : α → Type v} {x : β a} {y : β b} (h : x =[ β ]= y) :
    a = b :=
  (SEq_iff.mp h).fst

theorem SEq_eq {α : Type u} {a b : α} {β : α → Type v} {x : β a} {y : β b} (h : x =[ β ]= y) :
    x = dcast (SEq_idx_eq h).symm y :=
  (SEq_iff'.mp h).snd

-- This produces a `HEq` which we don't want
attribute [-simp] Sigma.mk.inj_iff

/-! ## Test case: proofs about intrinsically sized vectors
Note: no constructor or function is Forded here;
we carry proofs of index equality in `dcast` and `SEq` instead. -/

inductive Vector : Type u → Nat → Type u :=
  | vnil (α) : Vector α 0
  | vcons {α} {n} : α → Vector α n → Vector α (n + 1)
  deriving Repr, BEq

namespace Vector

def tail {α n} : Vector α (n + 1) → Vector α n
  | vcons _ v => v

def vapp {α n m} : Vector α n → Vector α m → Vector α (m + n)
  | vnil _,    v => v
  | vcons a u, v => vcons a (vapp u v)

notation "⟦⟧" => Vector.vnil _
infixr:67 " ::: " => Vector.vcons
infixl:65 " +++ " => Vector.vapp

def vrev {α n} : Vector α n → Vector α n
  | vnil _      => vnil _
  | vcons hd tl => dcast (by omega) $ vrev tl +++ hd ::: ⟦⟧

def take : (n: Nat) → Vector α m → Vector α (min n m)
  | 0,   _     => dcast (by omega) ⟦⟧
  | _+1, ⟦⟧    => dcast (by omega) ⟦⟧
  | n+1, a:::as => dcast (by omega) (a ::: take n as)

def drop : (n: Nat) → Vector α m → Vector α (m - n)
  | 0,   a     => a
  | _+1, ⟦⟧    => dcast (by omega) ⟦⟧
  | n+1, _ ::: a => dcast (by omega) (drop n a)

/-! ## "Indexed cast calculus" for Vector operations
Simp rules pull casts outwards. -/

@[local simp]
theorem vcons_dcast {α : Type u} {n m : Nat} (a : α) (v : Vector α n) (h : n = m) :
    a ::: dcast h v = dcast (h ▸ rfl) (a ::: v) := by
  cases h
  simp

@[local simp]
theorem vapp_dcast_left {α : Type u} {n m k : Nat}
      (u : Vector α n) (h : n = m) (v : Vector α k) :
    dcast h u +++ v = dcast (h ▸ rfl) (u +++ v) := by
  cases h
  simp

@[local simp]
theorem vapp_dcast_right {α : Type u} {n m k : Nat}
      (u : Vector α n) (v : Vector α m) (h : m = k)  :
    u +++ dcast h v = dcast (h ▸ rfl) (u +++ v) := by
  cases h
  simp

/-! ## Congruence laws
These helper lemmas would be superseded by a `srw` tactic/term elaborator. -/

theorem vcons_scongr {α : Type u} {n m : Nat} {u : Vector α n} {v : Vector α m} (a : α)
    (h : u =[ Vector α ]= v) : a ::: u =[ Vector α ]= a ::: v := by
  simp [SEq_iff, SEq_eq h, SEq_idx_eq h]

/-! ## Properties of Vector operations -/

theorem HEq.comm {a : α} {b : β} : HEq a b ↔ HEq b a :=
  Iff.intro HEq.symm HEq.symm

theorem vapp_vnil {α n} (v : Vector α n) : v +++ ⟦⟧ =[Vector α]= v := by
  induction v with
  | vnil => rfl
  | vcons a v ih =>
    rename_i n
    rw [vapp]

    -- This proof simulates `Hrewritec` as described in the paper
    rw [Sigma.mk.inj_iff] at ih
    have ⟨eq, eq'⟩ := ih
    rw [HEq.comm, ← cast_eq_iff_heq (e := type_eq_of_heq ih.right.symm)] at eq'
    rw [← eq']
    generalize_proofs pf
    clear ih eq' -- Now `+++` no longer appears anywhere
    -- `generalize` fails if we don't `dsimp` first,
    -- which I think is a bug
    dsimp only [HAdd.hAdd, Add.add, Nat.add] at eq pf ⊢
    generalize Nat.add 0 n = x at *
    cases eq
    rfl

theorem vapp_vnil' {α n} (v : Vector α n) : v +++ ⟦⟧ =[Vector α]= v := by
  induction v with
  | vnil => rfl
  | vcons a v ih =>
    rename_i n
    rw [vapp]

    -- This proof uses `dcast`
    simp [SEq_iff, SEq_eq ih]

theorem vapp_assoc {α n m k} (u : Vector α n) (v : Vector α m) (w : Vector α k) :
    (u +++ v) +++ w =[Vector α]= u +++ (v +++ w) := by
  induction u with
  | vnil => rfl
  | vcons a w ih => simp [SEq_iff, SEq_eq ih, vapp, Nat.add_assoc]

theorem vrev_vapp {α n m} (u : Vector α n) (v : Vector α m) :
    vrev (u +++ v) =[Vector α]= vrev v +++ vrev u := by
  induction u with
  | vnil => simp [SEq_iff, SEq_eq (vapp_vnil _), vapp, vrev]
  | vcons a u ih => simp [SEq_iff, SEq_eq ih, SEq_eq (vapp_assoc ..), vrev, Nat.add_comm]

/-! ## Final boss: tail-recursive rev -/

def vrev_tailRec {α n} (v : Vector α n) : Vector α n :=
  dcast (by omega) $ go ⟦⟧ v
where go {n m : Nat} (acc : Vector α n) : Vector α m → Vector α (n + m)
  | vnil _      => acc
  -- TODO: does leanc see through the cast and compile this as tail-recursive?
  | vcons a v => dcast (by omega) $ go (a ::: acc) v

@[csimp]
theorem vrev_eq_vrev_tailRec : @vrev = @vrev_tailRec := by
  ext1 α
  suffices ∀ {n m} (u : Vector α n) (v : Vector α m), vrev_tailRec.go u v =[ Vector α ]= vrev v +++ u by
    ext n v
    simp [vrev_tailRec, SEq_eq (this ..), SEq_eq (vapp_vnil _)]
  intro n m u v
  induction v generalizing n u with
  | vnil => rfl
  | vcons a v ih =>
    simp [SEq_iff, vrev_tailRec.go, SEq_eq (ih _), vrev, SEq_eq (vapp_assoc ..), vapp]

/-! Not a bad proof at all!
Key point is that `SEq_eq` allows rewriting by `SEq`,
and `simp` lemmas normalize the resulting `dcast`s
until we end up with `dcast h a = dcast h' a`
which is true by proof-irrelevance. -/

/-! ## Actually that wasn't the final boss: pushing casts
Sometimes we need to *push* `dcast` downwards.
So `op_dcast` lemmas shouldn't be `simp`,
but rather part of a custom simp-set similar to `norm_cast`. -/

def vplus {n} : Vector Nat n → Vector Nat n → Vector Nat n
  | vnil _,    vnil _    => vnil _
  | vcons a u, vcons b v => (a + b) ::: vplus u v

theorem push_vcons_dcast {α : Type u} {n m : Nat} (a : α) (v : Vector α n) (h : n + 1 = m + 1) :
    dcast h (a ::: v) = a ::: dcast (by simpa using h) v := by
  simp

-- "Now we consider the following goal."
example {n m} (u : Vector Nat n) (v : Vector Nat m) (a b : Nat) :
    vplus (a ::: (u +++ v)) (dcast (by omega) $ b ::: (v +++ u)) =[ Vector Nat ]=
    (a + b) ::: vplus (u +++ v) (dcast (by omega) $ v +++ u) := by
  simp [-vcons_dcast, push_vcons_dcast, vplus]

end Vector -- Clear `local simp` lemmas above.

/-! ## Iterated dependent pairs
This is not as nice as it could be.
Given a type such as `VectorH` below which depends on a telescope of arguments,
motive inference for `dcast` and `SEq` fails.
We provide a custom motive by defining `SVectorH v`,
but even then unification cannot find `?v` and we have to provide it manually.
Custom elaborators might be needed to really make this work.
The paper deals with this by using the pattern `PvecH`.
Fortunately, after this setup the proving of nested `SEq`s still just needs `simp`. -/

inductive VectorH : {n : Nat} → Vector Type n → Type 1
  | vnil : VectorH ⟦⟧
  | vcons {α : Type} {n : Nat} {v : Vector Type n} :
    α → VectorH v → VectorH (α ::: v)

namespace VectorH

/-- Package the arguments to `VectorH` as a telescope
in order to provide a motive for `dcast` and `SEq`. -/
-- @[reducible]
abbrev SVectorH (v : (n : Nat) × Vector Type n) : Type 1 := VectorH v.2

def vapp {n m} {u : Vector Type n} {v : Vector Type m} :
    VectorH u → VectorH v → VectorH (u +++ v)
  | vnil,      V => V
  | vcons a U, V => vcons a (vapp U V)

/-! ## VectorH cast calculus -/

@[local simp]
theorem vcons_dcast {α : Type} {n m : Nat} {u : Vector Type n} {v : Vector Type m}
    (a : α) (V : VectorH u) (h : u =[ Vector Type ]= v) :
    -- FIXME: Lean really fails to infer the motive.
    -- A `▸`-like notation for `dcast` with a custom elaborator might be needed
    vcons a (dcast (α := (n : Nat) × Vector Type n) (β := SVectorH) h V) =
    dcast
      (α := (n : Nat) × Vector Type n) (β := SVectorH)
      (a := ⟨n+1, α ::: u⟩) (b := ⟨m+1, α ::: v⟩)
      (Vector.vcons_scongr α h) (vcons a V) := by
  cases h
  simp

/-! ## Properties of VectorH operations -/

theorem vapp_vnil {n} {v : Vector Type n} {V : VectorH v} :
    -- FIXME: A custom elaborator for `=[β]=` might be needed to infer the pattern of nested Σs.
    @Eq (Sigma SVectorH)
      ⟨⟨_, v +++ ⟦⟧⟩, vapp V vnil⟩
      ⟨⟨_, v⟩, V⟩ := by
  induction V with
  | vnil => rfl
  | vcons a V ih =>
    simp [SEq_iff, vapp, SEq_eq ih, SEq_eq (Vector.vapp_vnil _)]

theorem vapp_assoc {n m k} {u : Vector Type n} {v : Vector Type m} {w : Vector Type k}
    (U : VectorH u) (V : VectorH v) (W : VectorH w) :
    @Eq (Sigma SVectorH)
      ⟨⟨_, (u +++ v) +++ w⟩, vapp (vapp U V) W⟩
      ⟨⟨_, u +++ (v +++ w)⟩, vapp U (vapp V W)⟩ := by
  induction U with
  | vnil => rfl
  | vcons a U ih =>
    simp [SEq_iff, vapp, SEq_eq ih, SEq_eq (Vector.vapp_assoc ..), Nat.add_assoc]

end VectorH

/-! ## hpattern -/

-- TODO: `generalize` could take a list of occurrences to abstract

/-! ## What about `cast` and `Eq.rec`?
`vcons_dcast` can be stated in terms of `cast`,
but applying this automatically would have to unify `?h` inside an equality proof such as `h ▸ rfl`
(because `Vector α n = Vector α m` doesn't imply `Vector α (n+1) = Vector α (m+1)`)
which neither `rw` nor `simp` can (or probably should) do. -/

-- theorem Vector.vcons_cast_bad {α : Type} {n m : Nat} (a : α) (v : Vector α n) (h : n = m) :
--     a ::: cast (h ▸ rfl) v = cast (h ▸ rfl) (a ::: v) := by
--   cases h
--   simp

/-! Instead, since `dcast` reduces to `Eq.rec` (`▸`),
it is possible to carry out the same development using `Eq.rec`.
However, it is crucial to control the motive:
`h ▸ h' ▸ b` does not simplify in general.
By setting the motive, `eqRec_eqRec` can be proven.
It is probably still worse than using `dcast`
as applying it involves higher-order unification (of the motive). -/

@[simp]
theorem eqRec_eqRec {α : Type u} {β : α → Type v} (a b c : α) (h : a = b) (h' : b = c) (x : β a) :
    Eq.rec (motive := fun x _ => β x) (Eq.rec (motive := fun x _ => β x) x h) h' =
    Eq.rec (motive := fun x _ => β x) x (h.trans h') := by
  cases h
  simp

theorem SEq_iff_rec {α : Type u} {a b : α} {β : α → Type v} {x : β a} {y : β b} :
    x =[ β ]= y ↔ ∃ (h : a = b), h ▸ x = y := by
  constructor
  . intro h
    have ⟨h, h'⟩ := Sigma.mk.inj_iff.mp h
    refine ⟨h, by cases h; simpa [Sigma.mk.inj_iff] using h⟩
  . intro ⟨h, h'⟩
    cases h
    simpa [Sigma.mk.inj_iff] using h'

theorem SEq_iff_rec' {α : Type u} {a b : α} {β : α → Type v} {x : β a} {y : β b} :
    x =[ β ]= y ↔ ∃ (h : b = a), x = h ▸ y := by
  constructor
  . intro h
    have ⟨h, h'⟩ := Sigma.mk.inj_iff.mp h
    refine ⟨h.symm, by cases h; simpa [Sigma.mk.inj_iff] using h'⟩
  . intro ⟨h, h'⟩
    cases h
    simpa [Sigma.mk.inj_iff] using h'

theorem SEq_eq_rec {α : Type u} {a b : α} {β : α → Type v} {x : β a} {y : β b} (h : x =[ β ]= y) :
    x = (SEq_idx_eq h) ▸ y :=
  (SEq_iff_rec'.mp h).snd

namespace Vector

@[local simp]
theorem vcons_cast {α : Type u} {n m : Nat} (a : α) (v : Vector α n) (h : n = m) :
    a ::: (h ▸ v) = Eq.rec (motive := fun x _ => Vector α x) (a ::: v) (h ▸ rfl) := by
  cases h
  simp

@[local simp]
theorem vapp_cast_left {α : Type u} {n m k : Nat}
      (u : Vector α n) (h : n = m) (v : Vector α k) :
    h ▸ u +++ v = Eq.rec (motive := fun x _ => Vector α x) (u +++ v) (h ▸ rfl) := by
  cases h
  simp

@[local simp]
theorem vapp_cast_right {α : Type u} {n m k : Nat}
      (u : Vector α n) (v : Vector α m) (h : m = k)  :
    u +++ h ▸ v = Eq.rec (motive := fun x _ => Vector α x) (u +++ v) (h ▸ rfl) := by
  cases h
  simp

theorem vrev_vapp' {α n m} (u : Vector α n) (v : Vector α m) :
    vrev (u +++ v) =[Vector α]= vrev v +++ vrev u := by
  induction u with
  | vnil =>
    simp [SEq_iff_rec, SEq_eq_rec (vapp_vnil _), vapp, vrev]
  | vcons a u ih =>
    simp [SEq_iff_rec, SEq_eq_rec ih, SEq_eq_rec (vapp_assoc ..), vrev, Nat.add_comm, dcast]

end Vector
