import Mathlib.Tactic

-- #check Fin.succ
-- #check Fin.castSucc
-- #check Fin.succAbove
-- #check Fin.pred
-- #check Fin.castPred
-- #check Fin.predAbove
-- #check Fin.succAboveCases
-- #check Fin.removeNth

variable {α : Type} {n : ℕ}

-- #check Fin.succAboveCases (α := (fun _ => α)) (n := n)

def remove_index' (i : Fin (n + 1)) (f: Fin (n + 1) → α) (j : Fin n) : α  := f (Fin.succAbove i j)

def remove_index := @Fin.removeNth

def Fin.insert' (i : Fin (n + 1)) (a : α) (f : Fin n → α) (j : Fin (n + 1)) : α := Fin.succAboveCases i a f j

def Fin.insert := @Fin.insertNth

-- #check Fin.insertNth

section

variable (i : Fin (n + 1)) (a : α) (f : Fin n → α) (j : Fin (n + 1))

end
def recover_index (i : Fin (n + 1)) (k: Fin n) (f: Fin n → α):
  (Fin (n + 1) → α) := Fin.insertNth i (f k) f


def recover_value' (i : Fin (n + 1)) (x : α) (f: Fin n → α) :
 (Fin (n + 1) → α) := Fin.insertNth i x f

def recover_value := @Fin.insertNth

theorem remove_insert (i : Fin (n + 1)) (f: Fin n → α) :
  remove_index i (Fin.insert i a f) = f := by
  ext x
  -- simp_all[remove_index, Fin.insert, Fin.succAboveCases, Fin.succAbove, Fin.removeNth]
  simp_all only [remove_index, Fin.removeNth, Fin.insert,
    Fin.insertNth_apply_succAbove]


  -- split; simp_all only [Fin.insertNth, Fin.succAboveCases, Fin.castPred_castSucc, dite_eq_ite, ite_eq_else, Fin.castSucc, Fin.castAdd, Fin.castLE, Fin.castPred, Fin.castLT]
  -- . intro h
  --   omega
  -- . split
  --   . rename_i h h'
  --     simp_all [Fin.succ, Fin.castSucc, Fin.castAdd, Fin.castLE]
  --     have : i.val ≤ x.val := by
  --       -- Hard, need aesop
  --       subst h'
  --       simp_all only [Fin.mk_le_mk, add_le_iff_nonpos_right, nonpos_iff_eq_zero, one_ne_zero]
  --     have : x.val + 1 = i := by
  --       subst h'
  --       simp_all only [Fin.mk_le_mk, add_le_iff_nonpos_right, nonpos_iff_eq_zero, one_ne_zero]
  --     omega
  --   . split; simp_all only [Fin.succ, Nat.succ_eq_add_one, Fin.castPred, Fin.castLT_mk]
  --     . rename_i h h' h'''
  --       have : x.val + 1 < i.val := by
  --         simp_all only [not_lt]
  --         exact h'
  --       have : ¬ x.val < i := by
  --         simp_all only [not_lt]
  --         exact h
  --       omega
  --     . simp only [Fin.pred_succ]

theorem insert_remove (i : Fin (n + 1)) (a : α) (f: Fin (n + 1) → α) (hf: f i = a) :
  Fin.insert i a (remove_index i f) = f := by
  -- rw[remove_index]
  ext x
  simp_all[remove_index, Fin.insert,Function.update]

  -- split
  -- .
  --   rename_i h
  --   subst hf h
  --   rfl
  -- . split
  --   . subst hf
  --     rfl
  --   . split <;> simp_all only [Fin.castSucc, Fin.castAdd, Fin.castLE, Fin.pred, Fin.coe_subNat]
  --     . have: x.val - 1 < i.val := by
  --         rename_i h_2
  --         subst hf
  --         exact h_2
  --       omega
