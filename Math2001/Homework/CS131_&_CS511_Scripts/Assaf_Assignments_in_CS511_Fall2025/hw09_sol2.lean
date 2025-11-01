import Mathlib.Data.Real.Basic
import Library.Basic           -- needed for math2001_init
import Library.Tactic.Rel

-- import Library.Tactic.Induction
-- import Library.Tactic.Extra
-- import Mathlib.Tactic.FieldSimp
-- import Mathlib.Tactic.GCongr

math2001_init          -- needed to access Macbeth's tactics:
                       -- `addarith`, `cancel`, `extra`, `numbers`

open Nat

def pascal : ℕ → ℕ → ℕ
  | a, 0 => 1
  | 0, b + 1 => 1
  | a + 1, b + 1 => pascal (a + 1) b + pascal a (b + 1)
termination_by _ a b => a + b

#check pascal


/- # Exercise 6.5.4.1 in Macbeth's [MOP] -/
theorem pascal_symm (m n : ℕ) : pascal m n = pascal n m := by
  match m, n with
  | 0, 0 => ring
  | a + 1, 0 => rw [pascal, pascal]
  | 0, b + 1 => rw [pascal, pascal]
  | a + 1, b + 1 =>
    have IH1 := pascal_symm (a + 1) b
    have IH2 := pascal_symm a (b + 1)
    calc pascal (a + 1) (b + 1) = pascal (a + 1) b + pascal a (b + 1) := by rw [pascal]
      _ = pascal b (a + 1) + pascal (b + 1) a := by rw [IH1, IH2]
      _ = pascal (b + 1) a + pascal b (a + 1) := by ring
      _ = pascal (b + 1) (a + 1) := by rw [pascal]
termination_by _ a b => a + b

/- # Exercise 6.5.4.2 in Macbeth's [MOP] -/
example (a : ℕ) : pascal a 1 = a + 1 := by
  simple_induction a with k IH
  · rw [pascal]
  · calc pascal (k + 1) 1 = pascal (k + 1) 0 + pascal k 1 := by rw [pascal, pascal, pascal]
      _ = 1 + (k + 1) := by rw [pascal, IH]
      _ = k + 1 + 1 := by ring
