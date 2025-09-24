/- 24 September 2025 -/
/- from Macbeth Sect 6.02: two examples -/
/- from ps7.lean in CS 131 Spring 2025: two theorems -/
/- SEVERAL EXERCISES WITH INDUCTION -/

import Mathlib.Tactic.GCongr
import Library.Basic
import Library.Tactic.ModEq

math2001_init

namespace Int

/- From Example 6.2.1 in 06_Induction in Macbeth's -/
def b : ℕ → ℤ
  | 0 => 3
  | n + 1 => b n ^ 2 - 2
/- it's cleaner to include the parentheses in the recursive call: -/
def bb : ℕ → ℤ
  | 0 => 3
  | n + 1 => (bb n) ^ 2 - 2
/- Show that for all n, (bb n) is odd -/
example (n : ℕ) : Odd (bb n) := by
  simple_induction n with k hk
  · -- base case
    dsimp [Odd] -- 'Odd' is defined in Example 3.1.1
    use 1
    calc bb 0 = 3 := by rw [bb]
      _ = 2 * 1 + 1 := by numbers
  · -- inductive step
    dsimp [Odd] at * -- unwind the defn of 'Odd' everywhere
    obtain ⟨x, hx⟩ := hk
    use 2 * x ^ 2 + 2 * x - 1
    calc bb (k + 1) = (bb k) ^ 2 - 2 := by rw [bb]
      _ = (2 * x + 1) ^ 2 - 2 := by rw [hx]
      _ = 2 * (2 * x ^ 2 + 2 * x - 1) + 1 := by ring

/- From Example 6.2.3 in 06_Induction in Macbeth's -/
def x : ℕ → ℤ
  | 0 => 5
  | n + 1 => 2 * (x n) - 1
example (n : ℕ) : x n = 2 ^ (n + 2) + 1 := by
  simple_induction n with k IH
  · -- base case
    calc x 0 = 5 := by rw [x]
      _ = 2 ^ (0 + 2) + 1 := by numbers
  · -- inductive step
    calc x (k + 1) = 2 * (x k) - 1 := by rw [x]
      _ = 2 * (2 ^ (k + 2) + 1) - 1 := by rw [IH]
      _ = 2 ^ ((k + 1) + 2) + 1 := by ring
