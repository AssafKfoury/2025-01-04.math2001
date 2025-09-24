/- 24 September 2025 -/
/- from Macbeth Sect 6.02 in Chapt 6: three examples -/
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

/- From Example 6.2.6 in 06_Induction in Macbeth's -/
def factorial : ℕ → ℕ
  | 0 => 1
  | n + 1 => (n + 1) * factorial n

notation:10000 n "!" => factorial n

example (n : ℕ) : (n + 1)! ≥ 2 ^ n := by
  simple_induction n with k IH
  · -- base case
    calc (0 + 1)! = (0 + 1) * 0! := by rw [factorial, factorial, factorial]
      _ = (0 + 1) * 1 := by rw [factorial]
      _ ≥ 2 ^ 0 := by numbers
  · -- inductive step
    calc (k + 1 + 1)! = (k + 1 + 1) * (k + 1)! := by rw [factorial]
      _ ≥ (k + 1 + 1) * 2 ^ k := by rel [IH]
      _ = k * 2 ^ k + 2 * 2 ^ k := by ring
      _ ≥ 2 * 2 ^ k := by extra
      _ = 2 ^ (k + 1) := by ring
