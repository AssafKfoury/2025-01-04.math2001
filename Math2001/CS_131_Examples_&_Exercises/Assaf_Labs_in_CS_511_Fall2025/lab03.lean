/- 17 September 2025 -/
/- SEVERAL EXERCISES WITH INDUCTION -/

import Mathlib.Data.Real.Basic
import Library.Tactic.ModEq
import Library.Basic

theorem problem1 (n : ℕ) : 3 ^ n ≥ n ^ 2 + n + 1 := by
  simple_induction n with k IH
  · numbers
  · calc
      3 ^ (k + 1) = 3 * 3 ^ k := by ring
      _ ≥ 3 * (k ^ 2 + k + 1) := by rel [IH]
      _ = (k + 1) ^ 2 + (k + 1) + 1 + 2 * k ^ 2 := by ring
      _ ≥ (k + 1) ^ 2 + (k + 1) + 1 := by extra

theorem problem2 : forall_sufficiently_large n : ℕ, 2 ^ n ≥ n ^ 2 + 4 := by
  dsimp
  use 5
  intros x hx
  induction_from_starting_point x, hx with k hk IH
  · numbers
  · calc
      2 ^ (k + 1) = 2 * 2 ^ k := by ring
      _ ≥ 2 * (k ^ 2 + 4) := by rel [IH]
      _ = k ^ 2 + 4 + k * k + 4 := by ring
      _ ≥ k ^ 2 + 4 + 5 * k + 4 := by rel [hk]
      _ = k ^ 2 + 2 * k + 5 + (3 * k + 3) := by ring
      _ ≥ k ^ 2 + 2 * k + 5 + (3 * 5 + 3) := by rel [hk]
      _ ≥ k ^ 2 + 2 * k + 5 := by extra
      _ = (k + 1) ^ 2 + 4 := by ring
