/- 17 September 2025 -/
/- from Macbeth Sect 6.01: two examples -/
/- from ps7.lean in CS 131 Spring 2025: two theorems -/
/- SEVERAL EXERCISES WITH INDUCTION -/

import Mathlib.Data.Real.Basic
import Library.Tactic.ModEq
import Library.Basic

math2001_init

namespace Nat

example (n : ℕ) : 2 ^ n ≥ n + 1 := by
  simple_induction n with k IH
  · -- base case
    numbers
  · -- inductive step
    calc 2 ^ (k + 1) = 2 * 2 ^ k := by ring
      _ ≥ 2 * (k + 1) := by rel [IH]
      _ = (k + 1 + 1) + k := by ring
      _ ≥ k + 1 + 1 := by extra

example {n : ℕ} (hn : 2 ≤ n) : (3:ℤ) ^ n ≥ 2 ^ n + 5 := by
  induction_from_starting_point n, hn with k hk IH
  · -- base case
    numbers
  · -- inductive step
    calc (3:ℤ) ^ (k + 1) = 2 * 3 ^ k + 3 ^ k := by ring
      _ ≥ 2 * (2 ^ k + 5) + 3 ^ k := by rel [IH]
      _ = 2 ^ (k + 1) + 5 + (5 + 3 ^ k) := by ring
      _ ≥ 2 ^ (k + 1) + 5 := by extra

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
