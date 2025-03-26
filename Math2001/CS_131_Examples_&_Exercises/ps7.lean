import Mathlib.Data.Real.Basic
import Library.Tactic.ModEq
import Library.Basic
import AutograderLib

/-
Suggested starting steps:
  simple_induction n with k IH
-/

@[autogradedProof 10]
theorem problem1 (n : ℕ) : 3 ^ n ≥ n ^ 2 + n + 1 := by
  sorry

/-
Suggested starting steps:
  dsimp
  use 5
  intros x hx
  induction_from_starting_point x, hx with k hk IH
-/

@[autogradedProof 15]
theorem problem2 : forall_sufficiently_large n : ℕ, 2 ^ n ≥ n ^ 2 + 4 := by
  sorry
