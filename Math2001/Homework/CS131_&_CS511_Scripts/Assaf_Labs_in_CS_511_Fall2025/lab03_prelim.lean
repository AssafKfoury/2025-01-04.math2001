/- 17 September 2025 -/
/- SEVERAL EXERCISES WITH INDUCTION -/

import Mathlib.Data.Real.Basic
import Library.Tactic.ModEq
import Library.Basic

math2001_init
namespace Nat

example (n : ℕ) : 2 ^ n ≥ n + 1 := by
  sorry

example {n : ℕ} (hn : 2 ≤ n) : (3:ℤ) ^ n ≥ 2 ^ n + 5 := by
  sorry

theorem problem1 (n : ℕ) : 3 ^ n ≥ n ^ 2 + n + 1 := by
  sorry

theorem problem2 : forall_sufficiently_large n : ℕ, 2 ^ n ≥ n ^ 2 + 4 := by
  sorry
