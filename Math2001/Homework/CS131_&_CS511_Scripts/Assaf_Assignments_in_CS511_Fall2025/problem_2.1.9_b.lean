import Mathlib.Data.Real.Basic
import Library.Tactic.ModEq
import Library.Basic

math2001_init
namespace Nat

example {n : ℕ} (hn : n ^ 2 + 4 = 4 * n) : n = 2 := by
  have h1 :=
  calc (n - 2) ^ 2 = n ^ 2 + 4 - 4 * n := by ring
                _  = 4 * n - 4 * n := by rw [hn]
                _  = 0 := by ring
                _  = 0 ^ 2 := by ring
  have h2 :=
  calc (n - 2) = 0 := by cancel 2 at h1

  /-
  calc
    n = (n - 2) + 2 := by ring
    _ = 0 + 2     := by rw[h2] --rw [←h2]
    _ = 2         := by ring
  -/
