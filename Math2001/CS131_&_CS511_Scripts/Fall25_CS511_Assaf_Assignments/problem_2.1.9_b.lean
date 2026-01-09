import Mathlib.Data.Real.Basic
import Library.Tactic.ModEq
import Library.Basic

math2001_init
namespace Nat

example {n : ℤ} (hn : n ^ 2 + 4 = 4 * n) : n = 2 := by
  have h : (n-2)^2 = 0^2 := by
    calc (n - 2) ^ 2 = n ^ 2 + 4 - 4 * n := by ring
                _  = 4 * n - 4 * n := by rw [hn]
                _  = 0 := by ring
                _  = 0 ^ 2 := by ring
  cancel 2 at h
  calc n = 2 + (n - 2) := by ring
       _ = 2 + 0 := by rw [h]
       _ = 2 := by ring
--  addarith [h]

#eval (3 : ℕ) ^ 2
#eval (3 : ℤ) ^ 2
