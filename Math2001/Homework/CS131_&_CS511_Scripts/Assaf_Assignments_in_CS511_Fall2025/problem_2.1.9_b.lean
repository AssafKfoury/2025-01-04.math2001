import Mathlib.Data.Real.Basic
import Library.Tactic.ModEq
import Library.Basic

math2001_init
namespace Nat

example {n : ℕ} (hn : n ^ 2 + 4 = 4 * n) : n = 2 := by
  have h1 :=
  calc (n - 2) ^ 2 = n ^ 2 + 4 - 4 * n := by ring
                   = (n ^ 2 + 4) - (4 * n) := by ring

  --             = 4*n - 4*n := by rw [hn]
  have h2 :=
  calc
  --           = 4*n - 4*n := by rw [hn]



/-
:=
  calc
    a ^ 2 = b ^ 2 + 1 := by rw [h1]
    _ ≥ 1 := by extra
    _ = 1 ^ 2 := by ring
  cancel 2 at h3

-/
