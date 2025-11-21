/- # 20 November 2025 -/

/- # We examine the rate of growth of the Fibonnaci function (called Fib here)
   # by comparing it with the factorial function (called Fact2 here) and the
   # exponential functions 2ⁿ and (3/2)ⁿ. Basically, we show:
   #      (3/2)ⁿ < Fib (n) < 2ⁿ < Fact2 (n)
   # More precisely, regarding the first inequality, we show that:
   #      (3/2)^(n-2) ≤ Fib (n) for all n ≥ 2 or equivalently
   #      3^(n-2) ≤ 2^(n-2) * Fib (n) for all n ≥ 2 or equivalently
   #      3^n ≤ 2^n * Fib (n + 2) for all n ≥ 0
   # All the proofs are by induction, purposely set up in different ways.
-/

import Mathlib.Data.Real.Basic
import Library.Basic

math2001_init
open Nat

/- # Fibonacci function -/
def Fib : ℕ → ℤ -- ℕ
   | 0 => 0 -- sometimes `Fib 0` is defined as returning value `1`
   | 1 => 1
   | n + 2 => Fib (n) + Fib (n+1)

/- # Factorial function -/
def Fact2 : ℕ → ℕ
   | 0 => 1
   | n + 1 => (n + 1) * Fact2 n

/- # `Fact_overtakes_Exp1` is the same as Example 6.2.6 in Macbeth's -/
theorem Fact_overtakes_Exp1 (n : ℕ) :  Fact2 (n+1) ≥ 2 ^ n := by
  induction n with
  | zero =>
    calc Fact2 (0+1) = (0+1) * Fact2 0 := by exact rfl -- `rw [Fact2,Fact2,Fact2]` also works
         _ = (0+1) * 1                 := by exact rfl -- `rw [Fact2]` also works
         _ ≥ 2 ^ 0                     := by numbers
  | succ n ih =>
    calc Fact2 (n+1+1) = (n+1+1) * (Fact2 (n+1)) := by rw [Fact2]
         _ ≥ (n+1+1) * (2 ^ n) := by exact mul_le_mul_left (n + 1 + 1) ih
         _ = n * 2 ^ n + 2 * 2 ^ n := by ring
         _ ≥ 2 * 2 ^ n := by extra
         _ = 2 ^ (n + 1) := by ring

/- # `Fact_overtakes_Exp2` is the same as `Fact_overtakes_Exp1` but its
   #  proof by induction is set up differently -/
theorem Fact_overtakes_Exp2 (n : ℕ) : Fact2 (n + 1) ≥ 2 ^ n := by
  simple_induction n with k IH
  · -- base case
    calc Fact2 (0 + 1) = (0 + 1) * Fact2 0 := by rw [Fact2, Fact2, Fact2]
      _ = (0 + 1) * 1 := by rw [Fact2]
      _ ≥ 2 ^ 0 := by numbers
  · -- inductive step
    calc Fact2 (k + 1 + 1) = (k + 1 + 1) * Fact2 (k + 1) := by rw [Fact2]
      _ ≥ (k + 1 + 1) * 2 ^ k := by exact mul_le_mul_left (k + 1 + 1) IH
                     -- in the previous step, `rel [IH]` does not work ???
      _ = k * 2 ^ k + 2 * 2 ^ k := by ring
      _ ≥ 2 * 2 ^ k := by extra
      _ = 2 ^ (k + 1) := by ring

/- # `Exp_overtakes_Fib` , same as Example 6.3.3 in [MOP] -/
theorem Exp_overtakes_Fib (n : ℕ) : Fib n ≤ 2 ^ n := by
  two_step_induction n with k IH1 IH2
  · calc Fib 0 = 0     := by rw [Fib]
             _ ≤ 2 ^ 0 := by numbers
  · calc Fib 1 = 1     := by rw [Fib]
             _ ≤ 2 ^ 1 := by numbers
  · calc Fib (k + 2) = Fib (k) + Fib (k+1) := by rw [Fib]
                   _ ≤ 2 ^ k + 2 ^ (k+1)   := by rel [IH1,IH2]
    -- in previous step, `exact Int.add_le_add IH1 IH2`instead of `rel[IH1,IH2]` works
                   _ ≤ 2 ^ k + 2 ^ k + 2 ^ (k+1)   := by extra
                   _ = 2 ^ (k + 2)                 := by ring

/- # Fib_overtakes_SlowExp -/
theorem Fib_overtakes_SlowExp (n : ℕ) : (2 ^ n) * Fib (n + 2) ≥ 3 ^ n := by
  induction' n using Nat.twoStepInduction with k IH1 IH2
  · calc 2^0 * Fib (0+2)
             = 1 * Fib (2) := by exact rfl  -- or `by rfl`
          _  = 1 * 1       := by exact rfl  -- or `by rfl`
          _  ≥ 3^0         := by numbers    -- or `by exact Int.le_refl (3 ^ 0)`
  · calc 2^1 * Fib (1+2)
             = 2 * Fib (3) := by rfl
          _  = 2 * 2       := by rfl
          _  = 4           := by numbers
          _  ≥ 3^1         := by numbers
  · calc 2^(k+2) * Fib (k+2+2)
                 = 2^(k+2) * (Fib (k+2) + Fib (k+2+1))           := by rw [Fib]
              _  = 2^(k+2) * Fib (k+2) + 2^(k+2) * Fib (k+3)     := by ring
              _  = 2^2 * (2^k * Fib (k+2)) + 2 * (2^(k+1) * Fib (k+3)) := by ring
              _  ≥ 2^2 * 3^k + 2 * 3^(k+1)                       := by rel [IH1,IH2]
              _  = 4 * 3^k + 2 * 3^(k+2) - 12 * 3^k              := by ring
              _  = 2 * 3^(k+2) - 8 * 3^k                         := by ring
              _  = 3^(k+2) + 9 * 3^k - 8 * 3^k                   := by ring
              _  = 3^(k+2) + 3^k                                 := by ring
              _  ≥ 3^(k+2)                                       := by extra
