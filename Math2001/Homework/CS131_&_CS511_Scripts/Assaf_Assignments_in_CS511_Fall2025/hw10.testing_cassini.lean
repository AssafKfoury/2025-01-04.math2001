-- import Mathlib
import Mathlib.Data.Real.Basic
import Library.Basic

-- import Mathlib.Data.Nat.Lemmas -- Required to access Nat.twoStepInduction




-- import Mathlib.Data.Nat.Fib.Basic

math2001_init
open Nat

open Nat

/- # Fibonacci function -/
def Fib : ℕ → ℤ -- ℕ
   | 0 => 0 -- sometimes `Fib 0` is defined as returning value `1`
   | 1 => 1
   | n + 2 => Fib (n) + Fib (n+1)

-- Example function (similat to Fibonacci)
def a : ℕ → ℤ
  | 0 => 2
  | 1 => 1
  | n + 2 => a (n + 1) + 2 * a n

/- Same example as Example 6.3.1 in [MOP] -/
example (n : ℕ) : a n = 2 ^ n + (-1) ^ n := by
  induction' n using Nat.twoStepInduction with k IH1 IH2
  . calc a 0 = 2                := by rw [a]
           _ = 2 ^ 0 + (-1) ^ 0 := by rfl -- or `by numbers` or `by norm_num`
  . calc a 1 = 1                := by rw [a]
           _ = 2 ^ 1 + (-1) ^ 1 := by rfl
  . calc
      a (k + 2)
        = a (k + 1) + 2 * a k                       := by rw [a]
      _ = (2^(k+1) + (-1)^(k+1)) + 2*(2^k + (-1)^k) := by rw [IH1, IH2]
      _ = (2 : ℤ) ^ (k+2) + (-1) ^ (k+2)            := by ring

/- Same as the preceding two-step-induction but now using induction
   instead of induction' and a little less transparently -/
example (n : ℕ) : a n = 2 ^ n + (-1) ^ n := by
  induction n using Nat.twoStepInduction
  . rfl
  . rfl
  . case _ k ik1 ik2 => calc
    a (k + 2) = a (k + 1) + 2 * a k := rfl
    _ = (2 ^ (k + 1) + (-1) ^ (k + 1)) + 2 * (2 ^ k + (-1) ^ k) := by rw [ik1, ik2]
    _ = 2 ^ (k + 2) + (-1) ^ (k + 2) := by ring

/- The preceding example once more, but without using Nat.twoStepInduction -/
example (n : ℕ) : a n = 2 ^ n + (-1) ^ n := by
  -- prove the `n` and `n+1` cases simultaneously by induction
  have aux_lemma :
      a n = 2 ^ n + (-1) ^ n ∧
      a (n + 1) = 2 ^ (n + 1) + (-1) ^ (n + 1) := by
    induction n with
    | zero =>
      constructor
      . rfl
      . rfl
    | succ k ik =>
      constructor
      . exact ik.2
      . calc
        a (k + 2) = a (k + 1) + 2 * (a k) := rfl
        _ = 2 ^ (k + 1) + (-1) ^ (k + 1) + 2 * (2 ^ k + (-1) ^ k) := by rw [ik.1, ik.2]
        _ = 2 ^ (k + 2) + (-1) ^ (k + 2) := by ring
  -- we just need the `n` case in the end
  exact aux_lemma.1

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
