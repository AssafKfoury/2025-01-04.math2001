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
  induction n with -- using Nat.twoStepInduction with
  | zero =>
      calc
      2^0 + Fib (0+2) = 1 + Fib (2) := by exact rfl
                    _ = 1 + 1       := by exact rfl
                    _ = 2           := by numbers
                    _ ≥ 3^0         := by numbers
  | succ k ik =>
      calc   sorry


/-
-- Import the Fibonacci sequence definition and standard tactics
import Mathlib.Data.Nat.Fib
import Mathlib.Tactic

-- Use the definitions from the Nat namespace
open Nat

theorem fib_inequality (n : ℕ) : 2^n * fib (n + 2) ≥ 3^n := by
  -- We use two-step induction because the Fibonacci recurrence
  -- depends on two previous values.
  induction n using Nat.twoStepInduction with
  | zero =>
    -- Base case n = 0
    -- Goal: 2^0 * fib (0 + 2) ≥ 3^0
    --       1 * fib 2       ≥ 1
    --       1 * 1           ≥ 1
    norm_num

  | one =>
    -- Base case n = 1
    -- Goal: 2^1 * fib (1 + 2) ≥ 3^1
    --       2 * fib 3       ≥ 3
    --       2 * 2           ≥ 3
    --       4               ≥ 3
    norm_num

  | step k ih_1 ih_2 =>
    -- Inductive step for n = k + 2
    -- ih_1: 2^k * fib (k + 2) ≥ 3^k
    -- ih_2: 2^(k + 1) * fib (k + 3) ≥ 3^(k + 1)
    -- Goal: 2^(k + 2) * fib (k + 4) ≥ 3^(k + 2)

    -- First, we prove the simple arithmetic inequality that
    -- 2 * 3^(k+1) + 4 * 3^k ≥ 3^(k+2)
    -- This is the 10/3 part of the paper proof, multiplied by 3
    -- (10 * 3^k ≥ 9 * 3^k)
    have h_arith : 2 * 3^(k + 1) + 4 * 3^k ≥ 3^(k + 2) := by
      rw [pow_succ, mul_assoc, ← add_mul] -- 2*3*3^k + 4*3^k = (6+4)*3^k
      norm_num -- 10 * 3^k
      rw [pow_add, pow_two, mul_comm] -- 3^2 * 3^k = 9 * 3^k
      norm_num -- Goal: 10 * 3^k ≥ 9 * 3^k
      apply Nat.mul_le_mul_right -- Prove 10 ≥ 9 (since 3^k is non-neg)
      norm_num -- 10 ≥ 9

    -- Now, we start from the LHS of our main goal and use `calc`
    calc
      2^(k + 2) * fib (k + 4)
      _ = 2^(k + 2) * (fib (k + 3) + fib (k + 2)) := by rw [fib_add_two]
      _ = 2^(k + 2) * fib (k + 3) + 2^(k + 2) * fib (k + 2) := by rw [mul_add]
      _ = 2 * (2^(k + 1) * fib (k + 3)) + 4 * (2^k * fib (k + 2)) := by
          -- Rearrange powers to match ih_1 and ih_2
          rw [pow_succ (k + 1), mul_assoc] -- 2^(k+2) = 2 * 2^(k+1)
          rw [pow_add k 2, mul_assoc]      -- 2^(k+2) = 2^2 * 2^k
          rw [show (2^2 : ℕ) = 4 by rfl, rfl]
      _ ≥ 2 * 3^(k + 1) + 4 * 3^k := by
          -- Apply the two induction hypotheses
          apply add_le_add
          · -- 2 * (2^(k+1) * fib(k+3)) ≥ 2 * 3^(k+1)
            apply mul_le_mul_of_nonneg_left ih_2
            norm_num
          · -- 4 * (2^k * fib(k+2)) ≥ 4 * 3^k
            apply mul_le_mul_of_nonneg_left ih_1
            norm_num
      _ ≥ 3^(k + 2) := by
          -- Apply the arithmetic lemma we proved
          exact h_arith


-/
