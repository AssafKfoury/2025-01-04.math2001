import Mathlib.Data.Real.Basic
import Library.Basic

import Mathlib.Data.Nat.Fib.Basic

math2001_init
open Nat

#check fib 3

theorem cassini_identity_final (n : Nat) (hn : n ≥ 1) :
    (fib (n + 1) * fib (n - 1) : ℤ) - (fib n * fib n : ℤ) = (((-1) ^ n) : ℤ)  := by
  induction_from_starting_point n, hn with k hk IH
  · -- base case
    norm_num
  · -- inductive step
    have general_id :
      (fib (k + 2) * fib k : ℤ) - (fib (k + 1) * fib (k + 1) : ℤ) =
      -((fib (k + 1) * fib (k - 1) : ℤ) - (fib k * fib k : ℤ)) := by
      -- Expand terms and use ring to prove the algebraic equality
      rw [fib_add_two, fib_add_two (k - 1)] -- requires k >= 1, provided by hk
      push_cast
      ring

    rw [general_id, ih]
    exact Int.neg_eq_neg_one_mul_self_pow k
