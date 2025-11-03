
open Nat

/-- Cassini's Identity for Fibonacci numbers.
    F_{n+1} * F_{n-1} - F_n^2 = (-1)^n for n >= 1. -/
theorem cassini_identity_final (n : Nat) (h : n ≥ 1) :
    (fib (n + 1) * fib (n - 1) : Int) - (fib n * fib n : Int) = (-1) ^ (n : Int) := by
  induction n using Nat.le_induction with
  | base =>
    simp [fib_zero, fib_one, fib_two]
    norm_num
  | succ k hk ih =>
    have general_id :
      (fib (k + 2) * fib k : Int) - (fib (k + 1) * fib (k + 1) : Int) =
      -((fib (k + 1) * fib (k - 1) : Int) - (fib k * fib k : Int)) := by
      -- Expand terms and use ring to prove the algebraic equality
      rw [fib_add_two, fib_add_two (k - 1)] -- requires k >= 1, provided by hk
      push_cast
      ring

    rw [general_id, ih]
    exact Int.neg_eq_neg_one_mul_self_pow k
