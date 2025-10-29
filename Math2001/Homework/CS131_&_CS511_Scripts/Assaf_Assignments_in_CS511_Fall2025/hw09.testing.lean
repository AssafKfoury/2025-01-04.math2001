import Mathlib.Data.Nat.Fib.Basic
import Mathlib.Data.Nat.Parity

-- import Mathlib.Tactic.GCongr
-- import Library.Basic
-- import Library.Tactic.ModEq

-- math2001_init

open Nat

-- Assaf testing:
#eval Odd (4)
#eval fib (3)
#check fib_add_two
-- #check Nat.odd_add_odd
#eval (fib (5) = fib (3) + fib (4))

def myFib : ℕ → ℕ
   | 0 => 0
   | 1 => 1
   | n + 2 => myFib (n) + myFib (n+1)

/- From Example 6.2.6 in 06_Induction in Macbeth's -/
def myFact : ℕ → ℕ -- factorial : ℕ → ℕ
  | 0 => 1
  | n + 1 => (n + 1) * myFact n -- factorial n

notation:10000 n "!" => myFact n -- factorial n

lemma myFib_add_two {x : ℕ} : myFib (x+2) = myFib (x) + myFib (x+1) :=
  calc myFib (x+2) = myFib (x) + myFib (x+1) := by rw [myFib]

lemma odd_add_odd_is_even

#eval myFib 14
#eval fib 14
/-
example (n : ℕ) : (n + 1)! ≥ 2 ^ n := by
  simple_induction n with k IH
  · -- base case
    calc (0 + 1)! = (0 + 1) * 0! := by rw [factorial, factorial, factorial]
      _ = (0 + 1) * 1 := by rw [factorial]
      _ ≥ 2 ^ 0 := by numbers
  · -- inductive step
    calc (k + 1 + 1)! = (k + 1 + 1) * (k + 1)! := by rw [factorial]
      _ ≥ (k + 1 + 1) * 2 ^ k := by rel [IH]
      _ = k * 2 ^ k + 2 * 2 ^ k := by ring
      _ ≥ 2 * 2 ^ k := by extra
      _ = 2 ^ (k + 1) := by ring
-/

/- # =============================================== -/

/-- If two consecutive Fibonacci numbers are odd, the next one is even. -/
theorem fib_odd_odd_even (n : Nat) (h_odd_n : Odd (fib n)) (h_odd_n_plus_1 : Odd (fib (n + 1))) :
  Even (fib (n + 2)) := by
  -- The `fib_add_two` lemma states `fib (n + 2) = fib n + fib (n + 1)`.
  -- We apply this to rewrite the goal.
  rw [fib_add_two]
  -- The `odd_add_odd` lemma proves that the sum of two odd numbers is even.
  -- We apply this with our hypotheses.
  exact odd_add_odd h_odd_n h_odd_n_plus_1

-- A simple example to check the theorem works for a small number.
#check fib_odd_odd_even 1 (by decide) (by decide)
-- Lean confirms that `Even (fib 3)`, which is true (1, 1, 2, ...).
