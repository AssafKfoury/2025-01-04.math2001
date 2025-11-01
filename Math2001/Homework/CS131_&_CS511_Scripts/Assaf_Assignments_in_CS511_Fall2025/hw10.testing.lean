-- import Mathlib.Data.Real.Basic
-- import Mathlib.Data.Nat.Basic
-- import Mathlib.Data.Nat.Fib.Basic
-- import Mathlib.Data.Nat.Parity
-- import Mathlib.Tactic.GCongr
-- import Library.Basic
-- import Library.Tactic.ModEq
-- import Mathlib.Data.Nat.Parity

-- import Mathlib.Tactic.GCongr
-- import Mathlib.Data.Nat.Parity
import Library.Basic
import Library.Tactic.ModEq
-- import Mathlib.Data.Real.Basic
import Library.Basic

math2001_init

open Nat

/- # Fibonacci function -/
def myFib : ℕ → ℕ
   | 0 => 0
   | 1 => 1
   | n + 2 => myFib (n) + myFib (n+1)

/- # Factorial function -/
def myFact : ℕ → ℕ
   | 0 => 1
   | n + 1 => (n + 1) * myFact n

lemma myFib_add_two {x : ℕ} : myFib (x+2) = myFib (x) + myFib (x+1) :=
  calc myFib (x+2) = myFib (x) + myFib (x+1) := by rw [myFib]

lemma odd_add_odd {x y : ℕ} : Odd (x) → Odd (y) →  Even (x + y) := by
   intros h1 h2
   dsimp [Odd] at * ; dsimp [Even]
   obtain ⟨ a , h1 ⟩ := h1 ; obtain ⟨ b , h2 ⟩ := h2
   use (a + b + 1)
   rw [h1,h2]
   calc (2 * a + 1) + (2 * b + 1) = (a + a + 1) + (2 * b + 1) := by rw [two_mul]
        _ = (a + a + 1) + (b + b + 1) := by rw [two_mul]
        _ = (a + b + 1) + (a + b + 1) := by ring
        _ = 2 * (a + b + 1) := by ring

/- # `fact_overtakes_exp` is the same as Example 6.2.6 in Macbeth's -/
lemma fact_overtakes_exp (n : ℕ) :  myFact (n+1) ≥ 2 ^ n := by
  induction n with
  | zero =>
    calc myFact (0+1) = (0+1) * myFact 0 := by rw [myFact,myFact,myFact]
         _ = (0+1) * 1 := by rw [myFact]
         _ ≥ 2 ^ 0 := by numbers
  | succ n ih =>
    calc myFact (n+1+1) = (n+1+1) * (myFact (n+1)) := by rw [myFact]
         _ ≥ (n+1+1) * (2 ^ n) := by exact mul_le_mul_left (n + 1 + 1) ih
         _ = n * 2 ^ n + 2 * 2 ^ n := by ring
         _ ≥ 2 * 2 ^ n := by extra
         _ = 2 ^ (n + 1) := by exact IsSymmOp.symm_op 2 (2 ^ n)

/-- # If two consecutive Fibonacci numbers are odd, the next one is even. -/
theorem fib_odd_odd_even (n : Nat) :
   Odd (myFib n) → Odd (myFib (n + 1)) →  Even (myFib (n + 2)) := by
     intros h1 h2
     rw [myFib_add_two]        -- rewrite conclusion using lemma `myFib_add_two`
     exact odd_add_odd h1 h2   -- apply lemma `odd_add_odd` to conclude the proof

-- A simple example to check the theorem works for a small number.
#check fib_odd_odd_even 3
#check fib_odd_odd_even 1 (by decide) (by decide)
-- Lean confirms that `Even (fib 3)`, which is true (1, 1, 2, ...).
