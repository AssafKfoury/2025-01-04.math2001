/- # 20 November 2025 -/

/- # We examine the rate of growth of the Fibonnaci function (called Fib here)
   # by comparing it with the factorial function (called Fact2 here) and the
   # exponential functions 2ⁿ and (3/2)ⁿ. Basically, we show:
   #      (3/2)ⁿ < Fib (n) < 2ⁿ < Fact2 (n)
   # More precisely, regarding the first inequality, we show that:
   #      (3/2)^(n-2) ≤ Fib (n) for all n ≥ 2 or equivalently
   #      3^(n-2) ≤ 2^(n-2) * Fib (n) for all n ≥ 2 or equivalently
   #      3^n ≤ 2^n * Fib (n + 2) for all n ≥ 0
   # All the proofs are by induction, purposely set up in different ways
-/

import Mathlib.Data.Real.Basic
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
-- import Library.Tactic.ModEq
-- import Library.Tactic.Rel


-- import Mathlib.Data.Nat.Fib.Basic
-- import Mathlib.Data.Int.Units -- for the (-1)^n part

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

/- # Adding two odd integers returns an even integer -/
lemma odd_add_odd {x y : ℤ} : Int.Odd (x) → Int.Odd (y) →  Int.Even (x + y) := by
   intros h1 h2
   dsimp [Int.Odd] at * ; dsimp [Int.Even]
   obtain ⟨ a , h1 ⟩ := h1 ; obtain ⟨ b , h2 ⟩ := h2
   use (a + b + 1)
   rw [h1,h2]
   calc (2 * a + 1) + (2 * b + 1) = (a + a + 1) + (2 * b + 1) := by rw [two_mul]
        _ = (a + a + 1) + (b + b + 1) := by rw [two_mul]
        _ = (a + b + 1) + (a + b + 1) := by ring
        _ = 2 * (a + b + 1)           := by ring

/- # If two consecutive Fibonacci numbers are odd, the next one is even, i.e.
   # every third Fibonacci number is even -/
theorem Fib_odd_odd_even1 (n : ℕ) :
   Int.Odd (Fib n) → Int.Odd (Fib (n + 1)) →  Int.Even (Fib (n + 2)) := by
     intros h1 h2
     rw [Fib]
     exact odd_add_odd h1 h2   -- apply lemma `odd_add_odd` concludes the proof

/- # `Fib_odd_odd_even2` is a slight adjustment of `Fib_odd_odd_even1` -/
theorem Fib_odd_odd_even2 :
   (∀ (n : ℕ) , Int.Odd (Fib n) → Int.Odd (Fib (n + 1)) →  Int.Even (Fib (n + 2))) := by
     intro h0
     intros h1 h2
     rw [Fib]
     exact odd_add_odd h1 h2

/- CASSINI's IDENTITY Fib (n-1) * Fib (n+1) - (Fib (n)) ^ 2 = (-1) ^ n -/

/- # Next example is almost like `Example 6.3.4` in [MOP] but not quite, because
   # our definition of Fib 0 = 0, not Fib 0 = 1 as in [MOP] . I include it here
   # because it is closely related to Cassini's identity -/
example (n : ℕ) : Fib (n + 1) ^ 2 - Fib (n + 1) * Fib n - Fib n ^ 2 = (-1) ^ n := by
  simple_induction n with k IH
  · -- base case
    calc
      Fib 1 ^ 2 - Fib 1 * Fib 0 - Fib 0 ^ 2
        = 1 ^ 2 - 1 * 0 - 0 ^ 2   := by rw [Fib,Fib]
      _ = 1 - 0                   := by numbers
      _ = (-1) ^ 0                := by numbers
  · -- inductive step
    calc  Fib (k + 2) ^ 2 - Fib (k + 2) * Fib (k + 1) - Fib (k + 1) ^ 2
           = (Fib k + Fib (k + 1)) ^ 2 - (Fib k + Fib (k + 1)) * Fib (k + 1)
                - Fib (k + 1) ^ 2      := by rw [Fib]
         _ = - (Fib (k + 1) ^ 2 - Fib (k+1) * Fib k - Fib k^2) := by ring
         _ = -(-1) ^ k                 := by rw [IH]
         _ = (-1) ^ (k + 1)            := by ring

/- # I shift the statement of Cassini's identity by 1 so that we can start the
   # induction at n = 0 instead of n = 1: -/
theorem Fib_Cassini_id (n : ℕ) :
    Fib (n + 2) * Fib (n) - Fib (n+1) * Fib (n+1) = (-1) ^ (n+1) := by
    induction n with
    | zero =>
      calc Fib (0+2) * Fib 0 - Fib (0+1) * Fib (0+1)
                = (-1) ^ (0+1) := by exact rfl
    | succ n ih =>
      calc Fib (n+1+2) * Fib (n+1) - Fib (n+1+1) * Fib (n+1+1)
         = (Fib (n+1) + Fib (n+1+1)) * Fib (n+1) - (Fib n + Fib (n+1)) * Fib (n+1+1) := by rw [Fib,Fib]
       _ = Fib (n+1) * Fib (n+1) - Fib (n) * Fib (n+2)     := by ring
       _ = - (Fib (n+2) * Fib (n) - Fib (n+1) * Fib (n+1)) := by ring
       _ = - (-1) ^ (n+1)                                  := by rw [ih]
       _ = (-1) * (-1) ^ (n+1)                             := by ring
       _ = (-1) ^ (n+2)                                    := by ring

/- # `FibSum n` sums all the Fibonacci numbers Fib 0 + Fib 1 + ⋯ + Fib n -/
def FibSum : ℕ → ℤ
  | 0     => Fib 0
  | 1     => Fib 1
  | n + 2 => Fib (n + 2) + FibSum n

#eval Fib 1  #eval Fib 2  #eval Fib 3  #eval Fib 4  #eval Fib 5  #eval Fib 6  #eval Fib 7
/-     1.           1.           2.           3.           5.           8.           13   -/

#eval FibSum 2      -- 1
#eval FibSum 3      -- 3
#eval FibSum 4      -- 4
#eval FibSum 5      -- Fib 1 + Fib 3 + Fib 5 = 8
#eval FibSum 6      -- Fib 0 + Fib 2 + Fib 4 + Fib 6 = 0 + 1 + 3 + 8 = 12
#eval FibSum 7      -- Fib 1 + Fib 3 + Fib 5 + Fib 7 = 1 + 2 + 5 + 13 = 21
#eval FibSum 8      -- FibSum 6 + Fib 8 = 12 + 21 = 33
#eval (Fib (5)) ^ 2
#eval 2 = 2
#eval FibSum (2 * 2 + 1) = Fib (2 * 2 + 2)
#eval FibSum (2 * 3 + 1) = Fib (2 * 3 + 2)
#eval FibSum (2 * 3) = Fib (2 * 3 + 1) - 1
#eval FibSum (2 * 4) = Fib (2 * 4 + 1) - 1

/- SUM OF FIBONACCI NUMBERS -/

/- # FibSum (2 * n + 1) = Fib (2 * n + 2) for all n ≥ 0   -/
theorem FibSumOdd (n : ℕ) : FibSum (2 * n + 1) = Fib (2 * n + 2) := by sorry

/- # FibSum (2 * n) = Fib (2 * n + 1) - 1 for all n ≥ 0   -/
theorem FibSumEven (n : ℕ) : FibSum (2 * n) = Fib (2 * n + 1) - 1 := by sorry

/- DIVISIBILITY PROPERTY-/

/- # Fib (m) divides F (m * n)  for all m ≥ 1 and n ≥ 1 by induction on n  -/
theorem FibDiv (m n : ℕ) (hm : m ≥ 1) (hn : n ≥ 1) : (Fib m) ∣ (Fib m * n) :=
   by sorry

/- GROWTH RATE -/





#eval 3.0 / 2   #eval (3 : ℚ) / 2   #eval ((3:ℚ) / 2) ^ 2

/- Other nice facts about the Fibonacci can be found here:
   https://matheducators.stackexchange.com/questions/2021/what-interesting-properties-of-the-fibonacci-sequence-can-i-share-when-introduci

   Also, from the end of Section 5.4 in "Mathematics in Lean":
   example (n : ℕ): (fib n) ^ 2 + (fib (n + 1)) ^ 2 =
                                       fib (2 * n + 1) := by sorry
   https://leanprover-community.github.io/mathematics_in_lean/C05_Elementary_Number_Theory.html
-/
