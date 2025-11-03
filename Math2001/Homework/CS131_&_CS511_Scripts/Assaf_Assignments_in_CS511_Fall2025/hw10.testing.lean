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

#check Int.Odd

/- # Fibonacci function -/
def Fib : ℕ → ℤ -- ℕ
   | 0 => 0
   | 1 => 1
   | n + 2 => Fib (n) + Fib (n+1)

/- # Factorial function -/
def Fact2 : ℕ → ℕ
   | 0 => 1
   | n + 1 => (n + 1) * Fact2 n

/- # Fibonacci as defiend in [MOP, Example 6.3]
def F : ℕ → ℤ
  | 0 => 1                     -- note the difference: this is 1, not 0
  | 1 => 1
  | n + 2 => F (n + 1) + F n
-/

/- # Exp_overtakes_Fib -/
lemma Exp_overtakes_Fib (n : ℕ) : Fib n ≤ 2 ^ n := by
  two_step_induction n with k IH1 IH2
  · calc Fib 0 = 0     := by rw [Fib]
             _ ≤ 2 ^ 0 := by numbers
  · calc Fib 1 = 1     := by rw [Fib]
             _ ≤ 2 ^ 1 := by numbers
  · calc Fib (k + 2) = Fib (k) + Fib (k+1) := by rw [Fib]
                   _ ≤ 2 ^ k + 2 ^ (k+1)   := by exact Int.add_le_add IH1 IH2
         -- in the previous step, `rel [IH1,IH2]` does not work for some reason ...
                   _ ≤ 2 ^ k + 2 ^ k + 2 ^ (k+1)   := by extra
                   _ = 2 ^ (k + 2)                 := by ring

lemma Fib_add_two {x : ℕ} : Fib (x+2) = Fib (x) + Fib (x+1) :=
  calc Fib (x+2) = Fib (x) + Fib (x+1) := by rw [Fib]

lemma odd_add_odd {x y : ℤ} : Int.Odd (x) → Int.Odd (y) →  Int.Even (x + y) := by
   intros h1 h2
   dsimp [Int.Odd] at * ; dsimp [Int.Even]
   obtain ⟨ a , h1 ⟩ := h1 ; obtain ⟨ b , h2 ⟩ := h2
   use (a + b + 1)
   rw [h1,h2]
   calc (2 * a + 1) + (2 * b + 1) = (a + a + 1) + (2 * b + 1) := by rw [two_mul]
        _ = (a + a + 1) + (b + b + 1) := by rw [two_mul]
        _ = (a + b + 1) + (a + b + 1) := by ring
        _ = 2 * (a + b + 1) := by ring

/- # `Fact_overtakes_Exp` is the same as Example 6.2.6 in Macbeth's -/
lemma Fact_overtakes_Exp1 (n : ℕ) :  Fact2 (n+1) ≥ 2 ^ n := by
  induction n with
  | zero =>
    calc Fact2 (0+1) = (0+1) * Fact2 0 := by rw [Fact2,Fact2,Fact2]
         _ = (0+1) * 1 := by rw [Fact2]
         _ ≥ 2 ^ 0 := by numbers
  | succ n ih =>
    calc Fact2 (n+1+1) = (n+1+1) * (Fact2 (n+1)) := by rw [Fact2]
         _ ≥ (n+1+1) * (2 ^ n) := by exact mul_le_mul_left (n + 1 + 1) ih
         _ = n * 2 ^ n + 2 * 2 ^ n := by ring
         _ ≥ 2 * 2 ^ n := by extra
         _ = 2 ^ (n + 1) := by ring

lemma Fact_overtakes_Exp2 (n : ℕ) : Fact2 (n + 1) ≥ 2 ^ n := by
  simple_induction n with k IH
  · -- base case
    calc Fact2 (0 + 1) = (0 + 1) * Fact2 0 := by rw [Fact2, Fact2, Fact2]
      _ = (0 + 1) * 1 := by rw [Fact2]
      _ ≥ 2 ^ 0 := by numbers
  · -- inductive step
    calc Fact2 (k + 1 + 1) = (k + 1 + 1) * Fact2 (k + 1) := by rw [Fact2]
      _ ≥ (k + 1 + 1) * 2 ^ k := by exact mul_le_mul_left (k + 1 + 1) IH
              -- in the previous step, `rel [IH]` does not work for some reasonn ...
      _ = k * 2 ^ k + 2 * 2 ^ k := by ring
      _ ≥ 2 * 2 ^ k := by extra
      _ = 2 ^ (k + 1) := by ring

/- # If two consecutive Fibonacci numbers are odd, the next one is even, i.e.
   # every third Fibonacci number is even. -/
theorem Fib_odd_odd_even1 (n : Nat) :
   Int.Odd (Fib n) → Int.Odd (Fib (n + 1)) →  Int.Even (Fib (n + 2)) := by
     intros h1 h2
     rw [Fib_add_two]          -- rewrite conclusion using lemma `myFib_add_two`
     exact odd_add_odd h1 h2   -- apply lemma `odd_add_odd` to conclude the proof

theorem Fib_odd_odd_even2 :
   (∀ (n : ℕ) , Int.Odd (Fib n) → Int.Odd (Fib (n + 1)) →  Int.Even (Fib (n + 2))) := by
     intro h0
     intros h1 h2
     rw [Fib_add_two]
     exact odd_add_odd h1 h2

-- A simple example to check the theorem works for a small number.
#check Fib_odd_odd_even2 -- 3
#check Fib_odd_odd_even1 1 -- (by decide) (by decide)
-- Lean confirms that `Even (fib 3)`, which is true (1, 1, 2, ...).

/- # Cassini's identity Fib (n-1) * Fib (n+1) - (Fib (n)) ^ 2 = (-1) ^ n -/

example {n : ℕ} (hn : 2 ≤ n) : (3:ℤ) ^ n ≥ 2 ^ n + 5 := by
  induction_from_starting_point n, hn with k hk IH
  · -- base case
    numbers
  · -- inductive step
    calc (3:ℤ) ^ (k + 1) = 2 * 3 ^ k + 3 ^ k := by ring
      _ ≥ 2 * (2 ^ k + 5) + 3 ^ k := by rel [IH]
      _ = 2 ^ (k + 1) + 5 + (5 + 3 ^ k) := by ring
      _ ≥ 2 ^ (k + 1) + 5 := by extra

theorem Fib_cassini_identity (n : ℕ) (hn : n ≥ 1) :
   Fib (n + 1) * Fib (n - 1) - Fib n ^ 2 = (0 - 1) ^ n := by
    induction_from_starting_point n, hn with k hk IH
    · -- base case
      calc
      Fib (1 + 1) * Fib (1 - 1) - Fib 1 ^ 2 = Fib 2 * Fib 0 - Fib 1 ^ 2 := by exact rfl
              _ = 1 * 0 - 1 ^ 2   := by exact rfl
              _ = 0 - 1           := by numbers
              _ = (0 - 1) ^ 1     := by numbers
    · -- inductive step
      calc
      Fib (k+1+1) * Fib (k+1-1) - Fib (k+1) ^ 2
          = Fib (k+2) * Fib k - Fib (k+1) ^ 2                             := by exact rfl
        _ = Fib (k+2) * Fib k - Fib (k+1) * Fib (k+1)                     := by ring
        _ = Fib (k+2) * Fib k - (Fib (k-1) + Fib k) * Fib (k+1)           := by sorry
        _ = Fib (k+2) * Fib k - Fib (k-1) * Fib (k+1) - Fib k * Fib (k+1) := by ring
        _ = Fib k * (Fib (k+2) - Fib (k+1)) - Fib (k-1) * Fib (k+1)       := by ring
        _ = Fib k * Fib k - Fib (k-1) * Fib (k+1) := by sorry
        _ = (Fib k) ^ 2 - Fib (k-1) * Fib (k+1)   := by ring
        _ = 0 - (Fib (k+1) * Fib (k-1) - (Fib k)^2) := by sorry
        _ = 0 - (0 - 1) ^ k                            := by rw [IH]
        _ = (0 - 1) * (0 - 1) ^ k                      := by ring
        _ = (0 - 1) ^ (k+1)                            := by ring





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
/- # FibSum (2 * n) = Fib (2 * n + 1) - 1 for all n ≥ 0   -/

/- DIVISIBILITY PROPERTY-/
/- # Fib (m) divides F (m * n)  for all m ≥ 1 and n ≥ 1 by induction on n  -/

/- GROWTH RATE -/
/- # Fib (n) ≥ (3 / 2) ^ (n - 2) for all n ≥ 2 or
   # (2 ^ (n-2)) * Fib (n) ≥ 3 ^ (n-2)  for all n ≥ 2 or
   # (2 ^ n) * Fib (n + 2) ≥ 3 ^ n for all n ≥ 0   -/
#eval 3.0 / 2   #eval (3 : ℚ) / 2   #eval ((3:ℚ) / 2) ^ 2

/- Other nice facts about the Fibonacci can be found here:
   https://matheducators.stackexchange.com/questions/2021/what-interesting-properties-of-the-fibonacci-sequence-can-i-share-when-introduci
-/
