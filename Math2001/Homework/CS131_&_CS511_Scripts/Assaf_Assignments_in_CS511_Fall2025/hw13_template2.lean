/- # 30 November 2025 hw13_template2.lean -/

/- # This script involves proofs by induction, all
   # related to the Fibonacci numbers.  -/

import Mathlib.Data.Real.Basic
import Library.Basic

math2001_init

/- # PROBLEM 2 in HW13 -/

/- # Fibonacci function -/
def Fib : ℕ → ℤ -- ℕ
   | 0 => 0 -- sometimes `Fib 0` is defined as returning value `1`
   | 1 => 1
   | n + 2 => Fib (n) + Fib (n+1)

/- # THREE DIFFERENT WAYS of proving Example 6.3.1 in [MOP]-/

/- # Inductively defined function (similar to Fibonacci) -/
def a : ℕ → ℤ
  | 0 => 2
  | 1 => 1
  | n + 2 => a (n + 1) + 2 * a n

/- Following is essentially the same proof of Example 6.3.1 as in [MOP] -/
example (n : ℕ) : a n = 2 ^ n + (-1) ^ n := by
  induction' n using Nat.twoStepInduction with k IH1 IH2
  sorry

/- Different way of setting up the two-step-induction
   instead of " induction'" and a little less transparently -/
example (n : ℕ) : a n = 2 ^ n + (-1) ^ n := by
  induction n using Nat.twoStepInduction
  . rfl
  . rfl
  . case _ k ik1 ik2 => calc
    a (k + 2) = a (k + 1) + 2 * a k := rfl
    _ = (2 ^ (k + 1) + (-1) ^ (k + 1)) + 2 * (2 ^ k + (-1) ^ k) := by rw [ik1, ik2]
    _ = 2 ^ (k + 2) + (-1) ^ (k + 2) := by ring

/- Different way still of setting up the induction,
   but without using Nat.twoStepInduction -/
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

  /- # MORE PROPERTIES OF Fibonacci numbers -/

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

/- # Next example is almost like `Example 6.3.4` in [MOP] but not quite, because
   # our definition of Fib 0 = 0, not Fib 0 = 1 as in [MOP] . I include it here
   # because it is closely related to Cassini's identity (below) -/

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

/- # Cassini's identity : -/
theorem Cassini_id (n : ℕ) :
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
