import Mathlib.Tactic.GCongr
import Library.Basic
import Library.Tactic.ModEq
import AutograderLib

math2001_init

namespace Int

def A : ℕ → ℚ  -- recursive def of ∑ {1, 2, ... ,n}
  | 0 => 0
  | n + 1 => A n + (n + 1)

def B : ℕ → ℚ -- recursive def of ∑ {1*1, 2*2, ... , n*n}
  | 0 => 0
  | n + 1 => B n + (n + 1) * (n + 1)

def fact : ℕ → ℚ -- recursive def of factorial function
  | 0 => 1
  | n + 1 => (fact n) * (n+1)

def F : ℕ → ℚ -- recursive def of (n+3)! / (3! * n!)
  | 0 => 1
  | n + 1 => (F n) * (n + 4) / (n + 1)

def G : ℚ → ℚ -- G is a simpler (non-recursive) def of F
  | n => (n + 3) * (n + 2) * (n + 1) / 6

#eval G 1 = 1/2 * ((A 2) + (B 2))
#eval G 2 = 1/2 * ((A 3) + (B 3))
#eval G 3 = 1/2 * ((A 4) + (B 4))

lemma sum_A (n : ℕ) : A n = n * (n + 1) / 2 := by
  simple_induction n with k IH
  · -- base case
    calc A 0 = 0 := by rw [A]
      _ = 0 * (0 + 1) / 2 := by numbers
  · -- inductive step
    calc
      A (k + 1) = A k + (k + 1) := by rw [A]
      _ = k * (k + 1) / 2 + (k + 1) := by rw [IH]
      _ = (k + 1) * (k + 1 + 1) / 2 := by ring

lemma sum_B (n : ℕ) : B n = n * (n + 1) * (2 * n + 1) / 6 := by
  simple_induction n with k IH
  · calc B 0 = 0 := by rw [B]
           _ = 0 * (0 + 1) * (2 * 0 + 1) / 6 := by numbers
  · calc
      B (k + 1) = B k + (k + 1) * (k + 1) := by rw [B]
            _   = k * (k+1) * (2*k + 1) / 6 + (k+1) * (k+1) := by rw [IH]
            _   = (k+1) * (k+1+1) * (2 * (k+1) + 1) / 6 := by ring

theorem problem3 (n : ℕ) : G (n:ℚ) = 1 / 2 * (A (n  + 1) + B (n + 1)) := by
  -- have h_A : A n = n * (n + 1) / 2 := by apply (sum_A n)
  -- have hA : A (n+1) = (n+1) * (n + 2) / 2 := by apply? -- exact  sum_A (n+1)
  calc G n = (n + 3) * (n + 2) * (n + 1) / 6 := by rw [G]
     _ = (n * n * n + 6 * n * n + 11 * n + 6) / 6 := by ring
     _ = (2 * n * n * n + 12 * n * n + 22 * n + 12) / 12 := by ring
     _ = (3 * n * n + 9 * n + 6) / 12 + (2 * n * n * n + 9 * n * n + 13 * n +6) / 12 := by ring
     _ = (n * n + 3 * n + 2) / 4 + (2 * n * n * n + 9 * n * n + 13 * n + 6) / 12 := by ring
     _ = (1/2) * ((n + 1) * (n + 2) / 2 + (n + 1) * (n + 2) * (2 * n + 3) / 6) := by ring
     _ = (1/2) * (A (n+1) + (n + 1) * (n + 2) * (2 * n + 3) / 6) := by apply (sum_A (n+1))
