import Mathlib.Data.Real.Basic
import Library.Basic
-- import Library.Tactic.ModEq
-- import Mathlib.Tactic.GCongr
-- import AutograderLib

math2001_init
namespace Int

/-
  The calculation in this problem counts the number of distinct walking
  trajectories in Manhattan that require to walk 3 blocks EAST and n
  blocks SOUTH. We assume that Manhattan streets are organized as a
  rectangular grid, with streets running from EAST to WEST and avenues
  running from NORTH to SOUTH.

  In this exercise, you are asked to prove in Lean4 that this number
  of distinct trajectories is:

  (n + 3)! / (3! * n!)
     = (1/2) * Σ { k + k*k | 1 ≤ k ≤ n+1 }
     = (1/2) * [(1 * 2) + (2 * 3) + (3 * 4) + ... + ((n + 1) * (n + 2))
     = (1/6) * (n + 1) * (n + 2) * (n + 3)

  Proofs of these three equalities can be found on the Web. In particular,
  the third and last equality can be found on the Web by searching for:
  "what is the partial sum of the series k * (k+1) as k ranges from 1 to n+1?"
-/

def A : ℕ → ℚ  -- recursive def of ∑ {1, 2, ... ,n}
  | 0 => 0
  | n + 1 => A n + (n + 1)

def B : ℕ → ℚ -- recursive def of ∑ {1*1, 2*2, ... , n*n}
  | 0 => 0
  | n + 1 => B n + (n + 1) * (n + 1)

def fact : ℕ → ℚ -- recursive def of factorial function
  | 0 => 1
  | n + 1 => (fact n) * (n+1)

def F : ℕ → ℚ -- recursive def of (n+3)! / (3! * n!) which is the number
              -- of ways of walking 3 blocks EAST and n blocks SOUTH
  | 0 => 1
  | n + 1 => (F n) * (n + 4) / (n + 1)

def G : ℕ → ℚ -- G is a simpler (non-recursive) def of F
  | n => (n + 3) * (n + 2) * (n + 1) / 6

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
  · calc
      B 0 = 0 := by rw [B]
        _ = 0 * (0 + 1) * (2 * 0 + 1) / 6 := by numbers
  · calc
      B (k + 1) = B k + (k + 1) * (k + 1) := by rw [B]
            _   = k * (k+1) * (2*k + 1) / 6 + (k+1) * (k+1) := by rw [IH]
            _   = (k+1) * (k+1+1) * (2 * (k+1) + 1) / 6 := by ring

lemma sum_AB (n : ℕ) : A (n) + B (n) = n * (n+1) / 2 + n * (n+1) * (2*n + 1) / 6 := by
   simple_induction n with k IH
   · have h1 : A 0 = 0 * (0 + 1) / 2 := by apply sum_A
     have h2 : B 0 = 0 * (0 + 1) * (2 * 0 + 1) / 6 := by apply sum_B
     calc
      A 0 + B 0 = 0 * (0 + 1) / 2 + B 0 := by rw [h1]
              _ = 0 * (0 + 1) / 2 + 0 * (0+1) * (2*0 + 1) / 6 := by rw [h2]
   · calc
      A (k+1) + B (k+1) = A (k) + (k + 1) + (B (k) + (k+1)*(k+1)) := by rw [A,B]
      _ = A (k) + B (k) + (k+1) + (k+1)*(k+1) := by ring
      _ = k * (k+1) / 2 + k * (k+1) * (2*k + 1) / 6 + (k+1) + (k+1)*(k+1) := by rw [IH]
      _ = (k+1) * (k+1+1) / 2 + (k+1)*(k+1+1)*(2*(k+1)+1) / 6 := by ring

theorem problem3 (n : ℕ) : F n = (1/2) * (A (n+1) + B (n+1)) := by
  simple_induction n with k IH
  · calc F 0 = 1 := by rw [F]
           _ = 1 / 2 * (0 + (0+1) + (0 + (0+1)*(0+1))) := by ring -- 'by numbers' will work too
           _ = 1 / 2 * (A 0 + (0+1) + (B 0 + (0+1)*(0+1))) := by rw [A,B]
           _ = 1 / 2 * (A (0 + 1) + (B (0+1))) := by exact rfl
  · -- norm_cast
    have h1 : A (k+1) + B (k+1) = (k+1) * (k+1+1) / 2 + (k+1) * (k+1+1) * (2*(k+1) + 1) / 6 :=
         by apply sum_AB
/-    calc F (k+1) = (F k) * (k+4) / (k+1) := by rw [F]
         _  = (1/2) * (A (k+1) + B (k+1)) * (k+4) / (k+1) := by rw [IH]
         _  = (1/2) * ((k+1) * (k+1+1) / 2 + (k+1) * (k+1+1) * (2*(k+1) + 1) / 6) * (k+4) / (k+1) :=
                by rw [h1] -- [sum_AB]
-/

theorem problem3_A (n : ℕ) : F n = (1/2) * (A (n+1) + B (n+1)) := by
  simple_induction n with k IH
  · calc F 0 = 1 := by rw [F]
           _ = 1 / 2 * (0 + (0+1) + (0 + (0+1)*(0+1))) := by ring -- 'by numbers' will work too
           _ = 1 / 2 * (A 0 + (0+1) + (B 0 + (0+1)*(0+1))) := by rw [A,B]
           _ = 1 / 2 * (A (0 + 1) + (B (0+1))) := by exact rfl
  · calc F (k+1) = (F k) * (k+4) / (k+1) := by rw [F]
         _  = (1/2) * (A (k+1) + B (k+1)) * (k+4) / (k+1) := by rw [IH]
         _  = (1/2) * ((A (k+1) + (k+2)) + B (k+1) + (k+2)*(k+2) - (k+2)*(k+3)) * (k+4)/(k+1) := by ring
         _  = (1/2) * (A (k+2) + B (k+1) + (k+2)*(k+2) - (k+2)*(k+3)) * (k+4)/(k+1) := sorry

theorem problem3_B (n : ℕ) : G n = 1 / 2 * (A (n  + 1) + B (n + 1)) := by
  simple_induction n with k IH
  · -- base case
    calc G 0 = (0 + 3) * (0 + 2) * (0 + 1) / 6 := by exact rfl
           _ = 1 := by ring
           _ = (1/2) * (1 + 1) := by ring
           _ = (1/2) * ((0 + (0+1)) + (0 + (0+1)*(0+1))) := by ring
           _ = (1/2) * (((A 0) + (0+1)) + ((B 0) + (0+1)*(0+1))) := by rw [A,B]
           _ = (1/2) * ( A (0+1) + B (0+1) ) := by exact rfl
  · -- inductive step
    sorry
