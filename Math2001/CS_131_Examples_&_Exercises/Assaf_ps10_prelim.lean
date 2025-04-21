import Mathlib.Tactic.GCongr
import Library.Basic
import Library.Tactic.ModEq
import AutograderLib

math2001_init

namespace Int

def A : ℕ → ℚ
  | 0 => 0
  | n + 1 => A n + (n + 1)

def B : ℕ → ℚ
  | 0 => 0
  | n + 1 => B n + (n + 1) * (n + 1)

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

#check sum_A
#eval A 3
#eval B 3
