import Mathlib.Data.Real.Basic
import Library.Basic

math2001_init

/-! # CS 511 Homework 1 -/

/- 6 points -/
theorem exercise3 {w : ℚ} (h1 : 3 * w + 1 = 4) : w = 1 := by
  calc
    w = (3 * w + 1) / 3 - (1 / 3) := by ring
    _ = 4 / 3 - 1 / 3 := by rw [h1]
    _ = 1 := by ring

/- 6 points -/
theorem exercise4 {a b : ℚ} (h1 : a - 3 = 2 * b) : a ^ 2 - a + 3 = 4 * b ^ 2 + 10 * b + 9 := by
  calc
    a ^ 2 - a + 3 = (a - 3) ^ 2 + 5 * (a - 3) + 9 := by ring
    _ = (2 * b) ^ 2 + 5 * (2 * b) + 9 := by rw [h1]
    _ = 4 * b ^ 2 + 10 * b + 9 := by ring

/- 6 points -/
theorem problem2 {a b c : ℝ} (h1 : a + 2 * b + 3 * c = 7) (h2 : b + 2 * c = 3)
    (h3 : c = 1) : a = 2 := by
  calc
    a = a + 2 * b + 3 * c - 2 * (b + 2 * c) + c := by ring
    _ = 7 - 2 * 3 + 1 := by rw [h1,h2,h3]
    _ = 2 := by ring
