import Mathlib.Data.Real.Basic
import Library.Basic

math2001_init

-- # Exercise 3

/- 2 points -/
theorem exercise2_3_6_2 {x : ℝ} (h : x = 1 ∨ x = 2) : x ^ 2 - 3 * x + 2 = 0 := by
  sorry

/- 2 points -/
theorem exercise2_3_6_3 {t : ℚ} (h : t = -2 ∨ t = 3) : t ^ 2 - t - 6 = 0 := by
  sorry

/- 2 points -/
theorem exercise2_3_6_4 {x y : ℝ} (h : x = 2 ∨ y = -2) : x * y + 2 * x = 2 * y + 4 := by
  sorry

-- # Exercise 4

/- 2 points -/
theorem exercise2_3_6_12 {x : ℤ} : 2 * x ≠ 3 := by
  sorry

/- 2 points -/
theorem exercise2_4_5_1 {a b : ℚ} (H : a ≤ 1 ∧ a + b ≤ 3) : 2 * a + b ≤ 4 := by
  sorry

/- 2 points -/
theorem exercise2_4_5_6 {x y : ℚ} (h : x + y = 5 ∧ x + 2 * y = 7) : x = 3 ∧ y = 2 := by
  sorry

-- # Problem 2

/- 2 points -/
theorem exercise2_3_6_10 {t : ℝ} (ht : t ^ 3 = t ^ 2) : t = 1 ∨ t = 0 := by
  sorry

/- 2 points -/
theorem exercise2_3_6_14 {m : ℕ} : m ^ 2 + 4 * m ≠ 46 := by
  sorry

/- 2 points -/
theorem exercise2_4_5_7 {a b : ℝ} (h1 : a * b = a) (h2 : a * b = b) : a = 0 ∧ b = 0 ∨ a = 1 ∧ b = 1 := by
  sorry
