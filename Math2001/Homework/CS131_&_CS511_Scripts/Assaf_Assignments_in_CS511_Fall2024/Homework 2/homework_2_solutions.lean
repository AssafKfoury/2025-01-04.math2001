import Mathlib.Data.Real.Basic
import Library.Basic

math2001_init

/-! # Homework 2 Solutions -/

/- # Exercise 3 -/

-- Example 1.4.6
/- 2 points -/
theorem example1_4_6 {n : ℤ} (hn : n ≥ 5) : n ^ 2 > 2 * n + 11 := by
  calc
    n^2 = n*n := by ring
    _ ≥ 5*n := by rel [hn]
    _ = 2*n + 3*n := by ring
    _ ≥ 2*n + 3*5 := by rel [hn]
    _ = (2*n + 11) + 4 := by ring
    _ > 2*n + 11 := by extra

-- Example 2.1.3
/- 2 points -/
theorem example2_1_3 {r s : ℚ} (h1 : s + 3 ≥ r) (h2 : s + r ≤ 3) : r ≤ 3 := by
  have h3 : r ≤ 3 + s := by addarith [h1] -- justify with one tactic
  have h4 : r ≤ 3 - s := by addarith [h2] -- justify with one tactic
  calc
    r = (r + r) / 2 := by ring -- justify with one tactic
    _ ≤ (3 - s + (3 + s)) / 2 := by rel [h3,h4] -- justify with one tactic
    _ = 3 := by ring -- justify with one tactic

-- Example 2.1.7
/- 2 points -/
theorem example2_1_7 (a b : ℝ) (h1 : -b ≤ a) (h2 : a ≤ b) : a ^ 2 ≤ b ^ 2 := by
  have h3 : b + a ≥ 0 := by addarith [h1]
  have h4 : b - a ≥ 0 := by addarith [h2]
  have h5 : b^2 - a^2 ≥ 0 := by
    calc
      b^2 - a^2 = (b - a)*(b + a) := by ring
      _ ≥ 0*0 := by rel [h3,h4]
      _ = 0 := by ring
  addarith [h5]

/- # Exercise 4 -/

-- Exercise 2.1.9 (1)
/- 2 points -/
theorem example2_1_9_1 {x : ℚ} (h1 : x ^ 2 = 4) (h2 : 1 < x) : x = 2 := by
  have h3 : x^2 - 4 = 0 := by addarith [h1]
  have h4 : (x - 2)*(x + 2) = 0 * (x + 2) := by
    calc
      (x - 2)*(x + 2) = x^2 - 4 := by ring
      _ = 0 := by rw [h3]
      _ = 0 * (x + 2) := by ring
  have h5 : x + 2 > 3 := by addarith [h2]
  cancel (x + 2) at h4
  addarith [h4]

-- Exercise 2.1.9 (3)
/- 2 points -/
theorem example2_1_9_3 (x y : ℚ) (h : x * y = 1) (h2 : x ≥ 1) : y ≤ 1 := by
  have h' : x*y > 0 := by
    calc
      x*y = 1 := by rw [h]
      _ > 0 := by numbers
  cancel x at h'
  calc
    y = 1 * y := by ring
    _ ≤ x * y := by rel [h2]
    _ = 1 := by rw [h]

-- Exercise 2.2.4 (1)
/- 2 points -/
theorem exercise2_2_4_1 {m : ℤ} (hm : m + 1 = 5) : 3 * m ≠ 6 := by
  apply ne_of_gt
  have hm' : m = 4 := by addarith [hm]
  calc
    6 < 3 * 4 := by numbers
    _ = 3 * m := by rw [hm']

/- # Problem 2 -/

-- Example 2.1.8
/- 2 points -/
theorem example2_1_8 (a b : ℝ) (h : a ≤ b) : a ^ 3 ≤ b ^ 3 := by
  have h' : 0 ≤ b - a := by addarith [h]
  calc
    a^3 ≤ a^3 + ((b - a)*((b - a)^2 + 3*(b + a)^2))/4 := by extra
    _ = b^3 := by ring

-- Exercise 2.1.9 (2)
/- 2 points -/
theorem exercise2_1_9_2 {n : ℤ} (hn : n ^ 2 + 4 = 4 * n) : n = 2 := by
  have h : (n - 2)^2 = 0^2 := by
    calc
      (n - 2)^2 = n^2 + 4 - 4*n := by ring
      _ = 4*n - 4*n := by rw [hn]
      _ = 0^2 := by ring
  cancel 2 at h
  addarith [h]

-- Exercise 2.2.4 (2)
/- 2 points -/
theorem exercise2_2_4_2 {s : ℚ} (h1 : 3 * s ≤ -6) (h2 : 2 * s ≥ -4) : s = -2 := by
  have h1' : s ≤ -2 := by
    calc
      s = (3*s)/3 := by ring
      _ ≤ -6/3 := by rel [h1]
      _ = -2 := by ring
  have h2' : s ≥ -2 := by
    calc
      s = (2*s)/2 := by ring
      _ ≥ (-4)/2 := by rel [h2]
      _ = -2 := by ring
  apply le_antisymm; apply h1'; apply h2'
