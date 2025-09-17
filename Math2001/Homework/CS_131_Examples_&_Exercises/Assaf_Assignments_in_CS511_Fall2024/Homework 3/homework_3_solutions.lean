import Mathlib.Data.Real.Basic
import Library.Basic

math2001_init

-- # Exercise 3

/- 2 points -/
theorem exercise2_3_6_2 {x : ℝ} (h : x = 1 ∨ x = 2) : x ^ 2 - 3 * x + 2 = 0 := by
  obtain h | h := h
  · rw [h]; ring
  · rw [h]; ring

/- 2 points -/
theorem exercise2_3_6_3 {t : ℚ} (h : t = -2 ∨ t = 3) : t ^ 2 - t - 6 = 0 := by
  obtain h | h := h
  · rw [h]; ring
  · rw [h]; ring

/- 2 points -/
theorem exercise2_3_6_4 {x y : ℝ} (h : x = 2 ∨ y = -2) : x * y + 2 * x = 2 * y + 4 := by
  obtain h | h := h
  · rw [h]; ring
  · rw [h]; ring

-- # Exercise 4

/- 2 points -/
theorem exercise2_3_6_12 {x : ℤ} : 2 * x ≠ 3 := by
  have hx := le_or_succ_le x 1
  obtain hx | hx := hx
  · apply ne_of_lt
    calc
      2*x ≤ 2*1 := by rel [hx]
      _ < 3 := by numbers
  · apply ne_of_gt
    calc
      3 < 2*2 := by numbers
      _ ≤ 2*x := by rel [hx]

/- 2 points -/
theorem exercise2_4_5_1 {a b : ℚ} (H : a ≤ 1 ∧ a + b ≤ 3) : 2 * a + b ≤ 4 := by
  obtain ⟨h1,h2⟩ := H
  calc
    2 * a + b = a + (a + b) := by ring
    _ ≤ 1 + (3) := by rel [h1,h2]
    _ = 4 := by ring

/- 2 points -/
theorem exercise2_4_5_6 {x y : ℚ} (h : x + y = 5 ∧ x + 2 * y = 7) : x = 3 ∧ y = 2 := by
  obtain ⟨h1,h2⟩ := h
  have h3 : y = 2 := by
    calc
      y = (x + 2*y) - (x + y) := by ring
      _ = 7 - 5 := by rw [h1,h2]
      _ = 2 := by ring
  constructor
  · calc
      x = x + y - y := by ring
      _ = 5 - 2 := by rw [h1,h3]
      _ = 3 := by ring
  · exact h3

-- # Problem 2

/- 2 points -/
theorem exercise2_3_6_10 {t : ℝ} (ht : t ^ 3 = t ^ 2) : t = 1 ∨ t = 0 := by
  have h : (t*t)*(t-1) = 0 := by
    calc
      (t*t)*(t-1) = t^3 - t^2 := by ring
      _ = t^3 - t^3 := by rw [ht]
      _ = 0 := by ring
  apply eq_zero_or_eq_zero_of_mul_eq_zero at h
  obtain h | h := h
  · right
    apply eq_zero_or_eq_zero_of_mul_eq_zero at h
    obtain h | h := h
    · exact h
    · exact h
  · left; addarith [h]

/- 2 points -/
theorem exercise2_3_6_14 {m : ℕ} : m ^ 2 + 4 * m ≠ 46 := by
  have hm := le_or_succ_le m 5
  obtain hm | hm := hm
  · apply ne_of_lt
    calc
      m^2 + 4*m ≤ 5^2 + 4*5 := by rel [hm]
      _ < 46 := by numbers
  · apply ne_of_gt
    calc
      46 < 6^2 + 4*6 := by numbers
      _ ≤ m^2 + 4*m := by rel [hm]

/- 2 points -/
theorem exercise2_4_5_7 {a b : ℝ} (h1 : a * b = a) (h2 : a * b = b) : a = 0 ∧ b = 0 ∨ a = 1 ∧ b = 1 := by
  have h3 : a*b - a = 0 := by addarith [h1]
  have h4 : a*(b - 1) = 0 := by
    calc
      a*(b - 1) = a*b - a := by ring
      _ = 0 := by rw [h3]
  apply eq_zero_or_eq_zero_of_mul_eq_zero at h4
  obtain h4 | h4' := h4
  · left; constructor
    · exact h4
    · calc
        b = a * b := by rw [h2]
        _ = 0 * b := by rw [h4]
        _ = 0 := by ring
  · have h5 : b = 1 := by addarith [h4']
    right; constructor
    · calc
        a = a*b := by rw [h1]
        _ = b := by rw [h2]
        _ = 1 := by rw [h5]
    · exact h5
