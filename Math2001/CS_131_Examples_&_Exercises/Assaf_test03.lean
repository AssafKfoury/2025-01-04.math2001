import Mathlib.Tactic.GCongr
import Library.Basic
import AutograderLib

example {r s : ℤ} (h1 : s = 3) (h2 : r + 2 * s = -1) : r = -7 :=
calc
  r = r + 2 * s - 2 * s := by sorry
  _ = -1 - 2 * s := by sorry
  _ = -1 - 2 * 3 := by sorry
  _ = -7 := by sorry

example {r s : ℤ} (h1 : s = 3) (h2 : r + 2 * s = -1) : r = -7 :=
calc
  r = r + 2 * s - 2 * s := by ring
  _ = -1 - 2 * s := by rw [h2]
  _ = -1 - 2 * 3 := by rw [h1]
  _ = -7 := by ring

example {r s : ℚ} (h1 : s + 3 ≥ r) (h2 : s + r ≤ 3) : r ≤ 3 :=
calc
  r = (s + r + r - s) / 2 := by sorry
  _ ≤ (3 + (s + 3) - s) / 2 := by sorry
  _ = 3 := by sorry

/-
example {r s : ℚ} (h1 : s + 3 ≥ r) (h2 : s + r ≤ 3) : r ≤ 3 :=
calc
  r = (s + r + r - s) / 2 := by ring
  _ ≤ (3 + (s + 3) - s) / 2 := by rel [h1, h2]
  _ = 3 := by ring
-/

example {r s : ℚ} (h1 : s + 3 ≥ r) (h2 : s + r ≤ 3) : r ≤ 3 := by
  have h3 : r ≤ 3 + s := by sorry
  have h4 : r ≤ 3 - s := by sorry
  calc
    r = (r + r) / 2 := by sorry
    _ ≤ (3 - s + (3 + s)) / 2 := by sorry
    _ = 3 := by sorry

/-
example {r s : ℚ} (h1 : s + 3 ≥ r) (h2 : s + r ≤ 3) : r ≤ 3 := by
have h3 : r ≤ 3 + s := by addarith [h1]
have h4 : r ≤ 3 - s := by addarith [h2]
calc
r = (r + r) / 2 := by ring
_ ≤ (3 - s + (3 + s)) / 2 := by rel [h3, h4]
_ = 3 := by ring
-/

example {m : ℤ} (hm : m + 1 = 5) : 3 * m ≠ 6 := by
  sorry

/-
example {m : ℤ} (hm : m + 1 = 5) : 3 * m ≠ 6 := by
apply ne_of_gt
calc
(6:Z) < 3 * 5 - 3 := by numbers
_ = 3 * (m + 1) - 3 := by rw [hm]
_ = 3 * m := by ring
-/