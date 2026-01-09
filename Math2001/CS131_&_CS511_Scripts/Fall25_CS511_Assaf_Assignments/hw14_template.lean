/- # 8 December 2025 hw14_template.lean -/

import Library.Basic
import Library.Tactic.ModEq
import Library.Tactic.Exhaust

math2001_init

open Set Function Nat

/-# Exercise 4-/

-- Exercise 9.1.10.1 in [MOP]

example : 4 ∈ {a : ℚ | a < 3} := by
  sorry

example : 4 ∉ {a : ℚ | a < 3} := by
  sorry

-- Exercise 9.1.10.2 in [MOP]

example : 6 ∈ {n : ℕ | n ∣ 42} := by
  sorry

example : 6 ∉ {n : ℕ | n ∣ 42} := by
  sorry

-- Exercise 9.1.10.3 in [MOP]

example : 8 ∈ {k : ℤ | 5 ∣ k} := by
  sorry

example : 8 ∉ {k : ℤ | 5 ∣ k} := by
  sorry


/-# Exercise 5 -/

-- Exercise 9.1.10.6 in [MOP]

example : {a : ℕ | 20 ∣ a} ⊆ {x : ℕ | 5 ∣ x} := by
  sorry

example : {a : ℕ | 20 ∣ a} ⊈ {x : ℕ | 5 ∣ x} := by
  sorry

-- Exercise 9.1.10.7 in [MOP]

example : {a : ℕ | 5 ∣ a} ⊆ {x : ℕ | 20 ∣ x} := by
  sorry

example : {a : ℕ | 5 ∣ a} ⊈ {x : ℕ | 20 ∣ x} := by
  sorry

--Exercise 9.2.8.5 in [MOP]

example : {r : ℤ | r ≡ 7 [ZMOD 10] }
    ⊆ {s : ℤ | s ≡ 1 [ZMOD 2]} ∩ {t : ℤ | t ≡ 2 [ZMOD 5]} := by
  sorry

/-# PROBLEM 1 -/

-- Exercise 9.2.8.6 in [MOP]

example : {n : ℤ | 5 ∣ n} ∩ {n : ℤ | 8 ∣ n} ⊆ {n : ℤ | 40 ∣ n} := by
  sorry

-- Exercise 9.3.6.1 in [MOP]

def r (s : Set ℕ) : Set ℕ := s ∪ {3}

example : ¬ Injective r := by
  sorry
