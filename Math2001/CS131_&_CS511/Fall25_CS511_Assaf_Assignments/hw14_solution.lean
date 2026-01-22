/- # 8 December 2025 hw14_solution.lean -/

import Library.Basic
import Library.Tactic.ModEq
import Library.Tactic.Exhaust

math2001_init

open Set Function Nat

/-# Exercise 4 -/

-- Exercise 9.1.10.1 in [MOP]

example : 4 ∈ {a : ℚ | a < 3} := by
  sorry

example : 4 ∉ {a : ℚ | a < 3} := by
  dsimp [Set.subset_def]
  push_neg
  numbers

-- Exercise 9.1.10.2 in [MOP]

example : 6 ∈ {n : ℕ | n ∣ 42} := by
  dsimp
  use 7
  ring

example : 6 ∉ {n : ℕ | n ∣ 42} := by
  sorry

-- Exercise 9.1.10.3  in [MOP]

example : 8 ∈ {k : ℤ | 5 ∣ k} := by
  sorry

example : 8 ∉ {k : ℤ | 5 ∣ k} := by
  dsimp
  apply Int.not_dvd_of_exists_lt_and_lt
  use 1
  constructor <;> numbers

/-# Exercise 5 -/

-- Exercise 9.1.10.6 in [MOP]

example : {a : ℕ | 20 ∣ a} ⊆ {x : ℕ | 5 ∣ x} := by
  dsimp [Set.subset_def]
  intros x h
  dsimp [(.∣.)] at *
  obtain ⟨c,hc⟩ := h
  use 4 * c
  rw [hc]
  ring

example : {a : ℕ | 20 ∣ a} ⊈ {x : ℕ | 5 ∣ x} := by
  sorry

-- Exercise 9.1.10.7 in [MOP]

example : {a : ℕ | 5 ∣ a} ⊆ {x : ℕ | 20 ∣ x} := by
  sorry

example : {a : ℕ | 5 ∣ a} ⊈ {x : ℕ | 20 ∣ x} := by
  dsimp [Set.subset_def]
  push_neg
  use 5
  constructor
  · use 1
    numbers
  · apply Nat.not_dvd_of_exists_lt_and_lt
    use 0
    constructor
    · numbers
    · numbers

-- Exercise 9.2.8.5 in [MOP]

example : {r : ℤ | r ≡ 7 [ZMOD 10] }
    ⊆ {s : ℤ | s ≡ 1 [ZMOD 2]} ∩ {t : ℤ | t ≡ 2 [ZMOD 5]} := by
  dsimp [Set.subset_def]
  intros x hx
  dsimp [Int.ModEq] at *
  obtain ⟨k,hk⟩ := hx
  have hk' : x = 10 * k + 7 := by addarith [hk]
  constructor
  · use 5 * k + 3
    rw [hk']
    ring
  · use 2 * k + 1
    rw [hk']
    ring

/-# PROBLEM 1 -/

-- Exercise 9.2.8.6 in [MOP]

example : {n : ℤ | 5 ∣ n} ∩ {n : ℤ | 8 ∣ n} ⊆ {n : ℤ | 40 ∣ n} := by
  dsimp [Set.subset_def]
  intros x hx
  obtain ⟨h1,h2⟩ := hx
  obtain ⟨a, ha⟩ := h1
  obtain ⟨b, hb⟩ := h2
  use -3 * b + 2 * a
  calc
    x = -15 * x + 16 * x := by ring
    _ = -15 * (8 * b) + 16 * x := by rw [hb]
    _ = -15 * (8 * b) + 16 * (5 * a) := by rw [ha]
    _ = 40 * (-3 * b + 2 * a) := by ring

-- Exercise 9.3.6.1 in [MOP]

def r (s : Set ℕ) : Set ℕ := s ∪ {3}

example : ¬ Injective r := by
  dsimp [Injective,r]
  push_neg
  use ∅,{3}
  dsimp
  constructor
  · ext x
    constructor
    · intros hx
      dsimp at *
      obtain hx | hx := hx
      · contradiction
      · left; apply hx
    · intros hx
      dsimp at *
      right
      obtain hx | hx := hx
      · apply hx
      · apply hx
  · ext
    push_neg
    use 3
    right
    constructor
    · dsimp
      exhaust
    · dsimp
