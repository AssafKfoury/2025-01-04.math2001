/- # CS 511, 31 Oct 2025, hw09_solution.lean -/
import Mathlib.Data.Real.Basic
import Library.Basic           -- needed for math2001_init
import Library.Tactic.Rel

math2001_init          --  needed to access Macbeth's tactics:
                       -- `addarith`, `cancel`, `extra`, `numbers`

/- # Execise 3 in Homework Assignment 09 -/

/- Exercise 5.3.6.3 in Macbeth's [MOP] -/
example (P : α → Prop) : ¬ (∀ x, P x) ↔ ∃ x, ¬ P x := by
  constructor
  · intro h
    by_cases h : ∃ x, ¬ P x
    · apply h
    · have : ∀ x, P x
      · intro a
        by_cases ha : P a
        · apply ha
        · have : ∃ x, ¬ P x
          · use a
            apply ha
          contradiction
      contradiction
  · intro h h'
    obtain ⟨a, ha⟩ := h
    apply ha (h' a)

/- Exercise 5.3.6.4 in Macbeth's [MOP] -/
example : (¬ ∀ a b : ℤ, a * b = 1 → a = 1 ∨ b = 1)
    ↔ ∃ a b : ℤ, a * b = 1 ∧ a ≠ 1 ∧ b ≠ 1 :=
  calc
    ¬ (∀ a b : ℤ, a * b = 1 → a = 1 ∨ b = 1)
      ↔ ∃ a, ¬ (∀ b : ℤ, a * b = 1 → a = 1 ∨ b = 1) := by rel [not_forall]
    _ ↔ ∃ a b : ℤ, ¬ (a * b = 1 → a = 1 ∨ b = 1) := by rel [not_forall]
    _ ↔ ∃ a b : ℤ, a * b = 1 ∧ ¬(a = 1 ∨ b = 1) := by rel [not_imp]
    _ ↔ ∃ a b : ℤ, a * b = 1 ∧ (a ≠ 1 ∧ b ≠ 1) := by rel [not_or]

/- Exercise 5.3.6.5 in Macbeth's [MOP]  -/
example : (¬ ∃ x : ℝ, ∀ y : ℝ, y ≤ x) ↔ (∀ x : ℝ, ∃ y : ℝ, y > x) :=
  calc
    ¬ (∃ x : ℝ, ∀ y : ℝ, y ≤ x)
      ↔ ∀ x : ℝ, ¬ ∀ y : ℝ, y ≤ x := by rel [not_exists]
    _ ↔ ∀ x : ℝ, ∃ y : ℝ, ¬ y ≤ x := by rel [not_forall]
    _ ↔ ∀ x : ℝ, ∃ y : ℝ, y > x := by rel [not_le]

/- Exercise 5.3.6.6 in Macbeth's [MOP]  -/
example : ¬ (∃ m : ℤ, ∀ n : ℤ, m = n + 5) ↔ ∀ m : ℤ, ∃ n : ℤ, m ≠ n + 5 :=
  calc
    ¬ (∃ m : ℤ, ∀ n : ℤ, m = n + 5)
      ↔ ∀ m : ℤ, ¬ (∀ n : ℤ, m = n + 5) := by rel [not_exists]
    _ ↔ ∀ m : ℤ, ∃ n : ℤ, m ≠ n + 5 := by rel [not_forall]

/- Exercise 5.3.6.8 in Macbeth's [MOP]-/
example : ¬ (∀ x : ℝ, x ^ 2 ≥ x) := by
  push_neg
  use 0.5
  numbers

/- # Exercise 4 in Homework Assignment 09 -/

/- Exercise 5.3.6.11 in Macbeth's [MOP]-/
example {p : ℕ} (k : ℕ) (hk1 : k ≠ 1) (hkp : k ≠ p) (hk : k ∣ p) : ¬ Prime p := by
  dsimp [Prime]
  push_neg
  right
  use k
  constructor
  · apply hk
  constructor
  · apply hk1
  · apply hkp

/- Exercise 5.3.6.13 in Macbeth's [MOP]-/
example {p : ℕ} (hp : ¬ Prime p) (hp2 : 2 ≤ p) : ∃ m, 2 ≤ m ∧ m < p ∧ m ∣ p := by
  have H : ¬ (∀ (m : ℕ), 2 ≤ m → m < p → ¬m ∣ p)
  · intro H
    have : Prime p
    · apply prime_test hp2
      apply H
    contradiction
  push_neg at H
  apply H

/- # PROBLEM 2 in Homework Assignment 09 -/

open Nat

def pascal : ℕ → ℕ → ℕ
  | a, 0 => 1
  | 0, b + 1 => 1
  | a + 1, b + 1 => pascal (a + 1) b + pascal a (b + 1)
termination_by _ a b => a + b

#check pascal

/- Exercise 6.5.4.1 in Macbeth's [MOP] -/
theorem pascal_symm (m n : ℕ) : pascal m n = pascal n m := by
  match m, n with
  | 0, 0 => ring
  | a + 1, 0 => rw [pascal, pascal]
  | 0, b + 1 => rw [pascal, pascal]
  | a + 1, b + 1 =>
    have IH1 := pascal_symm (a + 1) b
    have IH2 := pascal_symm a (b + 1)
    calc pascal (a + 1) (b + 1) = pascal (a + 1) b + pascal a (b + 1) := by rw [pascal]
      _ = pascal b (a + 1) + pascal (b + 1) a := by rw [IH1, IH2]
      _ = pascal (b + 1) a + pascal b (a + 1) := by ring
      _ = pascal (b + 1) (a + 1) := by rw [pascal]
termination_by _ a b => a + b

/- Exercise 6.5.4.2 in Macbeth's [MOP] -/
example (a : ℕ) : pascal a 1 = a + 1 := by
  simple_induction a with k IH
  · rw [pascal]
  · calc pascal (k + 1) 1 = pascal (k + 1) 0 + pascal k 1 := by rw [pascal, pascal, pascal]
      _ = 1 + (k + 1) := by rw [pascal, IH]
      _ = k + 1 + 1 := by ring
