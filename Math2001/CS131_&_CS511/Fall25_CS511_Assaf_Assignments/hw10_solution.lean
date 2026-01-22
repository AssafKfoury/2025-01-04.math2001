/- # CS 511, 08 November 2025, hw10_solution.lean -/

import Mathlib.Data.Real.Basic
import Library.Basic
import Library.Tactic.ModEq
math2001_init           --  needed to access Macbeth's tactics:
                        -- `addarith`, `cancel`, `extra`, `numbers`

/- # Example 6.1.3 in [MOP], Exercise 3, part 1, in HW10 -/
theorem exercise_3_1 {a b d : ℤ} (h : a ≡ b [ZMOD d]) (n : ℕ) : a ^ n ≡ b ^ n [ZMOD d] := by
  simple_induction n with k IH
  · dsimp [Int.ModEq,(.∣.)] at *
    use 0
    ring
  · dsimp [Int.ModEq,(.∣.)] at *
    obtain ⟨x,hx⟩ := IH
    obtain ⟨y,hy⟩ := h
    use (a * x + b ^ k * y)
    calc
        a ^ (k + 1) - b ^( k + 1) =
            a * (a ^ k - b ^ k) + b ^ k * (a - b) := by ring
        _ = a * (d * x) + b ^ k * (d * y)         := by rw [hx,hy]
        _ = d * (a * x + b ^ k * y)               := by ring

/- # Example 6.1.6 in [MOP], Exercise 3, part 2, in HW10 -/
theorem exercise_3_2 : forall_sufficiently_large n : ℕ, 2 ^ n ≥ n ^ 2 := by
  dsimp
  use 4
  intro n hn
  induction_from_starting_point n, hn with k hk IH
  · -- base case
    numbers
  · -- inductive step
    calc
      2 ^ (k + 1) = 2 * 2 ^ k   := by ring
      _ ≥ 2 * k ^ 2             := by rel [IH]
      _ = k ^ 2 + k * k         := by ring
      _ ≥ k ^ 2 + 4 * k         := by rel [hk]
      _ = k ^ 2 + 2 * k + 2 * k := by ring
      _ ≥ k ^ 2 + 2 * k + 2 * 4 := by rel [hk]
      _ = (k + 1) ^ 2 + 7       := by ring
      _ ≥ (k + 1) ^ 2           := by extra

/- # Exercise 6.1.7.2 in [MOP], Exercise 4, part 1, in HW10 -/
theorem exercise_4_1 {a : ℝ} (ha : -1 ≤ a) (n : ℕ) : (1 + a) ^ n ≥ 1 + n * a := by
  have ha' : 0 ≤ 1 + a :=
    calc
      0 = 1 + (-1) := by ring
      _ ≤ 1 + a    := by rel [ha]
  simple_induction n with n IH
  · calc
      (1 + a) ^ 0 = 1   := by ring -- `by numbers` does not work
       _   = 1 + 0 * a  := by ring
       _   ≥ 1 + 0 * a  := by exact Eq.ge rfl -- `by extra` also works
  · calc
      (1 + a) ^ (n + 1) = (1 + a) * (1 + a) ^ n := by ring
       _ ≥ (1 + a) * (1 + n * a)                := by rel [IH]
       _ = 1 + (n + 1) * a + n * a ^ 2          := by ring
       _ ≥ 1 + (n + 1) * a                      := by extra

/- # Exercise 6.1.7.6 in [MOP], Exercise 4, part 2, in HW10 -/
theorem exercise_4_2 : forall_sufficiently_large n : ℕ, (3:ℤ) ^ n ≥ 2 ^ n + 100 := by
  dsimp
  use 5
  intros x hx
  induction_from_starting_point x, hx with n hn IH
  · numbers
  · calc
      (3 : ℤ) ^ (n + 1) = 3 * 3 ^ n      := by ring
       _ ≥ 3 * (2 ^ n + 100)             := by rel [IH]
       _ = 2 * (2^n + 100) + (2^n + 100) := by ring
       _ ≥ 2 * (2 ^ n + 100)             := by extra
       _ = 2 ^ (n + 1) + 100 + 100       := by ring
       _ ≥ 2 ^ (n + 1) + 100             := by extra

/- # The function `foo` computes the sum of odd natural numbers, specifically,
   # `foo (n)` is the sum of the first (n+1) odd natural numbers for every n ∈ ℕ : -/

def foo : ℕ → ℕ
  | 0     => 1
  | n + 1 => foo (n) + 2 * n + 3

/- # PROBLEM 2 in HW10 -/
theorem problem_2 {n : ℕ} : ∃ (k : ℕ), foo (n) = k ^ 2 := by
  use n + 1
  simple_induction n with k IH
  · -- base case
    rw [foo]
    numbers
  · -- inductive step
    calc foo (k + 1) = foo (k) + 2 * k + 3 := by rw [foo]
           _  = (k + 1)^2 + 2 * k + 3      := by rw [IH]
           _  = (k + 2)^2                  := by ring
