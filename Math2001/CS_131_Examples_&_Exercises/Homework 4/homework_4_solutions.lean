import Mathlib.Data.Real.Basic
import Library.Basic
import AutograderLib

math2001_init

@[autogradedProof 2]
theorem exercise3a : ∃ m n : ℤ, m ^ 2 - n ^ 2 = 11 := by
  use 6, 5
  numbers

@[autogradedProof 2]
theorem exercise3b (a : ℤ) : ∃ m n : ℤ, m ^ 2 - n ^ 2 = 2 * a + 1 := by
  use a + 1, a
  ring

@[autogradedProof 2]
theorem exercise3c {p q : ℝ} (h : p < q) : ∃ x, p < x ∧ x < q := by
  use (p + q)/2
  constructor
  · calc
      p = (p + p)/2 := by ring
      _ < (p + q)/2 := by rel [h]
  · calc
      (p + q)/2 < (q + q)/2 := by rel [h]
      _ = q := by ring

@[autogradedProof 2]
theorem exercise4a {m n : ℤ} (hm : Odd m) (hn : Even n) : Odd (n + m) := by
  dsimp [Odd] at hm
  dsimp [Even] at hn
  dsimp [Odd]
  obtain ⟨x,hx⟩ := hm
  obtain ⟨y,hy⟩ := hn
  use x + y
  rw [hx,hy]
  ring

@[autogradedProof 2]
theorem exercise4b {a : ℚ} (h : ∀ b : ℚ, a ≥ -3 + 4 * b - b ^ 2) : a ≥ 1 := by
  have h1 : a ≥ -3 + 4*2 - 2^2 := by apply h 2
  addarith [h1]

@[autogradedProof 2]
theorem exercise4c {a b : ℝ} (h : ∀ x, x ≥ a ∨ x ≤ b) : a ≤ b := by
  have h1 : (a + b)/2 ≥ a ∨ (a + b)/2 ≤ b := by apply h
  obtain h1 | h1 := h1
  · calc
      b = 2*((a + b)/2) - a := by ring
      _ ≥ 2*a - a := by rel [h1]
      _ = a := by ring
  · calc
      a = 2*((a + b)/2) - b := by ring
      _ ≤ 2*b - b := by rel [h1]
      _ = b := by ring

@[autogradedProof 2]
theorem problem2a : ¬(3 : ℤ) ∣ -10 := by
  apply Int.not_dvd_of_exists_lt_and_lt
  use -4
  constructor
  · numbers
  · numbers

@[autogradedProof 2]
theorem problem2b {a b : ℤ} (hab : a ∣ b) : a ∣ 2 * b ^ 3 - b ^ 2 + 3 * b := by
  dsimp [(·∣·)] at *
  obtain ⟨k,hk⟩ := hab
  use 2*a^2*k^3 - a*k^2 + 3*k
  rw [hk]
  ring

@[autogradedProof 2]
theorem problem2c {k l m : ℤ} (h1 : k ∣ l) (h2 : l ^ 3 ∣ m) : k ^ 3 ∣ m := by
  dsimp [(·∣·)] at *
  obtain ⟨a,ha⟩ := h1
  obtain ⟨b,hb⟩ := h2
  use a^3*b
  rw [hb,ha]
  ring
