/- # CS 511, 15 Oct 2025, hw06_solution.lean -/

import Mathlib.Data.Real.Basic
import Library.Basic
import Library.Tactic.ModEq

math2001_init

/- # Exercise 3.4.5.1 in [MOP] -/
example {n : ℤ} (hn : n ≡ 1 [ZMOD 3]) : n ^ 3 + 7 * n ≡ 2 [ZMOD 3] :=
  calc
    n ^ 3 + 7 * n
      ≡ 1 ^ 3 + 7 * 1 [ZMOD 3] := by rel [hn]
    _ = 2 + 2 * 3 := by numbers
    _ ≡ 2 [ZMOD 3] := by extra
/- # Exercise 3.4.5.3 in [MOP] -/
example (a b : ℤ) : (a + b) ^ 3 ≡ a ^ 3 + b ^ 3 [ZMOD 3] :=
  calc
    (a + b) ^ 3
      = a ^ 3 + b ^ 3 + 3 * (a ^ 2 * b + b ^ 2 * a) := by ring
    _ ≡ a ^ 3 + b ^ 3 [ZMOD 3] := by extra
/- # Exercise 3.4.5.4 in [MOP] -/
example : ∃ a : ℤ, 4 * a ≡ 1 [ZMOD 7] := by
  use 2
  calc
    (4:ℤ) * 2 = 1 + 7 * 1 := by numbers
    _ ≡ 1 [ZMOD 7] := by extra

/- # Example 4.1.3 in [MOP] -/
example {a b : ℝ} (h : ∀ x, x ≥ a ∨ x ≤ b) : a ≤ b := by
  have : (a + b) / 2 ≥ a ∨ (a + b) / 2 ≤ b
  · apply h
  obtain H | H := this
  calc
    b = 2 * ((a + b) / 2) - a := by ring
    _ ≥ 2 * a - a := by rel [H]
    _ = a := by ring
  calc
    a = 2 * ((a + b) / 2) - b := by ring
    _ ≤ 2 * b - b := by rel [H]
    _ = b := by ring
/- # Example 4.1.4 in [MOP] -/
example {a b : ℝ} (ha1 : a ^ 2 ≤ 2) (hb1 : b ^ 2 ≤ 2) (ha2 : ∀ y, y ^ 2 ≤ 2 → y ≤ a)
    (hb2 : ∀ y, y ^ 2 ≤ 2 → y ≤ b) :
    a = b := by
  apply le_antisymm
  · apply hb2
    apply ha1
  · apply ha2
    apply hb1

namespace Nat

/- # Exercise 6.4.3.1 in [MOP] -/
theorem extract_pow_two (n : ℕ) (hn : 0 < n) : ∃ a x, Odd x ∧ n = 2 ^ a * x := by
  obtain H | H := even_or_odd n
  · -- case 1: `n` is even
    obtain ⟨m, hmn⟩ := H
    have hm :=
      calc 0 < n := hn
        _ = 2 * m := hmn
    cancel 2 at hm
    obtain ⟨b, y, hy, hmby⟩ := extract_pow_two m hm
    use b + 1, y
    constructor
    · apply hy
    · calc n = 2 * m := hmn
        _ = 2 * (2 ^ b * y) := by rw [hmby]
        _ = 2 ^ (b + 1) * y := by ring
  · -- case 2: `n` is odd
    use 0, n
    constructor
    · apply H
    · ring
