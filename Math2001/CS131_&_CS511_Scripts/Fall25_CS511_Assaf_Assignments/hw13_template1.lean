/- # 20 November 2025 hw13_template.lean -/
import Mathlib.Data.Real.Basic
import Library.Basic

import Library.Theory.InjectiveSurjective

math2001_init

open Set Function Nat

/-# Exercise 3-/

--Exercise 8.3.10.5 in [MOP]

example {f : X → Y} (hf : Surjective f) : ∃ g : Y → X, f ∘ g = id := by
  sorry

--Exercise 8.3.10.7 in [MOP]

example {f : X → Y} {g1 g2 : Y → X} (h1 : Inverse f g1) (h2 : Inverse f g2) :
    g1 = g2 := by
  sorry

/-# Exercise 4-/

--Exercise 8.4.10.1 in [MOP]

example : Bijective (fun ((r, s) : ℚ × ℚ) ↦ (s, r - s)) := by
  rw [bijective_iff_exists_inverse]
  sorry

--Exercise 8.4.10.2.1 in [MOP]

example : ¬ Injective (fun ((x, y) : ℤ × ℤ) ↦ x - 2 * y - 1) := by
  sorry

--Exercise 8.4.10.2.2 in [MOP]

example : Surjective (fun ((x, y) : ℤ × ℤ) ↦ x - 2 * y - 1) := by
  sorry
