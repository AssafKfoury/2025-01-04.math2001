/- # 21 November 2025, hw12_template1.lean -/
import Mathlib.Data.Real.Basic
import Library.Basic
import Library.Theory.InjectiveSurjective

math2001_init

open Set Function Nat

/-# Exercise 3 in HW 12 -/

--Exercise 6.4.3.1 in [MOP]

theorem extract_pow_two (n : ℕ) (hn : 0 < n) : ∃ a x, Nat.Odd x ∧ n = 2 ^ a * x := by
     sorry

/-# Exercise 4 in HW 12 -/

-- Exercise 8.3.10.2 in [MOP]

def u (x : ℝ) : ℝ := 5 * x + 1

noncomputable def v (x : ℝ) : ℝ := sorry

example : Inverse u v := by
  sorry

-- Exercise 8.3.10.3 in [MOP]

example {f : X → Y} (hf : Injective f) {g : Y → Z} (hg : Injective g) :
    Injective (g ∘ f) := by
  sorry

-- Exercise 8.3.10.4 in [MOP]

example {f : X → Y} (hf : Surjective f) {g : Y → Z} (hg : Surjective g) :
    Surjective (g ∘ f) := by
  sorry
