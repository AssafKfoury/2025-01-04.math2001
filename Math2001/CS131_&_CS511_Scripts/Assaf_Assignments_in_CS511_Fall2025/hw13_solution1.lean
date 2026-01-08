/- # 20 November 2025 hw13_solution1.lean -/
import Mathlib.Data.Real.Basic
import Library.Basic

import Library.Theory.InjectiveSurjective

math2001_init

open Set Function Nat

/-# Exercise 3 in HW13 -/

--Exercise 8.3.10.5 in [MOP]

example {f : X → Y} (hf : Surjective f) : ∃ g : Y → X, f ∘ g = id := by
  dsimp [Surjective] at hf
  choose g hg using hf
  use g
  ext y
  have this := hg y
  apply this

--Exercise 8.3.10.7 in [MOP]

example {f : X → Y} {g1 g2 : Y → X} (h1 : Inverse f g1) (h2 : Inverse f g2) :
    g1 = g2 := by
  dsimp [Inverse] at *
  obtain ⟨gof1,fog1⟩ := h1
  obtain ⟨gof2,fog2⟩ := h2
  calc
    g1 = id ∘ g1 := by rfl
    _ = (g2 ∘ f) ∘ g1 := by rw [gof2]
    _ = g2 ∘ (f ∘ g1) := by rfl
    _ = g2 ∘ (id) := by rw [fog1]
    _ = g2 := by rfl

/-# Exercise 4 in HW13 -/

--Exercise 8.4.10.1 in [MOP]

example : Bijective (fun ((r, s) : ℚ × ℚ) ↦ (s, r - s)) := by
  rw [bijective_iff_exists_inverse]
  use fun (a,b) ↦ (a+b,a)
  constructor
  · ext ⟨r,s⟩; dsimp; ring
  · ext ⟨a,b⟩; dsimp; ring

--Exercise 8.4.10.2.1 in [MOP]

example : ¬ Injective (fun ((x, y) : ℤ × ℤ) ↦ x - 2 * y - 1) := by
  dsimp [Injective]
  push_neg
  use (0,0), (2,1)
  constructor
  · ring
  · numbers

--Exercise 8.4.10.2.2 in [MOP]

example : Surjective (fun ((x, y) : ℤ × ℤ) ↦ x - 2 * y - 1) := by
  dsimp [Surjective]
  intros b
  use (3*b+1,b)
  dsimp
  ring
