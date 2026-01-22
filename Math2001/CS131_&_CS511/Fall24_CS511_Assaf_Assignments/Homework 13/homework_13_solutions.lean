import Mathlib.Data.Real.Basic
import Library.Basic
import Library.Tactic.Exhaust
import Library.Tactic.ModEq

math2001_init

/-# Exercise 3-/

--Exercise 10.1.5.4

section
local infix:50 "∼" => fun (x y : ℤ) ↦ y ≡ x + 1 [ZMOD 5]

example : Reflexive (· ∼ ·) := by
  sorry

example : ¬ Reflexive (· ∼ ·) := by
  dsimp [Reflexive]
  push_neg
  use 0
  numbers

example : Symmetric (· ∼ ·) := by
  sorry

example : ¬ Symmetric (· ∼ ·) := by
  dsimp [Symmetric]
  push_neg
  use 0, 1
  constructor <;> numbers

example : AntiSymmetric (· ∼ ·) := by
  dsimp [AntiSymmetric]
  intros x y h1 h2
  have := calc
    0 = x - x := by ring
    _ ≡ y + 1 - x [ZMOD 5] := by rel [h2]
    _ ≡ (x + 1) + 1 - x [ZMOD 5] := by rel [h1]
    _ = 2 := by ring
  numbers at this

example : ¬ AntiSymmetric (· ∼ ·) := by
  sorry

example : Transitive (· ∼ ·) := by
  sorry

example : ¬ Transitive (· ∼ ·) := by
  dsimp [Transitive]
  push_neg
  use 0, 1, 2
  constructor
  · numbers
  · constructor <;> numbers

end

/-# Exercise 4-/

--Exercise 10.1.5.5

section
local infix:50 "∼" => fun (x y : ℤ) ↦ x + y ≡ 0 [ZMOD 3]

example : Reflexive (· ∼ ·) := by
  sorry

example : ¬ Reflexive (· ∼ ·) := by
  dsimp [Reflexive]
  push_neg
  use 1
  numbers

example : Symmetric (· ∼ ·) := by
  dsimp [Symmetric]
  intros x y h
  calc
    y + x = x + y := by ring
    _ ≡ 0 [ZMOD 3] := by rel [h]

example : ¬ Symmetric (· ∼ ·) := by
  sorry

example : AntiSymmetric (· ∼ ·) := by
  sorry

example : ¬ AntiSymmetric (· ∼ ·) := by
  dsimp [AntiSymmetric]
  push_neg
  use 0, 3
  constructor
  · use 1; ring
  · constructor
    · use 1; ring
    · numbers

example : Transitive (· ∼ ·) := by
  sorry

example : ¬ Transitive (· ∼ ·) := by
  dsimp [Transitive]
  push_neg
  use 1, 2, 1
  constructor
  · use 1; numbers
  · constructor
    · use 1; numbers
    · numbers

end

/-# Problem 2-/

--Exercise 10.1.5.6

example : Reflexive ((· : Set ℕ) ⊆ ·) := by
  dsimp [Reflexive]
  intros X
  dsimp [Set.subset_def]
  intros x h
  apply h

example : ¬ Reflexive ((· : Set ℕ) ⊆ ·) := by
  sorry

example : Symmetric ((· : Set ℕ) ⊆ ·) := by
  sorry

example : ¬ Symmetric ((· : Set ℕ) ⊆ ·) := by
  dsimp [Symmetric]
  push_neg
  use ∅, {1}
  constructor
  · dsimp [Set.subset_def]
    intros x contra
    contradiction
  · dsimp [Set.subset_def]
    push_neg
    use 1
    constructor
    · numbers
    · exhaust

example : AntiSymmetric ((· : Set ℕ) ⊆ ·) := by
  dsimp [AntiSymmetric]
  intros X Y h1 h2
  dsimp [Set.subset_def] at h1 h2
  ext a
  have h1a := h1 a
  have h2a := h2 a
  constructor
  · apply h1a
  · apply h2a

example : ¬ AntiSymmetric ((· : Set ℕ) ⊆ ·) := by
  sorry

example : Transitive ((· : Set ℕ) ⊆ ·) := by
  dsimp [Transitive]
  intros X Y Z h1 h2
  dsimp [Set.subset_def] at *
  intros x hx
  apply h2 x (h1 x hx)

example : ¬ Transitive ((· : Set ℕ) ⊆ ·) := by
  sorry
