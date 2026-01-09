import Mathlib.Data.Real.Basic
import Library.Basic
import Library.Tactic.Rel
import AutograderLib

math2001_init
set_option pp.funBinderTypes true

--Exercise 5.1.7.6

@[autograded 2]
example {P Q R : Prop} (h : P ↔ Q) : (P ∧ R) ↔ (Q ∧ R) := by
  sorry

--Exercise 5.1.7.8

@[autograded 2]
example (P Q : Prop) : (P ∨ Q) ↔ (Q ∨ P) := by
  sorry

--Exercise 5.1.7.9

@[autograded 2]
example (P Q : Prop) : ¬(P ∨ Q) ↔ (¬P ∧ ¬Q) := by
  sorry

--Exercise 5.1.7.11

@[autograded 2]
example {P Q : α → Prop} (h : ∀ x, P x ↔ Q x) : (∃ x, P x) ↔ (∃ x, Q x) := by
  sorry

--Exercise 5.1.7.12

@[autograded 2]
example (P : α → β → Prop) : (∃ x y, P x y) ↔ ∃ y x, P x y := by
  sorry

--Exercise 5.1.7.13

@[autograded 2]
example (P : α → β → Prop) : (∀ x y, P x y) ↔ ∀ y x, P x y := by
  sorry

--Exercise 5.1.7.14

@[autograded 3]
example (P : α → Prop) (Q : Prop) : ((∃ x, P x) ∧ Q) ↔ ∃ x, (P x ∧ Q) := by
  sorry

--Exercise 5.2.7.2

@[autograded 3]
example (P Q : Prop) : (¬P → ¬Q) ↔ (Q → P) := by
  sorry
