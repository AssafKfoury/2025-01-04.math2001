import AutograderLib   -- **COMMENT OUT IN THE Lean_4 PLAYGROUND**
import Mathlib.Logic.Basic

variable (P Q : Prop)

/- # different ways of proving the 3rd deMorgan's "¬ P ∨ ¬ Q → ¬ (P ∧ Q)" -/

@[autogradedProof 10]
theorem example_2 : ¬ P ∨ ¬ Q → ¬ (P ∧ Q) := by
   sorry
