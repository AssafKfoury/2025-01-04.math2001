import AutograderLib   -- **COMMENT OUT IN THE Lean_4 PLAYGROUND**
import Mathlib.Logic.Basic

variable (P Q : Prop)

@[autogradedProof 10]
theorem example_2 : ¬ P ∨ ¬ Q → ¬ (P ∧ Q) := by
   sorry
