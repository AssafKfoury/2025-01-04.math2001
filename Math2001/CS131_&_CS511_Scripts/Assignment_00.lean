/- 9 January 2026 -/
import Mathlib.Logic.Basic
import AutograderLib   -- **COMMENT OUT IN THE Lean_4 PLAYGROUND**

variable (P Q : Prop)

@[autogradedProof 10]
example : ¬ P ∧ ¬ Q → ¬ (P ∨ Q) := by
   sorry
