/- 9 January 2026 -/
import AutograderLib   -- **COMMENT OUT IN THE Lean_4 PLAYGROUND**
import Mathlib.Logic.Basic

variable (P Q : Prop)

@[autogradedProof 10]
example : ¬ P ∧ ¬ Q → ¬ (P ∨ Q) := by
   sorry
