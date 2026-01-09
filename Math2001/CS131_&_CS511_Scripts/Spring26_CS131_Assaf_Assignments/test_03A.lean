/- 9 January 2026 -/
import Mathlib.Logic.Basic -- basic facts in logic
-- theorems in Lean's mathematics library

-- import Mathlib.Tactic -- Standard library for additional tactics
-- import Mathlib.Tactic.ByContra  -- lighter than 'import' on preceding line
                                -- needed for tactic `by_contra`
-- The next two `imports` are not understood by the Lean_4 Playground.
-- They should be commented out when you run the script in the playground.
import Library.Basic -- needed for tactic `apply?`
import AutograderLib -- **COMMENT OUT IN THE Lean_4 PLAYGROUND**

@[autogradedProof 10]
example : ¬ P ∧ ¬ Q → ¬ (P ∨ Q) := by
  sorry
