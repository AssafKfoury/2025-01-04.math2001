/- 9 January 2026 -/
import Mathlib.Logic.Basic
import Library.Basic
import AutograderLib   -- **COMMENT OUT IN THE Lean_4 PLAYGROUND**

variable (P Q : Prop)

@[autogradedProof 10]
example : ¬ P ∧ ¬ Q → ¬ (P ∨ Q) := by
  intro h
  intro h_pos
  obtain ⟨ h_np , h_nq ⟩ := h
  obtain h_pos1 | h_pos2 := h_pos
  exact h_np h_pos1
  exact h_nq h_pos2
