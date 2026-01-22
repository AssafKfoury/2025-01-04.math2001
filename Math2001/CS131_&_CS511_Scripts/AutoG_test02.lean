import AutograderLib   -- **COMMENT OUT IN THE Lean_4 PLAYGROUND**
import Mathlib.Logic.Basic

variable (P Q : Prop)

/- # different ways of proving the 3rd deMorgan's "¬ P ∨ ¬ Q → ¬ (P ∧ Q)" -/

@[autogradedProof 10]
theorem example_2 : ¬ P ∨ ¬ Q → ¬ (P ∧ Q) := by
  intro h
  intro h_pq
  obtain ⟨ h_p , h_q ⟩ := h_pq
  obtain  h_np | h_nq  := h
  exact h_np h_p
  exact h_nq h_q
