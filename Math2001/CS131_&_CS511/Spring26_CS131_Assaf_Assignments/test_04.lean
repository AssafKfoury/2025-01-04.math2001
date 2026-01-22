import AutograderLib   -- **COMMENT OUT IN THE Lean_4 PLAYGROUND**
import Mathlib.Logic.Basic

variable (P Q : Prop)

/- # different ways of proving the 3rd deMorgan's "¬ P ∨ ¬ Q → ¬ (P ∧ Q)" -/

example : ¬ P ∨ ¬ Q → ¬ (P ∧ Q) := by
  intro h
  intro h_pq
  obtain ⟨ h_p , h_q ⟩ := h_pq
  obtain  h_np | h_nq  := h
  exact h_np h_p
  exact h_nq h_q

/- obtained by asking Claude AI -/
theorem not_or_not_implies_not_and : ¬P ∨ ¬Q → ¬(P ∧ Q) := by
  intro h
  cases h with
  | inl hnp =>
      intro hpq
      exact hnp hpq.left
  | inr hnq =>
      intro hpq
      exact hnq hpq.right

/- obtained by asking ChatGPT -/
theorem not_and_of_not_or : ¬ P ∨ ¬ Q → ¬ (P ∧ Q) := by
  intro h
  intro hPQ
  cases h with
  | inl hP =>
      exact hP hPQ.left
  | inr hQ =>
      exact hQ hPQ.right

/- obtained by asking Gemini, in tactic mode  -/
 example : ¬ P ∨ ¬ Q → ¬ (P ∧ Q) := by
  -- Introduce the hypothesis `h` which is (¬ P ∨ ¬ Q)
  -- and `hpq` which is (P ∧ Q) because ¬ (P ∧ Q) is sugar for (P ∧ Q) → False
  intro h hpq

  -- Split the 'And' (P ∧ Q) into individual components hp : P and hq : Q
  have hp : P := hpq.left
  have hq : Q := hpq.right

  -- We now split on the 'Or' hypothesis `h` (cases on ¬ P or ¬ Q)
  cases h with
  | inl hnp =>
    -- Case 1: We have ¬ P (hnp)
    -- We have P (hp) and ¬ P (hnp), which is a contradiction.
    exact hnp hp
  | inr hnq =>
    -- Case 2: We have ¬ Q (hnq)
    -- We have Q (hq) and ¬ Q (hnq), which is a contradiction.
    exact hnq hq

/- obtained by asking Gemini, in term mode -/
example : ¬ P ∨ ¬ Q → ¬ (P ∧ Q)
  -- If the left side (¬ P) is true, ignore Q, and apply ¬ P to P
  | Or.inl hnp, ⟨hp, _⟩ => hnp hp
  -- If the right side (¬ Q) is true, ignore P, and apply ¬ Q to Q
  | Or.inr hnq, ⟨_, hq⟩ => hnq hq
