/- 8 January 2026 -/
import Mathlib.Logic.Basic -- basic facts in logic
-- theorems in Lean's mathematics library
-- preceding two lines taken from canned example "Logic" in the palyground

-- import Mathlib.Tactic -- Standard library for additional tactics
import Mathlib.Tactic.ByContra  -- lighter than 'import' on preceding line
                                -- needed for tactic `by_contra`
import Library.Basic -- needed for tactic `apply?`

/- # NEXT EXAMPLE +
   # comments are taken from canned example "Logic" in the playground -/
-- Let P and Q be true-false statements
variable (P Q : Prop)

-- A basic result in logic, deMorgan's laws 1 and 2
example : ¬ (P ∨ Q) ↔ ¬ P ∧ ¬ Q := by
  apply? -- we can search for the proof in the library
  -- we can also replace `apply?` with its output

/- # EVERYTHING BELOW THIS LINE is Assaf's script -/
/- # different ways of proving deMorgan's law 2 "¬ P ∧ ¬ Q → ¬ (P ∨ Q)" -/

example : ¬ P ∧ ¬ Q → ¬ (P ∨ Q) := by
  intro h
  -- to prove a negation, use `by_contra`
  by_contra h_pos
  -- h_pos is now: P ∨ Q

  -- From the conjunction h, we can extract ¬ P and ¬ Q
  have h_np : ¬ P := And.left h
  have h_nq : ¬ Q := And.right h

  -- Now we do case analysis on h_pos (P ∨ Q)
  cases h_pos with
  | inl hP =>
    -- hP : P
    exact h_np hP -- contradiction
  | inr hQ =>
    -- hQ : Q
    exact h_nq hQ -- contradiction

/- -/
example : ¬ P ∧ ¬ Q → ¬ (P ∨ Q) := by
  intro h
  intro h_pos
  obtain h_pos1 | h_pos2 := h_pos
  exact (And.left h) h_pos1
  exact (And.right h) h_pos2

/- without tactics `And.left` and `And.right` -/
example : ¬ P ∧ ¬ Q → ¬ (P ∨ Q) := by
  intro h
  intro h_pos
  obtain ⟨ h_np , h_nq ⟩ := h
  obtain h_pos1 | h_pos2 := h_pos
  exact h_np h_pos1
  exact h_nq h_pos2
