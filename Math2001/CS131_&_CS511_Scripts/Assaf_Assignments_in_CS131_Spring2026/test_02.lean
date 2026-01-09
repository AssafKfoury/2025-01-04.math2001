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
/- # different ways of proving deMorgan's law 1 "¬ (P ∨ Q) → ¬ P ∧ ¬ Q" -/

example : ¬ (P ∨ Q) → ¬ P ∧ ¬ Q := by
  intro h
  -- to prove a conjunction, prove each part separately
  constructor
  · -- first part: ¬ P
    by_contra h_np
    -- from h_np we get (P ∨ Q)
    have hhh : P ∨ Q := Or.inl h_np
    exact h hhh
  · -- second part: ¬ Q
    by_contra h_nq
    -- from h_nq we get (P ∨ Q)
    have hhh : P ∨ Q := Or.inr h_nq
    exact h hhh

/- without tactic `constructor` -/
example : ¬ (P ∨ Q) → ¬ P ∧ ¬ Q := by
  intro h
  -- to prove a conjunction, prove each part separately
  have h1 : ¬ P := by
    by_contra h_np -- `intro` can be used here as well
    -- from h_np we get (P ∨ Q)
    have hhh : P ∨ Q := Or.inl h_np
    exact h hhh
  have h2 : ¬ Q := by
    by_contra h_nq -- `intro` can be used here as well
    -- from h_nq we get (P ∨ Q)
    have hhh : P ∨ Q := Or.inr h_nq
    exact h hhh
  -- Now combine the two parts into a conjunction
  exact And.intro h1 h2

/- without tactic `And.intro` -/
example : ¬ (P ∨ Q) → ¬ P ∧ ¬ Q := by
  intro h
  -- to prove a conjunction, prove each part separately
  have h1 : ¬ P := by
    intro h_np
    -- from h_np we get (P ∨ Q)
    have hhh : P ∨ Q := Or.inl h_np
    exact h hhh
  have h2 : ¬ Q := by
    intro h_nq
    -- from h_nq we get (P ∨ Q)
    have hhh : P ∨ Q := Or.inr h_nq
    exact h hhh
  -- Now combine the two parts into a conjunction
  have h_conj : ¬ P ∧ ¬ Q := ⟨h1 , h2⟩
  exact h_conj -- h_conj is of type ¬ P ∧ ¬ Q
