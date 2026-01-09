/- 7 January 2026 -/
import Mathlib.Logic.Basic -- basic facts in logic
-- theorems in Lean's mathematics library
-- preceding two lines taken from canned example "Logic" in the palyground

-- import Mathlib.Tactic -- Standard library for additional tactics
import Mathlib.Tactic.ByContra  -- lighter than 'import' on preceding line
                                -- needed for tactic 'by_contra'
import Library.Basic -- needed for tactic 'apply?'
/- # TWO NEXT EXAMPLES +
   # comments are taken from canned example "logic" in the playground -/
-- Let P and Q be true-false statements
variable (P Q : Prop)

-- The following is a basic result in logic
example : ¬ (P ∧ Q) ↔ ¬ P ∨ ¬ Q := by
  -- its proof is already in Lean's mathematics library
  exact not_and_or

-- Here is another basic result in logic
example : ¬ (P ∨ Q) ↔ ¬ P ∧ ¬ Q := by
  apply? -- we can search for the proof in the library
  -- we can also replace `apply?` with its output

/- # EVERYTHING BELOW THIS LINE is Assaf's script -/
/- # different ways of proving the 4th deMorgan's "¬ (P ∧ Q) → ¬ P ∨ ¬ Q" -/

example : ¬ (P ∧ Q) → ¬ P ∨ ¬ Q := by
   intro h
   exact not_and_or.mp h    -- obtained by trying tactic "apply?"

example : ¬ (P ∧ Q) → ¬ P ∨ ¬ Q := by
  intro h
  -- Use double negation/contradiction to move forward
  by_contra h_neg
  -- h_neg is now: ¬ (¬ P ∨ ¬ Q)

  -- We want to show (P ∧ Q) to contradict 'h'
  -- To do this, we use 'specialize' on our contradiction hypothesis
  have hp : P := by
    by_contra h_np
    -- Specialize h_neg by providing a proof of (¬ P ∨ ¬ Q)
    have hhh : (¬ P ∨ ¬ Q) := Or.inl h_np
    specialize h_neg hhh -- (Or.inl h_np)
    exact h_neg

  have hq : Q := by
    by_contra h_nq
    -- Specialize h_neg by providing a proof of (¬ P ∨ ¬ Q)
    specialize h_neg (Or.inr h_nq)
    exact h_neg

  -- Now we have P and Q, so we have (P ∧ Q)
  have hhhh : P ∧ Q := ⟨ hp , hq ⟩
  exact h hhhh -- ⟨hp, hq⟩

/- without tactic 'specialize' -/
example : ¬ (P ∧ Q) → ¬ P ∨ ¬ Q := by
  intro h
  by_cases hP : P
  · by_cases hQ : Q
    · exfalso
      apply h
      exact ⟨hP, hQ⟩
    · exact Or.inr hQ
  · exact Or.inl hP
/- without tactic 'exfalso' -/
example : ¬ (P ∧ Q) → ¬ P ∨ ¬ Q := by
  intro h
  by_cases hP : P
  · by_cases hQ : Q
    · have hPQ : P ∧ Q := ⟨hP, hQ⟩
      have : False := h hPQ
      contradiction
    · exact Or.inr hQ
  · exact Or.inl hP
/- without tactics 'exfalso' and 'contradiction' -/
example : ¬ (P ∧ Q) → ¬ P ∨ ¬ Q := by
  intro h
  by_cases hP : P
  · by_cases hQ : Q
    · -- This creates a contradiction directly
      exact False.elim (h ⟨hP, hQ⟩)
    · exact Or.inr hQ
  · exact Or.inl hP
/- using 'apply' and 'have' -/
example : ¬ (P ∧ Q) → ¬ P ∨ ¬ Q := by
  intro h
  by_cases hP : P
  · by_cases hQ : Q
    · -- Apply h to the conjunction to get False
      have : False := h ⟨hP, hQ⟩
      -- From False, we can prove anything
      exact False.elim this
    · exact Or.inr hQ
  · exact Or.inl hP
/- without any explicit 'False' elimination -/
example : ¬ (P ∧ Q) → ¬ P ∨ ¬ Q := by
  intro h
  by_cases hP : P
  · by_cases hQ : Q
    · -- h : ¬(P ∧ Q) and we have P ∧ Q, so we have a contradiction
      -- We can use this contradiction to prove our goal
      exact (h ⟨hP, hQ⟩).rec
    · exact Or.inr hQ
  · exact Or.inl hP
/- using lambda notation -/
example : ¬ (P ∧ Q) → ¬ P ∨ ¬ Q := by
  intro h
  by_cases hP : P
  · refine by_cases (λ hQ : Q => ?_) (λ hQ => Or.inr hQ)
    exact (h ⟨hP, hQ⟩).elim
  · exact Or.inl hP
