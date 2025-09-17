-- The next two imports are needed by the Lean_4 Playground, but not by the
-- autograder. They should be commented out before submission to Gradescope.
-- import Mathlib.Logic.Basic -- **COMMENT OUT BEFORE SUBMISSION TO GRADESCOPE**
-- import Mathlib.Tactic.Ring -- **COMMENT OUT BEFORE SUBMISSION TO GRADESCOPE**

-- The next two imports are not understood by the Lean_4 Playground
-- and should be commented out when you run the script in the playground.
import Library.Basic -- **DE-COMMENT BEFORE SUBMISSION TO GRADESCOPE**
import AutograderLib -- **DE-COMMENT BEFORE SUBMISSION TO GRADESCOPE**

open Int

@[autogradedProof 7]
theorem problem1 {a b : ℤ} : a ∣ b → a ^ 2 ∣ b ^ 2 := by
  sorry

/- We recommend these first 8 lines to start off problem3.  These lines are a translation
of what we did in lab.

  intro hOdd
  dsimp [Odd] at hOdd
  obtain ⟨k,hk⟩ := hOdd
  dsimp [(.∣.)]
  rw [hk]
  have hFactor : (2*k + 1) ^ 2 - 1 = 4*k * (k + 1) := by ring
  rw [hFactor]
  by_cases hCases : Odd k
-/

@[autogradedProof 7]
theorem problem3 {x : ℤ} : Odd x → 8 ∣ x ^ 2 - 1 := by
  sorry
