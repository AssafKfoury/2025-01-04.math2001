-- The next two imports are needed by the Lean_4 Playground, but not by the
-- autograder. They should be commented out before submission to Gradescope.
-- import Mathlib.Logic.Basic -- **COMMENT OUT BEFORE SUBMISSION TO GRADESCOPE**
-- import Mathlib.Tactic.Ring -- **COMMENT OUT BEFORE SUBMISSION TO GRADESCOPE**

-- The next two imports are not understood by the Lean_4 Playground
-- and should be commented out when you run the script in the playground.
import Library.Basic -- **DE-COMMENT BEFORE SUBMISSION TO GRADESCOPE**
import AutograderLib -- **DE-COMMENT BEFORE SUBMISSION TO GRADESCOPE**

variable {A : Type}

def Lottian (R : A → A → Prop) : Prop :=
  ∀ x y z, R x y → R x z → R y z

variable (R : A → A → Prop)

/-
Prove that if a relation is Lottian and reflexive, then it is an equivalence relation.
Hint:  First introduce the assumptions and unfold the definitions with the following lines:
  intros h1 h2
  dsimp [Lottian] at h1
  dsimp [Reflexive] at h2
  dsimp [Symmetric]
  dsimp [Transitive]
 -/

@[autogradedProof 8]
theorem problem2b : Lottian R → Reflexive R → (Symmetric R ∧ Transitive R) := by
  sorry
