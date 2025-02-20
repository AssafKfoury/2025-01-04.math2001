-- The next two imports are needed by the Lean_4 Playground, but not by the
-- autograder. They should be commented out before submission to Gradescope.
-- import Mathlib.Logic.Basic -- **COMMENT OUT BEFORE SUBMISSION TO GRADESCOPE**
-- import Mathlib.Tactic.Ring -- **COMMENT OUT BEFORE SUBMISSION TO GRADESCOPE**

-- The next two imports are not understood by the Lean_4 Playground
-- and should be commented out when you run the script in the playground.
import Library.Basic -- **DE-COMMENT BEFORE SUBMISSION TO GRADESCOPE**
import AutograderLib -- **DE-COMMENT BEFORE SUBMISSION TO GRADESCOPE**

open Set

-- use dsimp [Set.subset_def] to unwrap the set notation into
-- logic notation and then solve as normal
-- make sure to read previous solutions to Lean problems if you need help as well

@[autogradedProof 15]
theorem problem1 : {n | 1331 ∣ n} ⊆ {n | 121 ∣ n} := by
    dsimp [Set.subset_def]
    intros x hx
    dsimp [(.∣.)] at *
    obtain ⟨k,hk⟩ := hx
    use 11 * k
    rw [hk]
    ring
    done
