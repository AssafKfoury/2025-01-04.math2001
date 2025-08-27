-- The next two imports are needed by the Lean_4 Playground, but not by the
-- autograder. They should be commented out before submission to Gradescope.
-- import Mathlib.Logic.Basic -- **COMMENT OUT BEFORE SUBMISSION TO GRADESCOPE**
-- import Mathlib.Tactic.Ring -- **COMMENT OUT BEFORE SUBMISSION TO GRADESCOPE**

-- The next two imports are not understood by the Lean_4 Playground
-- and should be commented out when you run the script in the playground.
import Library.Basic -- **DE-COMMENT BEFORE SUBMISSION TO GRADESCOPE**
import AutograderLib -- **DE-COMMENT BEFORE SUBMISSION TO GRADESCOPE**

open Function
open Set

def pairs (X Y : Set ℕ) : Set (ℕ × ℕ) := { (x,y) | (x ∈ X) (y ∈ Y) }

def evens : Set ℕ := { x | ∃ (k : ℕ), x = 2 * k }
def odds  : Set ℕ := { x | ∃ (k : ℕ), x = 2 * k + 1 }
def EvensOdds := pairs evens odds
#check EvensOdds

#check (25,42)
#eval (25,42).1
#eval (25,42).2
#check [ 2 , 3 ]

@[autogradedProof 10]
theorem problem2 {A B C D : Set ℕ} :
        (pairs A C) ∩ (pairs B D) ⊆ (pairs (A ∩ B) (C ∩ D)) := by
    dsimp [subset_def]
    intro h ; intro ha
    dsimp [pairs] at *
    obtain ⟨ h1 , h2 ⟩ := ha ;
    obtain ⟨ m1 , hm1 ⟩ := h1  ; obtain ⟨ m2 , hm2 ⟩ := h2
    obtain ⟨ h3 , h4 ⟩  := hm1 ; obtain ⟨ h5 , h6 ⟩  := hm2
    obtain ⟨ n1 , hn1 ⟩ := h4  ; obtain ⟨ n2 , hn2 ⟩ := h6
    obtain ⟨ h7 , h8 ⟩  := hn1 ; obtain ⟨ h9 , h10 ⟩ := hn2
    use h.1
    constructor ; constructor ; rw [← h8] ; exact h3
    rw [← h10] ; exact h5
    use h.2
    constructor ; constructor ; rw [← h8] ; exact h7
    rw [← h10] ; exact h9
    ring

@[autogradedProof 10]
theorem problem4 : Injective (fun (x : ℕ) ↦ (x + 2)^2) := by
  dsimp [Injective]
  intros a1 a2 ha
  rw [pow_left_inj] at ha
  addarith [ha]
  extra
  extra
  numbers
