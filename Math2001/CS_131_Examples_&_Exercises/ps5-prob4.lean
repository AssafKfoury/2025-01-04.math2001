-- The next two imports are needed by the Lean_4 Playground, but not by the
-- autograder. They should be commented out before submission to Gradescope.
-- import Mathlib.Logic.Basic -- **COMMENT OUT BEFORE SUBMISSION TO GRADESCOPE**
-- import Mathlib.Tactic.Ring -- **COMMENT OUT BEFORE SUBMISSION TO GRADESCOPE**

-- The next two imports are not understood by the Lean_4 Playground.
-- They should be commented out when you run the script in the playground.
import Library.Basic -- **COMMENT OUT IN THE Lean_4 PLAYGROUND**
import AutograderLib -- **COMMENT OUT IN THE Lean_4 PLAYGROUND**

open Set

-- def pairs (X Y : Set ℕ) : Set (ℕ × ℕ) := { (x,y) : ℕ × ℕ | (x ∈ X) ∧ (y ∈ Y) }
def pairs (X Y : Set ℕ) : Set (ℕ × ℕ) := { (x,y) | (x ∈ X) (y ∈ Y) }

def evens : Set ℕ := { x | ∃ (k : ℕ), x = 2 * k }
def odds  : Set ℕ := { x | ∃ (k : ℕ), x = 2 * k + 1 }
def EvensOdds := pairs evens odds
#check EvensOdds

#check (25,42)
#eval (25,42).1
#eval (25,42).2
#check [ 2 , 3 ]

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
    have h11 : (m1 , n1) = (m2 , n2) := by rw [h8 , ← h10]
    have h12 : m1 = m2 := by sorry
    have h13 : n1 = n2 := by sorry
    use m1
    constructor ; constructor ; exact h3
    rw [h12] ; exact h5
    use n1
    constructor ; constructor ; exact h7
    rw [h13] ; exact h9
    exact h8
