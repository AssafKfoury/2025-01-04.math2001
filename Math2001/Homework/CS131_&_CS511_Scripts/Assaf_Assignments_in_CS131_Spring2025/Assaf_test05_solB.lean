import Library.Basic 
import AutograderLib 
import Mathlib.Tactic.PushNeg 
import Mathlib.Logic.Basic 

axiom demorgan2 {p q : Prop} : ¬(p ∧ q) ↔ ¬p ∨ ¬q

@[autogradedProof 5]
theorem prob_6_ps1 (A M W : Prop) : 
          (¬ M ∨ ¬ W) ∧  ¬ (A ∧ M ∧ W) ↔ (¬ M ∨ ¬ W) := by
  constructor
  · intro h
    obtain ⟨ h1 , h2 ⟩ := h 
    exact h1 
  · intro h1 
    constructor ; exact h1
    rw [demorgan2] ; right ; rw [demorgan2] ; exact h1 
