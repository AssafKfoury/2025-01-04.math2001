import Library.Basic 
import AutograderLib 
import Mathlib.Tactic.PushNeg 
import Mathlib.Logic.Basic 

axiom demorgan2 {p q : Prop} : ¬(p ∧ q) ↔ ¬p ∨ ¬q

lemma de_Morgan2 { p q : Prop } : ¬( p ∧ q ) ↔ ¬p ∨ ¬q := by
  constructor
  intro h1 ; rw [← demorgan2] ; exact h1
  intro h1 ; push_neg 
  obtain h2 | h3 := h1 
  intro h4 ; contradiction 
  intro h5 ; exact h3

@[autogradedProof 5]
theorem prob_6_ps1_b (A M W : Prop) : 
          (¬ M ∨ ¬ W) ∧  ¬ (A ∧ M ∧ W) ↔ (¬ M ∨ ¬ W) := by
  constructor
  intro h
  obtain ⟨ h1 , h2 ⟩ := h 
  exact h1 
  intro h1 
  constructor ; exact h1 
  rw [de_Morgan2] ; right ; rw [de_Morgan2]
  exact h1  
  
  
   