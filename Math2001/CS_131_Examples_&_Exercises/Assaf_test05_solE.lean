import Library.Basic 
import AutograderLib 
import Mathlib.Tactic.PushNeg 
import Mathlib.Logic.Basic 

axiom demorgan2 {p q : Prop} : ¬(p ∧ q) ↔ ¬p ∨ ¬q

axiom notnot.Elim : ∀ {p : Prop}, ¬ ¬ p → p

 lemma de_Morgan2 { p q : Prop } : ¬( p ∧ q ) ↔ ¬p ∨ ¬q := by
  constructor 
  · intro h1 
    apply notnot.Elim 
    intro h2 
    push_neg at h2 ; contradiction 
  · intro h1
    obtain h3 | h4 := h1
    intro h5 
    obtain ⟨ h6 , h7 ⟩ := h5 ; contradiction 
    intro h8 
    obtain ⟨ h9, h10 ⟩ := h8 ; contradiction 

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