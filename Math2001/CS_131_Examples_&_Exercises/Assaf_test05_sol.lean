import Library.Basic 
import AutograderLib 
import Mathlib.Tactic.PushNeg 
import Mathlib.Logic.Basic 

axiom associative1 {p q r : Prop} : (p ∨ q) ∨ r ↔ p ∨ (q ∨ r)
axiom associative2 {p q r : Prop} : (p ∧ q) ∧ r ↔ p ∧ (q ∧ r)
axiom distributive1 {p q r : Prop} : p ∨ (q ∧ r) ↔ (p ∨ q) ∧ (p ∨ r)
axiom distributive2 {p q r : Prop} : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r)
axiom identity1 {p : Prop} : p ∨ False ↔ p
axiom identity2 {p : Prop} : p ∧ True ↔ p
axiom domination1 {p : Prop} : p ∧ False ↔ False
axiom domination2 {p : Prop} : p ∨ True ↔ True
axiom doublenegation {p : Prop} : ¬¬p ↔ p
axiom complement1 {p : Prop} : p ∧ ¬p ↔ False
axiom complement2 {p : Prop} : p ∨ ¬p ↔ True
axiom commutative1 {p q : Prop} : p ∨ q ↔ q ∨ p
axiom commutative2 {p q : Prop} : p ∧ q ↔ q ∧ p
axiom idempotent1 {p : Prop} : p ∨ p ↔ p
axiom idempotent2 {p : Prop} : p ∧ p ↔ p
axiom demorgan1 {p q : Prop} : ¬(p ∨ q) ↔ ¬p ∧ ¬q
axiom demorgan2 {p q : Prop} : ¬(p ∧ q) ↔ ¬p ∨ ¬q
axiom absorption1 {p q : Prop} : p ∨ (p ∧ q) ↔ p
axiom absorption2 {p q : Prop} : p ∧ (p ∨ q) ↔ p
axiom conditional1 {p q : Prop} : p → q ↔ ¬p ∨ q
axiom conditional2 {p q : Prop} : (p ↔ q) ↔ (p → q) ∧ (q → p)

@[autogradedProof 5]
theorem prob_6_ps1_b (A M W : Prop) : 
          (¬ M ∨ ¬ W) ∧  ¬ (A ∧ M ∧ W) ↔ (¬ M ∨ ¬ W) := by
  constructor
  intro h
  obtain ⟨ h1 , h2 ⟩ := h 
  -- rw [← demorgan2] ; rw [← demorgan2] at h1 ;
  exact h1 
  intro h1 
  constructor ; exact h1
  rw [← demorgan2] at h1 ; rw [demorgan2] ; right ; exact h1  