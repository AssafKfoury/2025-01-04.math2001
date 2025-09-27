/- CS 511, 26 Sept 2025 -/
/- solution for Exercise 4 in Homework Assignment 04 -/

import Mathlib.Logic.Basic
import Mathlib.Tactic.ByContra

lemma prove_implication_negation (p q : Prop) : (p → q) → ¬ (p ∧ ¬ q) := by
  intro h_pq
  by_contra h_pnq
  obtain ⟨ h_p , h_nq ⟩ := h_pnq
  have h_q : q := h_pq h_p
  contradiction

lemma prove_negation_implication (p q : Prop) :  ¬ (p ∧ ¬ q) → (p → q) := by
  intro h_neg_pnq
  intro h_p
  by_cases h_q : q
  exact h_q
  have h_pnq : (p ∧ ¬ q) := And.intro h_p h_q
  contradiction

example {p q : Prop} : (p → q) → (¬p ∨ q)  := by
  intro h_pq
  have h_neg_pnq : ¬ (p ∧ ¬ q) := by
     apply prove_implication_negation
     exact h_pq
  -- push_neg at h_pq
  sorry

example {p q : Prop} : (¬q → ¬p) → (p → q) := by
  intro h_nqnp
  apply prove_negation_implication
  sorry

example {p q : Prop} : (((p → q) → p) → p) := sorry

lemma de_morgan_4 (P Q : Prop) : ¬ (P ∧ Q) → (¬ P ∨ ¬ Q) := by
  intro h1
  by_cases hP : P
  · right
    intro hQ
    apply h1
    constructor
    exact hP
    exact hQ
  · left
    exact hP

/- constructor
  · intro h
    by_cases hP : P
    · right
      intro hQ
      have hPQ : P ∧ Q
      · constructor
        · apply hP
        · apply hQ
      contradiction
    · left
      apply hP
  · sorry
-/

/-
example (P Q : Prop) : ¬ (P ∧ Q) ↔ (¬ P ∨ ¬ Q) := by
  constructor
  · intro h
    by_cases hP : P
    · right
      intro hQ
      have hPQ : P ∧ Q
      · constructor
        · apply hP
        · apply hQ
      contradiction
    · left
      apply hP
  · sorry
-/
