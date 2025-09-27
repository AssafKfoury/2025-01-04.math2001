/- ## CS 511, 26 Sept 2025 -/
/- ## three proofs for Exercise 4 in Homework Assignment 04 -/

import Mathlib.Logic.Basic
import Mathlib.Tactic.ByContra
import Mathlib.Tactic.Contrapose

lemma imply_to_negate (p q : Prop) : (p → q) → ¬ (p ∧ ¬ q) := by
  intro h_pq
  by_contra h_pnq
  obtain ⟨ h_p , h_nq ⟩ := h_pnq
  have h_q : q := h_pq h_p
  contradiction

lemma negate_to_imply (p q : Prop) :  ¬ (p ∧ ¬ q) → (p → q) := by
  intro h_neg_pnq
  intro h_p
  by_cases h_q : q
  · exact h_q
  · have h_pnq : (p ∧ ¬ q) := And.intro h_p h_q
    contradiction

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

/- ## first proof for Exercise 4 -/
example {p q : Prop} : (p → q) → (¬p ∨ q)  := by
  intro h_pq
  have h_neg_pnq : ¬ (p ∧ ¬ q) := by
     apply imply_to_negate
     exact h_pq
  by_cases h_p : p
  · right
    have h_q : q := h_pq h_p
    exact h_q
  · left
    exact h_p

/- ## second proof for Exercise 4 -/
example {p q : Prop} : (¬q → ¬p) → (p → q) := by
  intro h_nqnp
  contrapose
  exact h_nqnp

/- ## third proof for Exercise 4 ,
   which proves so-called Peirce's Law which was already proved in
   different ways in the script `forward_backward_reasoning.lean`,
   the following is a proof from that script (the last one) -/
example {p q : Prop} : (((p → q) → p) → p) := by
  intro H_pqp
  by_contra H_np
  have H_pq : p → q := by
     intro H_p
     contradiction
  have H_p : p := H_pqp H_pq
  contradiction
