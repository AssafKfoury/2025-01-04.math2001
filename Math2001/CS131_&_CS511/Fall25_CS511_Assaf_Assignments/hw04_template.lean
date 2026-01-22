/- CS 511, 26 Sept 2025 -/
/- template for Exercise 4 in Homework Assignment 04 -/

import Mathlib.Logic.Basic
import Mathlib.Tactic.ByContra

lemma prove_implication_negation (p q : Prop) : (p → q) → ¬ (p ∧ ¬ q) := by
  intro h_pq       -- introduce hypothesis h_pq : p → q
  by_contra h_pnq  -- introduce hypothesis h_pnq : p ∧ ¬ q
  obtain ⟨ h_p , h_nq ⟩ := h_pnq  -- break up h_npnq into h_p : p and h_nq : ¬ q
  have h_q : q := h_pq h_p -- introduce hypothesis h_q : q by applying h_pq to h_p
  contradiction    -- complete proof immediately by the contradiction { h_nq , h_q }

lemma prove_negation_implication (p q : Prop) :  ¬ (p ∧ ¬ q) → (p → q) := by
  intro h_neg_pnq    -- introduce hypothesis h_neg_pnq : ¬ (p ∧ q)
  intro h_p          -- introduce hypothesis h_p : p
  by_cases h_q : q   -- consider two cases: (1) q is true, (2) q is false, resulting in 2 goals
  exact h_q          -- complete first goal
  have h_pnq : (p ∧ ¬ q) := And.intro h_p h_q
  contradiction  -- complete the proof immediately by the contradiction { h_pnq , h_neg_pnq }

example {p q : Prop} : (p → q) → (¬p ∨ q)  := sorry
example {p q : Prop} : (¬q → ¬p) → (p → q) := sorry
example {p q : Prop} : (((p → q) → p) → p) := sorry
