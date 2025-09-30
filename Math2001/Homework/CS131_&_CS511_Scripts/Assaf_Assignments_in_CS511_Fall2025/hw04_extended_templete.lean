/- ## CS 511, 26 Sept 2025 -/
import Mathlib.Data.Real.Basic
       -- there is no need to import `Mathlib` or `Mathlib.Tactic`
       -- in full, which are enormous modules taking time to be imported
import Library.Basic
       -- module `Library.Basic` must be imported for Macbeth's tactics:
       -- ## `extra`, `numbers`, `cancel`, `addarith [h]` ##
       -- and Macbeth's environment `math2001_init`
import Library.Tactic.Induction

math2001_init

/- ## three proofs for Exercise 3 in Homework Assignment 04 -/

example : ∃ m n : ℤ, m ^ 2 - n ^ 2 = 11 := by
  use 6, 5
  sorry

example (a : ℤ) : ∃ m n : ℤ, m ^ 2 - n ^ 2 = 2 * a + 1 := by
  use a + 1, a
  sorry

example {p q : ℝ} (h : p < q) : ∃ x, p < x ∧ x < q := by
  use (p + q)/2
  constructor
  · sorry

  · sorry


/- ## three proofs for Exercise 4 in Homework Assignment 04 -/

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
  · -- case 1, with new hypothesis h_q : q
    exact h_q
  · -- case 2, with new hypothesis h_q : ¬ q
    have h_pnq : (p ∧ ¬ q) := And.intro h_p h_q
    contradiction

lemma de_morgan_4 (P Q : Prop) : ¬ (P ∧ Q) → (¬ P ∨ ¬ Q) := by
  intro h1
  by_cases hP : P
  · -- case 1, with new hypothesis hP : P
    right
    intro hQ
    apply h1
    constructor
    exact hP
    exact hQ
  · -- case 2, with new hypothesis hP : ¬ P
    left
    exact hP

/- ## first proof for Exercise 4 -/
example {p q : Prop} : (p → q) → (¬p ∨ q)  := by
  intro h_pq
  have h_neg_pnq : ¬ (p ∧ ¬ q) := by
     apply imply_to_negate
     exact h_pq
  by_cases h_p : p
  · -- case 1, with new hypothesis h_p : p
    sorry
  · -- case 2, with new hypothesis h_p : ¬ p
    sorry

/- ## second proof for Exercise 4 -/
example {p q : Prop} : (¬q → ¬p) → (p → q) := by
  intro h_nqnp
  sorry

/- ## third proof for Exercise 4 ,
   which proves so-called Peirce's Law which was already proved in
   different ways in the script `forward_backward_reasoning.lean`,
   the following is a proof from that script (the last one) -/
example {p q : Prop} : (((p → q) → p) → p) := by
  sorry

/- ## two proofs for Problem 2 in Homework Assignment 04 -/

example : forall_sufficiently_large n : ℕ, 2 ^ n ≥ n ^ 2 := by
  dsimp
  use 4
  intro n hn
  induction_from_starting_point n, hn with k hk IH
  · -- base case
    calc 2 ^ 4 = 16      := by ring -- `exact rfl` will also work
             _ = 4 ^ 2   := by ring -- `exact rfl` will also work
             _ ≥ 4 ^ 2   := by numbers
  · -- inductive step
    sorry

example : forall_sufficiently_large n : ℕ, 2 ^ n ≥ n ^ 3 := by
  dsimp
  use 10
  intro n ; intro hn
  induction_from_starting_point n, hn with k hk IH
  · -- base case
    numbers
  · -- inductive step
    sorry
