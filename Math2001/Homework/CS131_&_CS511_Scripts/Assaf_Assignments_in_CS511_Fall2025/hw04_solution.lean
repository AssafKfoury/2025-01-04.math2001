/- ## CS 511, 26 Sept 2025 -/
import Mathlib.Data.Real.Basic
-- import Library.Theory.Comparison
-- import Library.Tactic.Addarith
-- import Library.Tactic.Cancel
-- import Library.Tactic.Numbers
-- import Library.Tactic.Extra
-- import Library.Tactic.Use
import Library.Tactic.Induction

-- attribute [-instance] Int.instDivInt_1 Int.instDivInt EuclideanDomain.instDiv Nat.instDivNat

notation3 (prettyPrint := false) "forall_sufficiently_large "(...)", "r:(scoped P => ∃ C, ∀ x ≥ C, P x) => r



/-
import Mathlib.Logic.Basic
import Mathlib.Data.Real.Basic
mport Mathlib.Tactic.ByContra
import Mathlib.Tactic.Contrapose
import Library.Theory.Comparison
import Library.Tactic.Addarith
import Library.Tactic.Cancel
import Library.Tactic.Numbers
import Library.Tactic.Extra
import Library.Tactic.Use
import Library.Tactic.Induction

/- From Macbeth's solution:
import Mathlib.Data.Real.Basic
import Library.Theory.Comparison
import Library.Tactic.Addarith
import Library.Tactic.Cancel
import Library.Tactic.Numbers
import Library.Tactic.Extra
import Library.Tactic.Use

-/

/-
import Mathlib.Data.Real.Basic
import Library.Theory.Parity
import Library.Tactic.Addarith
import Library.Tactic.Induction
import Library.Tactic.Numbers
import Library.Tactic.Extra
import Library.Tactic.Use

attribute [-instance] Int.instDivInt_1 Int.instDivInt EuclideanDomain.instDiv Nat.instDivNat
set_option linter.unusedVariables false

namespace Nat

notation3 (prettyPrint := false) "forall_sufficiently_large "(...)", "r:(scoped P => ∃ C, ∀ x ≥ C, P x) => r
-/

attribute [-instance] Int.instDivInt_1 Int.instDivInt EuclideanDomain.instDiv Nat.instDivNat
set_option linter.unusedVariables false

namespace Nat

notation3 (prettyPrint := false) "forall_sufficiently_large "(...)", "r:(scoped P => ∃ C, ∀ x ≥ C, P x) => r
-/

/- ## three proofs for Exercise 3 in Homework Assignment 04 -/

example : ∃ m n : ℤ, m ^ 2 - n ^ 2 = 11 := by
  use 6, 5
  ring

example (a : ℤ) : ∃ m n : ℤ, m ^ 2 - n ^ 2 = 2 * a + 1 := by
  use a + 1, a
  ring

example {p q : ℝ} (h : p < q) : ∃ x, p < x ∧ x < q := by
  use (p + q)/2
  constructor
  · calc
      p = (p + p)/2 := by ring
      _ < (p + q)/2 := by rel [h]
  · calc
      (p + q)/2 < (q + q)/2 := by rel [h]
      _ = q := by ring



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

/- ## two proofs for Problem 2 in Homework Assignment 04 -/

example : forall_sufficiently_large n : ℕ, 2 ^ n ≥ n ^ 2 := by
  dsimp
  use 4
  intro n hn
  induction_from_starting_point n, hn with k hk IH
  · -- base case
    calc 2 ^ 4 = 16      := by ring -- `exact rfl` will also work
             _ = 4 ^ 2   := by ring -- `exact rfl` will also work
             _ ≥ 4 ^ 2   := by exact Nat.le_refl (4 ^ 2)
                            -- obtained by first applying `by exact?`
  · -- inductive step
    calc 2 ^ (k + 1) = 2 * 2 ^ k := by ring
      _ ≥ 2 * k ^ 2              := by rel [IH]
      _ = k ^ 2 + k * k          := by ring
      _ ≥ k ^ 2 + 4 * k          := by rel [hk]
      _ = k ^ 2 + 2 * k + 2 * k  := by ring
      _ ≥ k ^ 2 + 2 * k + 2 * 4  := by rel [hk]
      _ = (k + 1) ^ 2 + 7        := by ring
      _ ≥ (k + 1) ^ 2            := by exact Nat.le_add_right ((k + 1) ^ 2) 7
                                    -- obtained by first applying `by exact?`

example : forall_sufficiently_large n : ℕ, 2 ^ n ≥ n ^ 3 := by
  dsimp
  sorry
