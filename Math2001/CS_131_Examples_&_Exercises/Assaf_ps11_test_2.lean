import Mathlib.Data.Set.Basic -- needed for "def A"
import Mathlib.Data.Finset.Basic -- needed for "lemma instA"
--import Mathlib.Data.Set.Finite

/- ## EXAMPLE 1 in "Working with integer sets in Lean 4":
      https://brandonrozek.com/blog/integer-sets-lean4/  -/

def A : Set ℤ := {x : Int | x^2 = 9}

#check A

/- ## 'instance' is used to declare a specific implementation of a
   ## type class for a given type, making it available for implicit
   ## type class resolution -/
instance (n : ℤ) : Decidable (n ∈ A) := by
  suffices Decidable (n^2 = 9) by
    rw [A, Set.mem_setOf_eq] -- 'rewrite [A, Set.mem_setOf_eq]' works also
    exact this -- 'assumption' works also
  apply inferInstance

#check Lean.Expr.rewrite
#check Decidable      -- Decidable (p : Prop) : Type
#check Lean.Meta.assumption
#check inferInstance

#eval List.Forall (· ∈ A) [-3, 3]   -- true

instance (S : Finset ℤ) : Decidable (↑S ⊆ A) := by
  rw [A]                 -- 'rewrite [A]' works also
  dsimp [Set.subset_def] -- 'rewrite [Set.subset_def]' works also
  show Decidable (∀ x ∈ S, x ∈ {x | x ^ 2 = 9})
  apply inferInstance

lemma instA : A = ({3, -3} : Finset ℤ) := by
  let S : Finset ℤ := {3, -3}
  change (A = ↑S)
  suffices A ⊆ ↑S ∧ ↑S ⊆ A by
    rewrite [Set.Subset.antisymm_iff]
    assumption

  have H1 : A ⊆ ↑S := by
    intro (n : ℤ)
    -- Goal is now (n ∈ A → n ∈ {3, -3})
    intro (H1_1: n ∈ A)
    have H1_1 : n^2 = 9 := by
      rewrite [A, Set.mem_setOf_eq] at H1_1
      assumption

    suffices n = 3 ∨ n = -3 by
      show n ∈ S
      rewrite [Finset.mem_insert, Finset.mem_singleton]
      assumption

    exact eq_or_eq_neg_of_sq_eq_sq n 3 H1_1

  have H2 : ↑S ⊆ A := by decide

  exact And.intro H1 H2

lemma instA_Assaf : A = ({3, -3} : Finset ℤ) := by
  let S : Finset ℤ := {3, -3}    -- declaration placed in the context
  change (A = ↑S)
  rw [Set.Subset.antisymm_iff]
  constructor

  have H1 : A ⊆ ↑S := by
    dsimp [Set.subset_def] -- added by Assaf
    intro (n : ℤ)
    -- Goal is now (n ∈ A → n ∈ {3, -3})
    intro H1_1             -- instead of 'intro (H1_1: n ∈ A)'
    have H1_1 : n^2 = 9 := by
      rw [A, Set.mem_setOf_eq] at H1_1
      exact H1_1

    suffices n = 3 ∨ n = -3 by
      show n ∈ S
      rw [Finset.mem_insert, Finset.mem_singleton]
      exact this

    exact eq_or_eq_neg_of_sq_eq_sq n 3 H1_1
  exact H1

  have H2 : ↑S ⊆ A := by decide
  exact H2
