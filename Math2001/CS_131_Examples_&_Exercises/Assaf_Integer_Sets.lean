-- import Mathlib -- it takes a very long time to import!!!
import Mathlib.Data.Set.Basic    -- needed for "def A"
import Mathlib.Data.Finset.Basic -- needed for "lemma instA"
-- import Mathlib.Tactic.Common -- For basic tactics, including decide
-- import Mathlib.Logic.Basic
import Library.Basic  -- needed for math2001_init

math2001_init

open Set

#check decide
#eval decide (1 = 2)
#eval decide (2 = 2)

/- In Macbeth's environment, but not in the Lean4 Playground,
   tactic "decide" is disabled -/
-- example : 1 + 1 = 2 := by decide -- in Macbeth's environment
-- theorem exxx : True := by decide

/- ## WORKING WITH INTEGER SETS in Lean 4 -/

/- ## EXAMPLE 1 in "Working with integer sets in Lean 4":
      https://brandonrozek.com/blog/integer-sets-lean4/  -/

def A : Set ℤ := {x : Int | x^2 = 9}

/- ## 'instance' is used to declare a specific implementation of a
   ## type class for a given type, making it available for implicit
   ## type class resolution -/
instance (n : ℤ) : Decidable (n ∈ A) := by
  suffices Decidable (n^2 = 9) by
    rw [A, Set.mem_setOf_eq] -- 'rewrite [A, Set.mem_setOf_eq]' works also
    exact this               -- 'assumption' works also
  apply inferInstance

#eval List.Forall (· ∈ A) [-3, 3]   -- true

instance (S : Finset ℤ) : Decidable (↑S ⊆ A) := by
  rw [A]                 -- 'rewrite [A]' works also
  dsimp [Set.subset_def] -- 'rewrite [Set.subset_def]' works also
  show Decidable (∀ x ∈ S, x ∈ {x | x ^ 2 = 9})
  apply inferInstance

#help tactic decide
#help tactic exact

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

  have H2 : ↑S ⊆ A := by -- decide
     rw [@Finset.coe_pair]
     rw [@insert_subset_iff]
     constructor
     exact rfl
     exact singleton_subset_iff.mpr rfl


  exact And.intro H1 H2

/- how to use tactic 'suffices':

Given a main goal ctx ⊢ t,
"suffices h : t1 from e" replaces the main goal with
"ctx ⊢ t1",
provided e has type t in the context "ctx, h : t1".

-/

/- ## Below is a different implementation of 'instA' by Assaf -/
lemma instA_Assaf : A = ({3, -3} : Finset ℤ) := by
  let S : Finset ℤ := {3, -3}    -- declaration placed in the context
  let T : Set ℤ := {3, -3}
  rw [Set.Subset.antisymm_iff]
  constructor

  have h1 : A ⊆ T := by
    dsimp [T]
    dsimp [A]
    dsimp [Set.subset_def]
    intro (p : ℤ) ; intro h1_1
    exact eq_or_eq_neg_of_sq_eq_sq p 3 h1_1

  have H1 : A ⊆ ↑S := by
    dsimp [Set.subset_def]
    intro (n : ℤ) ; intro H1_1
    rw [A] at H1_1
    have H1_2 : n^2 = 9 := by
       dsimp [(· ∈ ·)] at H1_1
       exact H1_1

    suffices n = 3 ∨ n = -3 by
      show n ∈ S
      rw [Finset.mem_insert]
      rw [Finset.mem_singleton]
      exact this

    exact eq_or_eq_neg_of_sq_eq_sq n 3 H1_1
  exact H1

  have H2 : ↑S ⊆ A := by decide
  exact H2

example : 1 ∈ {n : ℤ | n ≤ 3} := by
  dsimp
  numbers

#eval Nat.sqrt (3^2)

-- example (hn : n^2 = 9) : n = 3 := by
