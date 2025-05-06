import Mathlib.Data.Set.Basic -- needed for "def A"
import Mathlib.Data.Finset.Basic -- needed for "lemma instA"
--import Mathlib.Data.Set.Finite

def A : Set ℤ := {x : Int | x^2 = 9}
#check A

/- ## 'instance' is used to declare a specific implementation of a
   ## type class for a given type, making it available for implicit
   ## type class resolution -/
instance (n : ℤ) : Decidable (n ∈ A) := by
  suffices Decidable (n^2 = 9) by
    rw [A, Set.mem_setOf_eq] -- rewrite [A, Set.mem_setOf_eq]
    assumption
  apply inferInstance

#check Lean.Expr.rewrite
#check Decidable      -- Decidable (p : Prop) : Type
#check Lean.Meta.assumption
#check inferInstance

#eval List.Forall (· ∈ A) [-3, 3]   -- true

instance (S : Finset ℤ) : Decidable (↑S ⊆ A) := by
  rw [A]                 -- rewrite [A]
  dsimp [Set.subset_def] -- rewrite [Set.subset_def]
  show Decidable (∀ x ∈ S, x ∈ {x | x ^ 2 = 9})
  apply inferInstance

#check Set.subset_def -- ({1,2} ⊆ {1,2,3})

lemma instA : A = ({3, -3} : Finset ℤ) := by
  let S : Finset ℤ := {3, -3}
  change (A = ↑S)
