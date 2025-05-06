import Mathlib.Data.Set.Basic -- needed for "def A"
import Mathlib.Data.Finset.Basic -- needed for "lemma instA"
--import Mathlib.Data.Set.Finite

def A : Set ℤ := {x : Int | x^2 = 9}
#check A

lemma instA : A = ({3, -3} : Finset ℤ) := by sorry

/- ## 'instance' is used to declare a specific implementation of a
   ## type class for a given type, making it available for implicit
   ## type class resolution -/
instance (n : ℤ) : Decidable (n ∈ A) := by
  suffices Decidable (n^2 = 9) by
    rewrite [A, Set.mem_setOf_eq]
    assumption
  apply inferInstance
