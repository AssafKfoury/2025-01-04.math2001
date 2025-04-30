import Mathlib.Data.Real.Basic
import Library.Basic
-- import Mathlib.Tactic.Qify
-- import Mathlib.Tactic.Zify
import Library.Tactic.ModEq
-- import Mathlib.Tactic
-- import AutograderLib

-- import Init.Data.Nat.Defs
import Init.Data.Fin
import Std.Data.List.Basic
import Std.Data.List.Lemmas
import Mathlib.Data.Finset.Basic -- needed for Finset.range
-- import Mathlib.Data.Nat.Order
import Mathlib.Data.Set.Basic
import Mathlib.Data.List.Basic
-- import Mathlib.Data.List.Lemmas
import Std.Data.List.Lemmas

import Mathlib.Data.Set.Finite -- needed for Finset.card
--import Mathlib.Data.Finset.Basic -- /- ## DOES NOT CAUSE ERROR -/
import Mathlib.Algebra.BigOperators.Basic -- NEEDED FOR Finset.sum

math2001_init
namespace Int
set_option trace.Meta.Tactic.simp true -- hilights tactic
                                       -- 'simp' wherever it is used?

/- ## NONE OF THE FOLLOWING SEEMS NEEDED, THOUGH THEY DON'T CAUSE ERRORS -/
--open Finset
--open BigOperators
--open Function
open Set

/- ## Define an infinite set -/
   def myInfSet : Set ℕ := { n : ℕ | 0 < n }
/- ## Define a finite set -/
   def mySet : Finset ℕ := {1, 2, 3, 4}
/- ## Define a function the square function -/
   def myFunction (n : ℕ) : ℕ := n * n
/- ## Calculate sum of the squares using Finset.sum -/
   def sumOfSquares : ℕ := Finset.sum mySet myFunction
/- ## Print the result -/
#eval sumOfSquares -- Output: 30

#check Finset.range
#eval Finset.card mySet
#eval 3 ∈ mySet
#reduce 3 ∈ myInfSet -- #eval 3 ∈ myInfSet -- CAUSES ERROR!!!
#eval Finset.sum  ({1, 2, 3, 4}) (fun x => x)
#eval Finset.sum  ({1, 2, 3, 4}) (fun x => x * x)

/- ## Calculate sum of entries in finite set S of nats using Finset.sum -/
   def sumOfAll (S : Finset ℕ) : ℕ := Finset.sum S (fun (x : ℕ) => x)
#eval sumOfAll {1,2,3,4}

/- ## boundedFinset creates finite set of numbers
   ## from a (inclusive) to b (inclusive) -/
   def boundedFinset (a b : ℕ) : Finset ℕ :=
      (Finset.range (b + 1)).filter (λ (x : ℕ) => x ≥ a)

#check 3 ∈ (Finset.range 5)
#eval 5 ∈ (Finset.range 5)
#eval 7 ∈ (boundedFinset (2^3) (2*15))
#eval Finset.card (boundedFinset (2^3) (20*15))
#eval Finset.card (boundedFinset (2^3) (2*15))
#eval 7 ∈ (boundedFinset (2^3) (2*15))
#eval 2^3
#check fun (x : ℤ) => x + 1
#eval Finset.sum {1, 2, 3, 4} (fun (x : ℤ) => x)

/- ## Other useful sets of natural numbers -/
   def pairs (X Y : Set ℕ) : Set (ℕ × ℕ) := { (x,y) | (x ∈ X) (y ∈ Y) }
   def evens : Set ℕ := { x | ∃ (k : ℕ), x = 2 * k }
   def odds  : Set ℕ := { x | ∃ (k : ℕ), x = 2 * k + 1 }
   def EvensOdds := pairs evens odds

/- ## evenN and oddN test whether a natural number is even or odd -/
    def evenN (n : ℕ) : Bool := (2 ∣ n)
    def oddN (n : ℕ) : Bool := ¬ (2 ∣ n)
#eval (oddN 3)
#eval (evenN 3) ∧ (evenN 4)
/- ## cond is the conditional if-then-else -/
    def cond : Bool → ℕ → ℕ → ℕ
      | true, x, y => x
      | false, x, y => y
/- ## first_2_in_3 chooses first 2 in 3 numbers whose sum is even -/
    def first_2_in_3 (x y z : ℕ) : ℕ :=
      cond (((evenN x) ∧ (evenN y)) ∨ ((oddN x) ∧ (oddN y))) (x + y)
        (cond (((evenN x) ∧ (evenN z)) ∨ ((oddN x) ∧ (oddN z))) (x + z)
          (cond (((evenN y) ∧ (evenN z)) ∨ ((oddN y) ∧ (oddN z))) (y + z) (y + z)
          ))
#eval first_2_in_3 5 6 9
/- ## divisible_by_2_pow_n tests whether number m is divisible by 2^n -/
    def divisible_by_2_pow_n (m n :ℕ) : Bool := (m ∣ 2^n)
#eval divisible_by_2_pow_n 16 (2^3)
#eval divisible_by_2_pow_n 18 (2^3)
/- ## QntRdr_by_2_pow_n computes quotient and remainder of div by 2^n -/
   def QntRdr_by_2_pow_n (m n : ℕ) : ℕ × ℕ := ( Int.toNat (Int.div m (2^n)) , m % (2^n) )
#eval (QntRdr_by_2_pow_n 14 3)
#eval (2^3)*(QntRdr_by_2_pow_n 14 3).1 + (QntRdr_by_2_pow_n 14 3).2

/-
theorem foo1 (S : Finset ℕ) :
    ∀ (T : Finset ℕ), (T ⊆ S) → (sumOfAll T) ≤ (sumOfAll S) := by
    intro h ; intro hS ;
    -- dsimp [Set.subset_def] at
-/

/-
def random_set_of_k_distinct_nats (k n : ℕ) : IO (Finset ℕ) := do
  if k > n then
    return {}
  else
    let mut result : Finset Nat := {}
    let mut i : Nat := 0
    while i < k do
      let rand_num := StdGen.next -- IO.randNat (n + 1)
      let new_num : Nat ← rand_num
      if  new_num ∈ result then -- (result.contains new_num) then
          continue
      else
          result := insert new_num result -- result.insert new_num
          i := i + 1
    return result

-/
