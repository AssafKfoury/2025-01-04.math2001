import Mathlib.Data.Set.Basic
import Mathlib.Data.List.Basic
import Mathlib.Data.Set.Finite            -- NEEDED for Finset.card
import Mathlib.Algebra.BigOperators.Basic -- NEEDED FOR Finset.sum
-- import Mathlib.Data.Fintype.Basic      -- NOT CAUSING error
import Mathlib.Data.Finset.Basic         -- NEEDED for Finset.range
-- import Mathlib.Data.Nat.Order            -- CONFLICTS with Math.Data.Set.Basic
-- import Mathlib.Data.List.Lemmas          -- CONFLICTS with Math.Data.Set.Basic
import Library.Basic

import Init.Data.Fin
import Std.Data.List.Basic
import Std.Data.List.Lemmas
import Std.Data.List.Lemmas

math2001_init
namespace Int
set_option trace.Meta.Tactic.simp true -- hilights tactic
                                       -- 'simp' wherever it is used?
open Set

-- Define a custom set type with an element type of Nat
def MySet (α : Type) := Set α

-- Example usage: creating a set of natural numbers
def mySet1 : Set ℕ := {1, 2, 3}

-- Demonstrating set operations: adding an element and union
def mySet2 : Set ℕ := mySet1.insert 4
def mySet3 : Set ℕ := mySet1.union mySet2

-- Printing the sets to the console
#reduce mySet3
#check mySet3
-- #eval mySet2

-- Another example: using list comprehension to create a set
def evenNumbers : Set ℕ := { n | ∃ m, n = 2 * m }

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

-- Printing the set of even numbers
-- #eval evens
#reduce evens
#check evens

-- Using the included set operations from Math.Data.Set:
-- union, intersection, difference
def set1 : Set ℕ := {1, 2, 3}
def set2 : Set ℕ := {3, 4, 5}
--#eval set1.union set2
#reduce set1.union set2
#check set1.union set2
-- #eval set1.intersect set2
-- #reduce set1.intersect set2
-- #eval set1.diff set2
#reduce set1.diff set2
#check set1.diff set2
