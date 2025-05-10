
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Int.Basic

-- Define a finite set of integers
def mySet : Finset ℤ := {1, 2, 3}

-- Convert the set to a list
noncomputable def myList1 : List ℤ := mySet.toList

def myList2 : List ℤ := [1,2,3]

-- #eval myList1  -- myList1 does not have executable code
#eval myList2
