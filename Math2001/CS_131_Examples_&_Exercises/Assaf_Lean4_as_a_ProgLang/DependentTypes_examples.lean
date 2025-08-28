/-
2025-08-27
Dependent types are types that contain non-type expressions.
A common source of dependent types is a named argument to a function.
-/

/-
Warm up after several months of not using Lean 4:
-/
#check [3 , 5 , 8]
#check [3 , 5.0 , 8]
#check (3 , 5 , 8)
#check (3 , 5.0 , 8)
#check (3 , 5 , 8).fst
#eval  (3 , 5 , 8).snd.snd

/-
EXAMPLE 1: The type "if b then Nat else String"
contains the argument "b" as a non-type expression.
-/

def natOrStringThree (b : Bool) : if b then Nat else String :=
  match b with
  | true => (3 : Nat)
  | false => "three"

#check natOrStringThree
#check natOrStringThree true
#eval natOrStringThree true
#check natOrStringThree false
#eval natOrStringThree false

/-
EXAMPLE 2: No dependent types in this example. Just a WARM-UP and
  a reminder of how an inductive type is defined and how to use it.
-/

inductive MyNat where
  | MyZero : MyNat
  | MySucc : MyNat → MyNat

open MyNat
#check MyZero
#check MySucc

def My1 : MyNat := MySucc MyZero
def My2 : MyNat := MySucc (MySucc MyZero)
#check My1
#check My2

def MyAdd (m n : MyNat) : MyNat :=
  match n with
  | MyZero   => m
  | MySucc k => MySucc (MyAdd m k)
#check MyAdd My1 My2
-- #eval MyAdd My1 My2

/-
EXAMPLE 3: This declares an inductive type Vec, where
    "(α : Type)" is a type parameter, the type of elts in the vector.
    "Nat → Type" signifies that "Vec α" is a function that takes a
           Nat (representing the length of the vector) and returns
           a Type. This makes Vec a dependent type, as the resulting
           type depends on the Nat parameter.
-/

inductive Vec (α : Type) : Nat → Type where
  | nil : Vec α 0
  | cons : α → {n : Nat} → Vec α n → Vec α (n + 1)

#check Vec Nat 0  -- Type: Vec Nat 0
#check Vec Nat 3  -- Type: Vec Nat 3

open Vec

#check nil
#check cons 3 nil

#check cons false nil
#check cons true (cons false nil)
#check cons false (cons true (cons false nil))
