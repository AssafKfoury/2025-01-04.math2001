/- # CS 511, 23 Oct 2025, hw08_template.lean -/

import Mathlib.Data.Real.Basic -- needed in order to use tactic `contrapose`

/- This script illustrates how to prove the `cancellation` property for the natural
   numbers, in two ways: with and without tactic `contrapose`. It also illustrates
   `structural induction` on an `inductive definition` of the natural numbers.

   # This script does NOT use the pre-defined natural numbers 0, 1, ..., the
   # pre-defined type ℕ, and the pre-defined namespace Nat, from the Lean library.

-/

/-
Key Differences Between `inductive` And `class` Declarations:
# Purpose:
  `inductive` defines data structures; `class` defines interfaces for type classes.
# Constructors:
  `inductive` can have multiple constructors; `class` (as a `structure`) effectively
   has one constructor, but its fields define the "methods" of the class.
# Inference:
  `inductive` types do not inherently support type class inference; `class`
  declarations are designed for and rely heavily on type class inference.
# Usage:
  `inductive` types are used to represent data; `class` types are used to
  define generic operations and abstractions.
-/

/- we can define a `type class` as follows: -/
class MyClass (α : Type) where
  myMethod : α → α → α
  myValue : α
/- making type ℕ an anonymous implementation of `MyClass` using `instance`: -/
instance : MyClass ℕ where
  myMethod x y := x + y
  myValue := 0
/- making type ℝ an implementation of `MyClass` with a named definition: -/
instance instMyClassℝ : MyClass ℝ where
  myMethod x y := x * y
  myValue := 0
/- using ℕ as an implementation of `MyClass`: -/
#eval MyClass.myMethod (10 : ℕ) (5 : ℕ)  -- Evaluates to 15
#eval MyClass.myValue (α := ℕ)           -- Evaluates to 0
/- using ℝ as an implementation of `MyClass`: -/
#eval instMyClassℝ.myMethod (10 : ℝ) (5 : ℝ)
#eval instMyClassℝ.myValue (α := ℝ)
