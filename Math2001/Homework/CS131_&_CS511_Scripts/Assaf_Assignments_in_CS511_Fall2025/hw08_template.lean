/- # CS 511, 23 Oct 2025, hw08_template.lean -/

import Mathlib.Data.Real.Basic -- needed in order to use tactic `contrapose`

/- This script illustrates how to prove the `cancellation` property for the  myℕural
   numbers, in two ways: with and without tactic `contrapose`. It also illustrates
   `structural induction` on an `inductive definition` of the  myℕural numbers.

   # This script does NOT use the pre-defined natural numbers 0, 1, ..., of the
   # pre-defined type ℕ, and the pre-defined namespace Nat, from the Lean library.
-/

/- user-defined inductive type `myℕ` with two constructors, `myZero` and `mySucc` -/
inductive myℕ : Type
   |  myZero : myℕ
   |  mySucc :  myℕ → myℕ

namespace myℕ

axiom  myZero_not_succ : ∀ (n : myℕ) ,  myZero ≠ mySucc n
axiom  mySucc_inj : ∀ (n : myℕ) , ∀ (m : myℕ) , (n ≠ m) → (mySucc n ≠  mySucc m)
axiom  mySucc_not_zero : ∀ (n : myℕ) , (n ≠ myZero) → ∃ (m : myℕ) , mySucc m = n

/- user-defined inductive definition of `myAdd` -/
def myAdd :  myℕ → myℕ → myℕ
  |  myZero , m   => m
  |  mySucc n , m =>  mySucc (myAdd n m)

-- the `instance` declaration below is needed in order to be able
-- to use `+` in the next theorem. Specifically, we need to register
-- myℕ as a member (or an implementation) of the `Add` type class.
-- This allows the standard addition function for natural numbers,
-- nat.add, to be used via the + operator.
instance : Add myℕ where add := myAdd

/- # WITH TACTIC `contrapose` -/
theorem cancellation_law (a b c : myℕ) : (a + b) = (a + c) → b = c := by
  intro h
  induction a with
  |  myZero =>
    have h1 : b =  myZero + b := by rfl
    have h2 : c =  myZero + c := by rfl
    rw [h1, h2]
    exact h
  |  mySucc a ih =>
    have h1 :  mySucc a + b =  mySucc (a + b) := by rfl
    have h2 :  mySucc a + c =  mySucc (a + c) := by rfl
    rw [h1,h2] at h
    apply ih
    contrapose h           -- note the effect of `contrapose` in the Infoview
    apply  mySucc_inj
    exact h

/- # WITHOUT TACTIC `contrapose` -/
theorem cancellation_law' (a b c :  myℕ) : a + b = a + c → b = c := by
  intro h
  induction a with
  | myZero =>
     sorry
  | mySucc a ih =>
     sorry

/- # EVEN SHORTER THAN PRECEDING PROOF, still without `contrapose` -/
theorem cancellation_law'' (a b c :  myℕ) : a + b = a + c → b = c := by
  intro h
  induction a with
  | myZero =>
    sorry
  | mySucc a ih =>
    sorry
