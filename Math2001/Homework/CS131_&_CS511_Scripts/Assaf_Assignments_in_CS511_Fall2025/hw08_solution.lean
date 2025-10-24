/- # CS 511, 23 Oct 2025, hw08_solution.lean -/

import Mathlib.Data.Real.Basic -- needed in order to use tactic `contrapose`

/- This script illustrates how to prove the `cancellation` property for the  myℕural
   numbers, in two ways: with and without tactic `contrapose`. It also illustrates
   `structural induction` on an `inductive definition` of the  myℕural numbers.

   # This script does NOT use the pre-defined  myℕural numbers 0, 1, ..., the
   # pre-defined type ℕ, and the pre-defined namespace  myℕ, from the Lean library.

-/

-- open Classical

/- user-defined inductive type `myℕ` with two constructors, `myZero` and `mySucc` -/
inductive myℕ : Type
   |  myZero : myℕ
   |  mySucc :  myℕ → myℕ
namespace myℕ

axiom  myZero_not_mySucc : ∀ n : myℕ,  myZero ≠ mySucc n
axiom  mySucc_inj_1 : ∀ (n : myℕ) , ∀ (m : myℕ) , (n ≠ m) → (mySucc n ≠  mySucc m)
axiom  mySucc_inj_2 : ∀ (n : myℕ) , ∀ (m : myℕ) , (mySucc n = mySucc m) → (n = m)
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
  | myZero =>
    have h1 : b =  myZero + b := by rfl
    have h2 : c =  myZero + c := by rfl
    rw [h1, h2]
    exact h
  | mySucc a ih =>
    have h1 :  mySucc a + b =  mySucc (a + b) := by rfl
    have h2 :  mySucc a + c =  mySucc (a + c) := by rfl
    rw [h1,h2] at h
    apply ih
    contrapose h           -- note the effect of `contrapose` in the Infoview
    apply mySucc_inj_1
    exact h

/- # WITHOUT TACTIC `contrapose` -/
theorem cancellation_law' (a b c :  myℕ) : a + b = a + c → b = c := by
  intro h
  induction a with
  | myZero =>
    calc
      b =  myZero + b := rfl
      _ =  myZero + c := h
      _ = c           := rfl
  | mySucc a ih =>
    apply ih
    apply mySucc_inj_2           -- you can use instead `myℕ.mySucc.inj`
    calc
      mySucc (a + b) = (mySucc a) + b  := rfl
      _              = (mySucc a) + c  := h
      _              =  mySucc (a + c) := rfl

/- # EVEN SHORTER THAN PRECEDING PROOF, still without `contrapose` -/
theorem cancellation_law'' (a b c :  myℕ) : a + b = a + c → b = c := by
  intro h
  induction a with
  | myZero =>
    exact h
  | mySucc a ih =>
    apply ih
    apply mySucc_inj_2          -- you can use instead `myℕ.mySucc.inj`
    exact h
