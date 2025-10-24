/- # CS 511, 23 Oct 2025, hw08_solution.lean -/

import Mathlib.Data.Real.Basic -- needed in order to use tactic `contrapose`

import Library.Basic   -- needed for math2001_init
math2001_init          -- needed to access Macbeth's tactics:
                       -- `addarith`, `cancel`, `extra`, `numbers`

/- # Exercise 3 in Homework 08 -/
/- Consult page 25 in Slides 18 for hints -/

example (h : ∃x : Type, ∀y : Type, (x = y)) : (∀x : Type, ∀y : Type, (x = y)) := by
  intros x y
  obtain ⟨c,hc⟩ := h
  have hx := hc x
  have hy := hc y
  rw [hx] at hy
  exact hy

example : (∃x : Type, ∀y : Type, (x = y)) → (∀v : Type, ∀w : Type, (v = w)) := by
  intros h v w
  obtain ⟨x,hx⟩ := h
  have hv := hx v
  have hw := hx w
  rw [hv] at hw
  exact hw

/- # Exercise 4 in Homework 08 -/

/- Exercise 5.2.7.2 in Macbeth's book [MOP]  -/
example (P Q : Prop) : (¬P → ¬Q) ↔ (Q → P) := by
  constructor
  · intros nPnQ q
    by_cases p : P
    · apply p
    · have contra := nPnQ p
      contradiction
  · intros qp np
    by_cases q : Q
    · have contra := qp q
      contradiction
    · apply q

/- Exercise 5.3.6.9 in Macbeth's book [MOP] -/

example : ¬ (∃ t : ℝ, t ≤ 4 ∧ t ≥ 5) := by
  push_neg
  intros t
  by_cases ht : t ≥ 5
  · left
    calc
      t ≥ 5 := by rel [ht]
      _ > 4 := by numbers
  · push_neg at ht
    right
    apply ht


/- # Problem 2 in Homework 08 -/

/- The rest of this script illustrates how to prove the `cancellation` property for
   the natural numbers, in two ways: with and without tactic `contrapose`. It also
   illustrates `structural induction` on an `inductive definition` of the natural numbers.

   # This script does NOT use the pre-defined  natural numbers 0, 1, ..., the
   # pre-defined type ℕ, and the pre-defined namespace Nat, from the Lean_4 library.

-/

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
