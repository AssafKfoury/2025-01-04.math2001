import Mathlib.Data.Real.Basic -- needed in order to use tactic `contrapose`

/- This script illustrates how to prove the `cancellation` property for the natural
   numbers, in two ways: with and without tactic `contrapose`. It also illustrates
   `structural induction` on an `inductive definition` of the natural numbers.

   # This script does NOT use the pre-defined natural numbers 0, 1, ..., the
   # pre-defined type ℕ, and the pre-defined namespace Nat, from the Lean library.

-/

-- open Classical

/- user-defined inductive type `nat` with two constructors, `zero` and `succ` -/
inductive nat : Type
   | zero : nat
   | succ : nat → nat

namespace nat

axiom zero_not_succ : ∀ n : nat, zero ≠ succ n
axiom succ_inj : ∀ n : nat, ∀ m : nat, n ≠ m → succ n ≠ succ m

/- user-defined inductive definition of `add` -/
def add : nat → nat → nat
  | zero, m   => m
  | succ n, m => succ (add n m)

-- the `instance` declaration below is needed in order to be able
-- to use `+` in the next theorem.
-- Get to use the plus `+` operator
instance : Add nat where add := add

/- # WITH TACTIC `contrapose` -/
theorem cancellation_law (a b c : nat) : (a + b) = (a + c) → b = c := by
  intro h
  induction a with
  | zero =>
    have h1 : b = zero + b := by rfl
    have h2 : c = zero + c := by rfl
    rw [h1, h2]
    exact h
  | succ a ih =>
    have h1 : succ a + b = succ (a + b) := by rfl
    have h2 : succ a + c = succ (a + c) := by rfl
    rw [h1,h2] at h
    apply ih
    contrapose h           -- note the effect of `contrapose` in the Infoview
    apply succ_inj
    exact h

/- # WITHOUT TACTIC `contrapose` -/
theorem cancellation_law' (a b c : nat) : a + b = a + c → b = c := by
  intro h
  induction a with
  | zero =>
    calc
      b = zero + b := rfl
      _ = zero + c := h
      _ = c        := rfl
  | succ a ih =>
    apply ih
    apply nat.succ.inj
    calc
      succ (a + b) = (succ a) + b := rfl
      _            = (succ a) + c := h
      _            = succ (a + c) := rfl

/- # EVEN SHORTER THAN PRECEDING PROOF, still without `contrapose` -/
theorem cancellation_law'' (a b c : nat) : a + b = a + c → b = c := by
  intro h
  induction a with
  | zero =>
    exact h
  | succ a ih =>
    apply ih
    apply nat.succ.inj
    exact h
