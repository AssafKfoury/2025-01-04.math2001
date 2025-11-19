/- # CS 511, 14 November 2025, hw11_solution.lean -/
import Mathlib.Data.Real.Basic
import Library.Basic
--import Library.Tactic.Exhaust --
    -- The `exhaust` tactic is typically used to solve goals that involve
    -- finite-case analysis, primarily in the context of sets or other
    -- inductive types with a small number of elements. It is generally
    -- used after the tactics `dsimp` or `intro` in a by block.
math2001_init           --  needed to access Macbeth's tactics:
                        -- `addarith`, `cancel`, `extra`, `numbers`

open Function
namespace Int

/- # Exercise 3 in Homework 11-/

--Exercise 8.1.13.2
--# Prove one-------------------------------------------------------

example : Injective (fun (x : ℝ) ↦ 3) := by
  sorry

example : ¬ Injective (fun (x : ℝ) ↦ 3) := by
  dsimp [Injective]
  push_neg
  use 1, 2
  constructor
  · numbers
  · numbers

--Exercise 8.1.13.3
--# Prove one-------------------------------------------------------

example : Injective (fun (x : ℚ) ↦ 3 * x - 1) := by
  dsimp [Injective]
  intros x1 x2 hx
  have mid : 3 * x1 = 3 * x2 := by addarith [hx]
  cancel 3 at mid

example : ¬ Injective (fun (x : ℚ) ↦ 3 * x - 1) := by
  sorry

--Exercise 8.1.13.5
--# Prove one-------------------------------------------------------

example : Surjective (fun (x : ℝ) ↦ 2 * x) := by
  dsimp [Surjective]
  intros b
  use b/2
  ring

example : ¬ Surjective (fun (x : ℝ) ↦ 2 * x) := by
  sorry

--# -----------------------------------------------------------------

/- # Exercise 4 in Homework 11-/

inductive Musketeer
  | athos
  | porthos
  | aramis
  deriving DecidableEq

open Musketeer

inductive White
  | meg
  | jack
  deriving DecidableEq

open White

def h : Musketeer → White
  | athos => jack
  | porthos => meg
  | aramis => jack

--Exercise 8.1.13.8
--# Prove one-------------------------------------------------------

example : Injective h := by
  sorry

example : ¬ Injective h := by
  dsimp [Injective]
  push_neg
  use athos, aramis
  constructor
  · exact rfl                              -- exhaust
  · exact (bne_iff_ne athos aramis).mp rfl -- exhaust

--Exercise 8.1.13.9
--# Prove one-------------------------------------------------------

example : Surjective h := by
  dsimp [Surjective]
  intros b
  cases b
  · use porthos; exact rfl -- exhaust
  · use athos; exact rfl   -- exhaust

example : ¬ Surjective h := by
  sorry

--# ----------------------------------------------------------------

def l : White → Musketeer
  | meg => aramis
  | jack => porthos

--Exercise 8.1.13.11
--# Prove one-------------------------------------------------------

example : Surjective l := by
  sorry

example : ¬ Surjective l := by
  dsimp [Surjective]
  push_neg
  use athos
  intros a
  cases a
  · exhaust
  · exhaust
  -- the preceding 3 lines can be replaced by the single line `cases a <;> exhaust`

--# ----------------------------------------------------------------

/- # Problem 2 in Homework 11 -/

--Exercise 8.1.13.13
--# Prove one-------------------------------------------------------

example : ∀ (f : ℚ → ℚ), Injective f → Injective (fun x ↦ f x + 1) := by
  intros f hf
  dsimp [Injective] at *
  intros x1 x2 hx
  have mid : f x1 = f x2 := by
    calc
      f x1 = f x1 + 1 - 1 := by ring
      _ = f x2 + 1 - 1 := by rw [hx]
      _ = f x2 := by ring
  exact hf mid

example : ¬ ∀ (f : ℚ → ℚ), Injective f → Injective (fun x ↦ f x + 1) := by
  sorry

--Exercise 8.1.13.14
--# Prove one-------------------------------------------------------

example : ∀ (f : ℚ → ℚ), Injective f → Injective (fun x ↦ f x + x) := by
  sorry

example : ¬ ∀ (f : ℚ → ℚ), Injective f → Injective (fun x ↦ f x + x) := by
  push_neg
  use fun x ↦ -x
  constructor
  · dsimp [Injective]
    intros x1 x2 hx
    addarith [hx]
  · dsimp [Injective]
    push_neg
    use 1, 2
    constructor
    · numbers
    · numbers

--Exercise 8.1.13.16
--# Prove one-------------------------------------------------------

example : ∀ c : ℝ, Surjective (fun x ↦ c * x) := by
  sorry

example : ¬ ∀ c : ℝ, Surjective (fun x ↦ c * x) := by
  push_neg
  use 0
  dsimp [Surjective]
  push_neg
  use 1
  intro a
  rw [zero_mul]
  numbers
