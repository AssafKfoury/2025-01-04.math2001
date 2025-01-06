import Mathlib.Data.Real.Basic
import Library.Basic

math2001_init

/-! # CS 511 Homework 1 -/

-- (LCS) Exercise 1.2.1.h
example {p q : Prop} (h1 : p) : (p -> q) -> q := by
  intro h2; apply h2 h1

-- (LCS) Exercise 1.2.1.i
example {p q r : Prop} (h1 : (p -> r) ∧ (q -> r)) : p ∧ q -> r := by
  obtain ⟨h1,h2⟩ := h1; intros h3; obtain ⟨h3,h4⟩ := h3; apply h1 h3

-- (LCS) Exercise 1.2.1.j
example {p q r : Prop} (h1 : q -> r) : (p -> q) -> (p -> r) := by
  intros h2 h3; apply h1 (h2 h3)
