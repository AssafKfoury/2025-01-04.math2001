/- 3 Sept 2025 -/
import Library.Basic

-- 'Int' is the name of a module, part of the Lean4 standard
-- library. It is useful to open it when you work with integers
-- and carry out arithmetical operations, as it contains fundamental
-- definitions and operations on integers:
open Int

#check 3 --

example {p q : Prop} (h_p : p) : q → (p ∧ q) := by
  intro h_q
  constructor
  apply h_p
  apply h_q

theorem lem {p q : Prop} (h : p) : q → (p ∧ q) := by
   intro h_q
   apply And.intro h h_q
