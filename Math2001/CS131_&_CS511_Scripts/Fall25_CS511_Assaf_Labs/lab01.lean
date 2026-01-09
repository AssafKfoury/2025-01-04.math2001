/- 3 Sept 2025 -/
import Library.Basic

-- 'Int' is the name of a module, part of the Lean4 standard
-- library. It is useful to open it when you work with integers
-- and carry out arithmetical operations, as it contains fundamental
-- definitions and operations on integers:
open Int

#check 3
#check 5.0
#check 5.2
#eval 3 + 5.2

example {p q : Prop} (h_p : p) : q → (p ∧ q) := by
  intro h_q
  apply And.intro h_p h_q

lemma lem {p q : Prop} (h_p : p) : q → (p ∧ q) := by
  intro h_q
  apply And.intro h_p h_q

theorem thm {p q : Prop} (h_p : p) : q → (p ∧ q) := by
  intro h_q
  apply And.intro h_p h_q

example {p q : Prop} (h_p : p) : q → (p ∧ q) := by
  intro h_q
  constructor
  apply h_p
  apply h_q

example {p q r : Prop} (h : p → (q → r)) : p ∧ q → r := by
   intro h_pq
   obtain ⟨ h_p , h_q ⟩ := h_pq
   have h_qr : q → r := by apply h h_p
   apply h_qr h_q
