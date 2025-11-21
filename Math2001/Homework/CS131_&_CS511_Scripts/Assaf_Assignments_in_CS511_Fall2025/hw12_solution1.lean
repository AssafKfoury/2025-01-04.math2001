/- # 21 November 2025, hw12_solution1.lean -/

import Library.Basic
import Library.Tactic.ModEq
import Library.Tactic.Exhaust

math2001_init

open Set Function Nat

/-# Exercise 3 in HW 12 -/

--Exercise 6.4.3.1

theorem extract_pow_two (n : ℕ) (hn : 0 < n) : ∃ a x, Odd x ∧ n = 2 ^ a * x := by
  have hPar := even_or_odd n
  obtain hEven | hOdd := hPar
  · dsimp [Even] at hEven
    obtain ⟨k,hk⟩ := hEven
    rw [hk] at hn
    cancel 2 at hn
    have IH := extract_pow_two k hn
    obtain ⟨a,x,IH⟩ := IH
    obtain ⟨IH1,IH2⟩ := IH
    use a+1,x
    constructor
    · apply IH1
    · rw [hk]
      rw [IH2]
      ring
  · use 0, n
    constructor
    · apply hOdd
    · ring


/- For the template

import Library.Basic
import Library.Tactic.ModEq
import Library.Tactic.Exhaust

math2001_init

open Set Function Nat

/-# Exercise 4-/

--Exercise 6.4.3.1

theorem extract_pow_two (n : ℕ) (hn : 0 < n) : ∃ a x, Odd x ∧ n = 2 ^ a * x := by
  sorry

-/
