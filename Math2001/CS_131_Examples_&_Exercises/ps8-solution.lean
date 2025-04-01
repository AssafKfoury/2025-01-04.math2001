import Mathlib.Tactic.GCongr
import Library.Basic
import Library.Tactic.ModEq
import AutograderLib

open Nat
namespace Nat

def r : ℕ → ℤ
  | 0 => 2
  | 1 => 0
  | n + 2 => 2 * r (n + 1) + r n

#eval r 7 - 2 ^ 7 -- `12`
#eval r 7 -- `140`
#eval r 8 -- `338`
#eval 2^7 -- `128`
#eval 2^8 -- `256`

/-
Suggested steps:
  use 7
  intros n hn
  two_step_induction_from_starting_point n, hn with k hk IH1 IH2
-/

@[autogradedProof 15]
theorem problem1 : forall_sufficiently_large n : ℕ, r n ≥ 2 ^ n := by
  use 7
  intros n hn
  two_step_induction_from_starting_point n, hn with k hk IH1 IH2
  · calc
      r 7 = 140 := by rfl
      _ ≥ 2 ^ 7 := by numbers
  · calc
      r 8 = 338 := by rfl
      _ ≥ 2 ^ 8 := by numbers
  · rw [r]
    calc
      2 * r (k + 1) + r k ≥ 2 * 2 ^ (k + 1) + 2 ^ k := by rel [IH1,IH2]
      _ = 2 ^ (k + 2) + 2 ^ k := by ring
      _ ≥ 2 ^ (k + 1 + 1) := by extra

/-
Read MacBeth's book section 6.4 to see how strong induction is performed in Lean 4.
Suggested steps:
  have hPar := even_or_odd n
  obtain hEven | hOdd := hPar
-/

@[autogradedProof 15]
theorem problem2 (n : ℕ) (hn : 0 < n) : ∃ a x, Odd x ∧ n = 2 ^ a * x := by
  have hPar := even_or_odd n
  obtain hEven | hOdd := hPar
  · dsimp [Even] at hEven
    obtain ⟨k,hk⟩ := hEven
    rw [hk] at hn
    cancel 2 at hn
    have IH := problem2 k hn
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
