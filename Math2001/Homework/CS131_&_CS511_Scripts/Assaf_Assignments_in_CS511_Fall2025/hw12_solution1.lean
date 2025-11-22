/- # 21 November 2025, hw12_solution1.lean -/
import Mathlib.Data.Real.Basic
import Library.Basic
-- import Library.Tactic.ModEq
import Library.Theory.InjectiveSurjective

math2001_init

open Set Function Nat

/-# Exercise 3 in HW 12 -/

-- Exercise 6.4.3.1 in [MOP]

theorem extract_pow_two (n : ℕ) (hn : 0 < n) :
            ∃ a x, Nat.Odd x ∧ n = 2 ^ a * x := by
  have hPar := even_or_odd n
  obtain hEven | hOdd := hPar
  · dsimp [Nat.Even] at hEven
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

-- set_option pp.funBinderTypes true

/-# Exercise 4 in HW 12 -/

-- Exercise 8.3.10.2 in [MOP]

def u (x : ℝ) : ℝ := 5 * x + 1

noncomputable def v (x : ℝ) : ℝ := (x - 1) / 5

example : Inverse u v := by
  dsimp [Inverse]
  constructor
  · ext x
    dsimp [u,v]
    ring
  · ext x
    dsimp [u,v]
    ring

-- Exercise 8.3.10.3 in [MOP]

example {f : X → Y} (hf : Injective f) {g : Y → Z} (hg : Injective g) :
    Injective (g ∘ f) := by
  dsimp [Injective] at *
  intros a1 a2 ha
  exact hf (hg ha)

-- Exercise 8.3.10.4 in [MOP]

example {f : X → Y} (hf : Surjective f) {g : Y → Z} (hg : Surjective g) :
    Surjective (g ∘ f) := by
  dsimp [Surjective] at *
  intros z
  have ⟨y,hz⟩ := hg z
  have ⟨x,hy⟩ := hf y
  use x
  rw [← hy] at hz
  exact hz
