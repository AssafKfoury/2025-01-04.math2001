import Mathlib.Tactic.GCongr
import Library.Basic
import Library.Tactic.ModEq

math2001_init

namespace Int

--# Exercise 3

--Exercise 6.2.7.1
def c : ℕ → ℤ
  | 0 => 7
  | n + 1 => 3 * c n - 10

example (n : ℕ) : Odd (c n) := by
  simple_induction n with k IH
  · dsimp [Odd]
    rw [c]
    use 3
    ring
  · dsimp [Odd] at *
    obtain ⟨m,hm⟩ := IH
    rw [c]
    rw [hm]
    use 3 * m - 4
    ring

--Exercise 6.2.7.2
example (n : ℕ) : c n = 2 * 3 ^ n + 5 := by
  simple_induction n with k IH
  · rw [c]
    ring
  · rw [c,IH]
    ring

--Exercise 6.2.7.3
def y : ℕ → ℕ
  | 0 => 2
  | n + 1 => (y n) ^ 2

example (n : ℕ) : y n = 2 ^ (2 ^ n) := by
  simple_induction n with k IH
  · rw [y]
    ring
  · rw [y,IH]
    ring

--# Exercise 4

--Exercise 6.3.6.1
def b : ℕ → ℤ
  | 0 => 0
  | 1 => 1
  | n + 2 => 5 * b (n + 1) - 6 * b n

example (n : ℕ) : b n = 3 ^ n - 2 ^ n := by
  two_step_induction n with k IH1 IH2
  · rw [b]
    numbers
  · rw [b]
    numbers
  · rw [b,IH1,IH2]
    ring

--Exercise 6.3.6.2
def c' : ℕ → ℤ
  | 0 => 3
  | 1 => 2
  | n + 2 => 4 * c' n

example (n : ℕ) : c' n = 2 * 2 ^ n + (-2) ^ n := by
  two_step_induction n with k IH1 IH2
  · rw [c']; numbers
  · rw [c']; numbers
  · rw [c',IH1]; ring

--Exercise 6.3.6.3
def t : ℕ → ℤ
  | 0 => 5
  | 1 => 7
  | n + 2 => 2 * t (n + 1) - t n

example (n : ℕ) : t n = 2 * n + 5 := by
  two_step_induction n with k IH1 IH2
  · rw [t]; numbers
  · rw [t]; numbers
  · rw [t,IH1,IH2]; ring

--# Problem 2

--Exercise 6.3.6.5
def s : ℕ → ℤ
  | 0 => 2
  | 1 => 3
  | n + 2 => 2 * s (n + 1) + 3 * s n

example (m : ℕ) : s m ≡ 2 [ZMOD 5] ∨ s m ≡ 3 [ZMOD 5] := by
  have H : ∀ n : ℕ, 0 ≤ n →
    (s n ≡ 2 [ZMOD 5] ∧ s (n + 1) ≡ 3 [ZMOD 5]) ∨ (s n ≡ 3 [ZMOD 5] ∧ s (n + 1) ≡ 2 [ZMOD 5]) := by
    intros n hn
    induction_from_starting_point n, hn with k hk IH
    · rw [s]; left; constructor
      · apply Int.ModEq.refl
      · rw [s]; apply Int.ModEq.refl
    · obtain ⟨IH1,IH2⟩ | ⟨IH1,IH2⟩ := IH
      · right
        constructor
        · apply IH2
        · rw [Int.ModEq] at *
          rw [s]
          obtain ⟨x,hx⟩ := IH1
          obtain ⟨y,hy⟩ := IH2
          have hx' : s k = 5 * x + 2 := by addarith [hx]
          have hy' : s (k + 1) = 5 * y + 3 := by addarith [hy]
          rw [hx',hy']
          use 2 * y + 3 * x + 2
          ring
      · left
        · constructor
          · apply IH2
          · rw [Int.ModEq] at *
            rw [s]
            obtain ⟨x,hx⟩ := IH1
            obtain ⟨y,hy⟩ := IH2
            have hx' : s k = 5 * x + 3 := by addarith [hx]
            have hy' : s (k + 1) = 5 * y + 2 := by addarith [hy]
            rw [hx',hy']
            use 2 * y + 3 * x + 2
            ring
  have hm : m ≥ 0 := by extra
  obtain ⟨H1,H2⟩ | ⟨H1,H2⟩ := H m hm
  · left; apply H1
  · right; apply H1

--Exercise 6.3.6.7
def r : ℕ → ℤ
  | 0 => 2
  | 1 => 0
  | n + 2 => 2 * r (n + 1) + r n

example : forall_sufficiently_large n : ℕ, r n ≥ 2 ^ n := by
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
