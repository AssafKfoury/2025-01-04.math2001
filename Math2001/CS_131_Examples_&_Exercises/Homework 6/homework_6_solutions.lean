import Mathlib.Data.Real.Basic
import Library.Basic
import Library.Theory.ModEq.Defs
import Library.Tactic.ModEq
import Library.Theory.ParityModular
import AutograderLib

math2001_init

--# Exercise 3.4.5.6

@[autograded 3]
theorem exercise_3a (n : ℤ) : 5 * n ^ 2 + 3 * n + 7 ≡ 1 [ZMOD 2] := by
  mod_cases n % 2
  · have nsqu : n ^ 2 ≡ 0 [ZMOD 2] := by
      calc
        n ^ 2 ≡ 0 ^ 2 [ZMOD 2] := by apply Int.ModEq.pow; apply H
        _ ≡ 0 [ZMOD 2] := by use 0; ring
    calc
      5 * n ^ 2 + 3 * n + 7 ≡ 5 * 0 + 3 * 0 + 7 [ZMOD 2] := by rel [H,nsqu]
      _ ≡ 1 [ZMOD 2] := by use 3; ring
  · have nsqu : n ^ 2 ≡ 1 [ZMOD 2] := by
      calc
        n ^ 2 ≡ 1 ^ 2 [ZMOD 2] := by apply Int.ModEq.pow; apply H
        _ ≡ 1 [ZMOD 2] := by use 0; ring
    calc
      5 * n ^ 2 + 3 * n + 7 ≡ 5 * 1 + 3 * 1 + 7 [ZMOD 2] := by rel [H,nsqu]
      _ ≡ 1 [ZMOD 2] := by use 7; ring

--# Exercise 3.4.5.7

@[autograded 3]
theorem exercise_3b {x : ℤ} : x ^ 5 ≡ x [ZMOD 5] := by
  mod_cases hx : x % 5
  calc
    x ^ 5 ≡ 0 ^ 5 [ZMOD 5] := by rel [hx]
    _ ≡ 0 [ZMOD 5] := by numbers
  apply Int.ModEq.symm; exact hx
  calc
    x ^ 5 ≡ 1 ^ 5 [ZMOD 5] := by rel [hx]
    _ ≡ 1 [ZMOD 5] := by numbers
  apply Int.ModEq.symm; exact hx
  calc
    x ^ 5 ≡ 2 ^ 5 [ZMOD 5] := by rel [hx]
    _ ≡ 2 + 5 * 6 [ZMOD 5] := by numbers
    _ ≡ 2 [ZMOD 5] := by extra
  apply Int.ModEq.symm; exact hx
  calc
    x ^ 5 ≡ 3 ^ 5 [ZMOD 5] := by rel [hx]
    _ ≡ 3 + 5 * 48 [ZMOD 5] := by numbers
    _ ≡ 3 [ZMOD 5] := by extra
  apply Int.ModEq.symm; exact hx
  calc
    x ^ 5 ≡ 4 ^ 5 [ZMOD 5] := by rel [hx]
    _ ≡ 4 + 5 * 204 [ZMOD 5] := by numbers
    _ ≡ 4 [ZMOD 5] := by extra
  apply Int.ModEq.symm; exact hx

--# Exercise 4.4.6.2

@[autograded 3]
theorem exercise_4a (n : ℤ) (hn : n ^ 2 ≡ 4 [ZMOD 5]) : n ≡ 2 [ZMOD 5] ∨ n ≡ 3 [ZMOD 5] := by
  mod_cases h : n % 5
  · apply Int.ModEq.symm at hn
    have contra :=
    calc
      4 ≡ n^2 [ZMOD 5] := hn
      _ = n*n := by ring
      _ ≡ 0*n [ZMOD 5] := by rel [h]
      _ = 0 := by ring
      _ ≡ 0 [ZMOD 5] := by extra
    numbers at contra
  · apply Int.ModEq.symm at hn
    have contra :=
    calc
      4 ≡ n^2 [ZMOD 5] := hn
      _ = n*n := by ring
      _ ≡ 1*n [ZMOD 5] := by rel [h]
      _ ≡ 1*1 [ZMOD 5] := by rel [h]
      _ = 1 := by ring
    numbers at contra
  · left; exact h
  · right; exact h
  · apply Int.ModEq.symm at hn
    have contra :=
    calc
      4 ≡ n^2 [ZMOD 5] := hn
      _ = n*n := by ring
      _ ≡ 4*n [ZMOD 5] := by rel [h]
      _ ≡ 4*4 [ZMOD 5] := by rel [h]
      _ = 1 + 5*3 := by ring
      _ ≡ 1 [ZMOD 5] := by extra
    numbers at contra

--# Exercise 4.4.6.3

@[autograded 3]
theorem exercise_4b : Prime 7 := by
  apply prime_test
  · numbers
  · intros m h1 h2
    apply Nat.not_dvd_of_exists_lt_and_lt
    interval_cases m
    · use 3; constructor <;> numbers
    · use 2; constructor <;> numbers
    · use 1; constructor <;> numbers
    · use 1; constructor <;> numbers
    · use 1; constructor <;> numbers

--# Example 4.5.4

@[autograded 2]
theorem problem_2a : ¬ (∃ n : ℕ, n ^ 2 = 2) := by
  intros h
  obtain ⟨n,hn⟩ := h
  obtain h1 | h2 := le_or_succ_le n 1
  · have h :=
    calc
      n^2 = n*n := by ring
      _ ≤ 1*n := by rel [h1]
      _ ≤ 1*1 := by rel [h1]
      _ = 1 := by ring
    rw [hn] at h
    numbers at h
  · have h :=
    calc
      n^2 = n*n := by ring
      _ ≥ 2*n := by rel [h2]
      _ ≥ 2*2 := by rel [h2]
      _ = 4 := by ring
    rw [hn] at h
    numbers at h

--# Example 4.5.5

@[autograded 2]
theorem problem_2b (n : ℤ) : Int.Odd n ↔ ¬ Int.Even n := by
  constructor
  · intros hOdd hEven
    rw [Int.odd_iff_modEq] at hOdd
    rw [Int.even_iff_modEq] at hEven
    have h :=
    calc
      0 ≡ n [ZMOD 2] := by rel [hEven]
      _ ≡ 1 [ZMOD 2] := by rel [hOdd]
    numbers at h
  · intro hNotEven
    obtain h1 | h2 := Int.even_or_odd n
    · contradiction
    · apply h2

--# Example 4.5.6

@[autograded 2]
theorem problem_2c (n : ℤ) : ¬(n ^ 2 ≡ 2 [ZMOD 3]) := by
  intro h
  mod_cases hn : n % 3
  · have h :=
    calc (0:ℤ) = 0 ^ 2 := by numbers
      _ ≡ n ^ 2 [ZMOD 3] := by rel [hn]
      _ ≡ 2 [ZMOD 3] := by rel [h]
    numbers at h -- contradiction!
  · have h :=
    calc
      (1 : ℤ) = 1 ^ 2 := by numbers
      _ ≡ n ^ 2 [ZMOD 3] := by rel [hn]
      _ ≡ 2 [ZMOD 3] := by rel [h]
    numbers at h
  · have h' :=
    calc
      (1 : ℤ) ≡ 1 + 3*1 [ZMOD 3] := by extra
      _ = 2^2 := by ring
      _ ≡ n^2 [ZMOD 3] := by rel [hn]
      _ ≡ 2 [ZMOD 3] := h
    numbers at h'
