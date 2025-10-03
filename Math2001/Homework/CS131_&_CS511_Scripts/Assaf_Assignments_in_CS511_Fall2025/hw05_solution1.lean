/- # CS 511, 3 Oct 2025, hw05_solution1.lean -/
/- Most of this script is copied from Macbeth's Lean4 script for
   Section 3.3, after filling in every occurrence of `sorry` -/

import Library.Basic
import Library.Theory.ModEq.Defs

attribute [-instance] Int.instDivInt_1 Int.instDivInt Nat.instDivNat

example : -5 ≡ 1 [ZMOD 3] := by
  use -2
  numbers

theorem Int.ModEq.add {n a b c d : ℤ} (h1 : a ≡ b [ZMOD n]) (h2 : c ≡ d [ZMOD n]) :
    a + c ≡ b + d [ZMOD n] := by
  dsimp [Int.ModEq] at *
  obtain ⟨x, hx⟩ := h1
  obtain ⟨y, hy⟩ := h2
  use x + y
  calc
    a + c - (b + d) = a - b + (c - d) := by ring
    _ = n * x + n * y := by rw [hx, hy]
    _ = n * (x + y) := by ring

theorem Int.ModEq.sub {n a b c d : ℤ} (h1 : a ≡ b [ZMOD n]) (h2 : c ≡ d [ZMOD n]) :
    a - c ≡ b - d [ZMOD n] := by
  obtain ⟨x, hx⟩ := h1
  obtain ⟨y, hy⟩ := h2
  use x - y
  calc
    a - c - (b - d) = a - b - (c - d) := by ring
    _ = n * x - n * y := by rw [hx, hy]
    _ = n * (x - y) := by ring

theorem Int.ModEq.neg {n a b : ℤ} (h1 : a ≡ b [ZMOD n]) : -a ≡ -b [ZMOD n] := by
  obtain ⟨x, hx⟩ := h1
  use -x
  calc
    -a - -b = -(a - b) := by ring
    _ = -(n * x) := by rw [hx]
    _ = n * -x := by ring

theorem Int.ModEq.mul {n a b c d : ℤ} (h1 : a ≡ b [ZMOD n]) (h2 : c ≡ d [ZMOD n]) :
    a * c ≡ b * d [ZMOD n] := by
  obtain ⟨x, hx⟩ := h1
  obtain ⟨y, hy⟩ := h2
  use x * c + b * y
  calc
    a * c - b * d = (a - b) * c + b * (c - d) := by ring
    _ = n * x * c + b * (n * y) := by rw [hx, hy]
    _ = n * (x * c + b * y) := by ring

theorem Int.ModEq.pow_three (h : a ≡ b [ZMOD n]) : a ^ 3 ≡ b ^ 3 [ZMOD n] := by
  obtain ⟨x, hx⟩ := h
  use x * (a ^ 2 + a * b + b ^ 2)
  calc
    a ^ 3 - b ^ 3 = (a - b) * (a ^ 2 + a * b + b ^ 2) := by ring
    _ = n * x * (a ^ 2 + a * b + b ^ 2) := by rw [hx]
    _ = n * (x * (a ^ 2 + a * b + b ^ 2)) := by ring

theorem Int.ModEq.refl (a : ℤ) : a ≡ a [ZMOD n] := by
  use 0
  ring

/- # Exercises -/

example : 34 ≡ 104 [ZMOD 5] := by
  use -14
  numbers

theorem Int.ModEq.symm (h : a ≡ b [ZMOD n]) : b ≡ a [ZMOD n] := by
  obtain ⟨x, hx⟩ := h
  use -x
  calc
    b - a = -(a - b) := by ring
    _ = -(n * x) := by rw [hx]
    _ = n * -x := by ring

theorem Int.ModEq.trans (h1 : a ≡ b [ZMOD n]) (h2 : b ≡ c [ZMOD n]) :
    a ≡ c [ZMOD n] := by
  obtain ⟨x, hx⟩ := h1
  obtain ⟨y, hy⟩ := h2
  use x + y
  calc
    a - c = a - b + (b - c) := by ring
    _ = n * x + n * y := by rw [hx, hy]
    _ = n * (x + y) := by ring

example : a + n * c ≡ a [ZMOD n] := by
  use c
  ring

example {a b : ℤ} (h : a ≡ b [ZMOD 5]) : 2 * a + 3 ≡ 2 * b + 3 [ZMOD 5] := by
  obtain ⟨k, hk⟩ := h
  use 2 * k
  calc (2 * a + 3) - (2 * b + 3) = 2 * (a - b) := by ring
    _ = 2 * (5 * k) := by rw [hk]
    _ = 5 * (2 * k) := by ring

example {m n : ℤ} (h : m ≡ n [ZMOD 4]) : 3 * m - 1 ≡ 3 * n - 1 [ZMOD 4] := by
  obtain ⟨k, hk⟩ := h
  use 3 * k
  calc (3 * m - 1) - (3 * n - 1) = 3 * (m - n) := by ring
    _ = 3 * (4 * k) := by rw [hk]
    _ = 4 * (3 * k) := by ring
