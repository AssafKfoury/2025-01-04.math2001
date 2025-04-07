import Library.Basic
import AutograderLib

namespace Hidden

inductive List (α : Type μ) where
  | nil : List α
  | cons : α → List α → List α

namespace List

def length (as : List α) : ℕ :=
  match as with
  | nil       => 0
  | cons a as => 1 + length as

def append (as bs : List α) : List α :=
  match as with
  | nil       => bs
  | cons a as => cons a (append as bs)

def reverse (as : List α) : List α :=
  match as with
  | nil       => nil
  | cons a as => append (reverse as) (cons a nil)

theorem problem1 (as bs : List α) : length (append as bs) = length as + length bs := by
  sorry

theorem problem2 (as : List α) : length (reverse as) = length as := by
  sorry
