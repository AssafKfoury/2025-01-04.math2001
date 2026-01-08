/- # CS 511, 7 Oct 2025, hw05_prelim_sol2.lean -/

import Library.Basic

namespace Hidden

inductive List (α : Type μ) where
  | nil : List α
  | cons : α → List α → List α

namespace List

#check nil   #check cons

def A : List ℕ := nil
def B : List ℕ := cons 3 A
def C : List ℕ := cons 5 B
def D : List ℕ := cons 2 C
def E : List ℕ := List.cons 1 (List.cons 2 (List.cons 5 (List.cons 3 List.nil)))

#print D
#print E
#reduce D
#reduce E

def length (as : List α) : ℕ :=
  match as with
  | nil       => 0
  | cons a as => 1 + length as

#eval length D
#eval length E

def append (as bs : List α) : List α :=
  match as with
  | nil       => bs
  | cons a as => cons a (append as bs)

def F : List ℕ := append D E
#reduce F

def reverse (as : List α) : List α :=
  match as with
  | nil       => nil
  | cons a as => append (reverse as) (cons a nil)

def G : List ℕ := reverse F
#reduce G

/- In the proof of `problem1` below I use pe-defined library function `zero_add`
   but you don't have to use it, there are alternative ways -/
#check zero_add

theorem problem1 (as bs : List α) : length (append as bs) = length as + length bs := by
  induction as with
  | nil => dsimp [length] ;
           dsimp [append] ;
           rw [zero_add]
  | cons x xs IH => dsimp [length] ;
                    rw [IH] ;
                    ring

theorem problem2 (as : List α) : length (reverse as) = length as := by
   sorry
