import Mathlib.Data.Real.Basic
import Library.Basic

-- import Init.Data.Nat.Defs
import Init.Data.Fin
import Std.Data.List.Basic
import Std.Data.List.Lemmas
import Mathlib.Data.Finset.Basic
-- import Mathlib.Data.Nat.Order
import Mathlib.Data.Set.Basic
import Mathlib.Data.List.Basic
-- import Mathlib.Data.List.Lemmas
import Std.Data.List.Lemmas

open Function
open Set

-- import Mathlib.Tactic.Qify
-- import Mathlib.Tactic.Zify
-- import Library.Tactic.ModEq
-- import Mathlib.Tactic
-- import AutograderLib

math2001_init
namespace Int
set_option trace.Meta.Tactic.simp true -- hilights tactic
                                       -- 'simp' wherever it is used?

/- ## evenN and oddN test whether a natural number is even or odd -/
def evenN (n : ℕ) : Bool := (2 ∣ n)
def oddN (n : ℕ) : Bool := ¬ (2 ∣ n)
/- ## cond is the conditional if-then-else -/
def cond : Bool → ℕ → ℕ → ℕ
  | true, x, y => x
  | false, x, y => y
/- ## first_2_in_3 chooses first 2 in 3 nat numbers whose sum is even -/
def first_2_in_3 (x y z : ℕ) : ℕ :=
  cond (((evenN x) ∧ (evenN y)) ∨ ((oddN x) ∧ (oddN y))) (x + y)
    (cond (((evenN x) ∧ (evenN z)) ∨ ((oddN x) ∧ (oddN z))) (x + z)
      (cond (((evenN y) ∧ (evenN z)) ∨ ((oddN y) ∧ (oddN z))) (y + z) (y + z)
      ))

#eval (oddN 3)
#eval (evenN 3) ∧ (evenN 4)
#eval first_2_in_3 5 6 9
#check evenN
-- #eval Finset.ofList [1,2,3]

def PositiveIntSet1 : Type  := { n : ℕ | 0 < n }
def PositiveIntSet2 : Set ℕ := { n : ℕ | 0 < n }
#check (3 ∈ PositiveIntSet2)
-- #eval (3 ∈ PositiveIntSet2)
#reduce (3 ∈ PositiveIntSet2)


def bounded_finset (a b : ℕ) : Finset ℕ :=
   (Finset.range (b + 1)).filter (λ (x : ℕ) => x ≥ a)

--#eval bounded_finset 2 5 -- Output: {2, 3, 4, 5}
--#eval bounded_finset 0 3 -- Output: {0, 1, 2, 3}
--#eval bounded_finset 5 5 -- Output: {5}
--#eval bounded_finset 6 5 -- Output: {}
#check 3 ∈ (Finset.range 5)
#eval 3 ∈ (Finset.range 5)
#eval 13 ∈ (bounded_finset (2^3) (20*15))
#eval 2^3
#check fun (x : Int) => x + 1


def pairs (X Y : Set ℕ) : Set (ℕ × ℕ) := { (x,y) | (x ∈ X) (y ∈ Y) }
def evens : Set ℕ := { x | ∃ (k : ℕ), x = 2 * k }
def odds  : Set ℕ := { x | ∃ (k : ℕ), x = 2 * k + 1 }
def EvensOdds := pairs evens odds
/-
def random_set_of_k_distinct_nats (k n : Nat) : IO (Finset Nat) := do
  if k > n then
    return {}
  else
    let mut result : Finset Nat := {}
    let mut i : Nat := 0
    while i < k do
      let rand_num := StdGen.next -- IO.randNat (n + 1)
      let new_num : Nat ← rand_num
      if  new_num ∈ result then -- (result.contains new_num) then
          continue
      else
          result := insert new_num result -- result.insert new_num
          i := i + 1
    return result

-/
