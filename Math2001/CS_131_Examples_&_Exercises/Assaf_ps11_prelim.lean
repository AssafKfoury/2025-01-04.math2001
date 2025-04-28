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
/- ## two_from_three chooses 2 from 3 nat numbers whose sum is even -/
def two_from_three (x y z : ℕ) : ℕ :=
  cond (((evenN x) ∧ (evenN y)) ∨ ((oddN x) ∧ (oddN y))) (x + y)
    (cond (((evenN x) ∧ (evenN z)) ∨ ((oddN x) ∧ (oddN z))) (x + z)
      (cond (((evenN y) ∧ (evenN z)) ∨ ((oddN y) ∧ (oddN z))) (y + z) (y + z)
      ))

#eval (oddN 3)
#eval (evenN 3) ∧ (evenN 4)
#eval two_from_three 5 6 7

/-
def random_set_of_k_distinct_nats (k n : Nat) : IO (Finset Nat) := do
  if k > n then
    return {}
  else
    let mut result : Finset Nat := {}
    let mut i : Nat := 0
    while i < k do
      let rand_num := IO.randNat (n + 1)
      let new_num : Nat ← rand_num
      if (result.contains new_num) then
          continue
      else
          result := result.insert new_num
          i := i + 1
    return result

-/
