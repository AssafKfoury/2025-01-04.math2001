import Mathlib.Data.Real.Basic
import Library.Basic
import Mathlib.Tactic.Qify
import Mathlib.Tactic.Zify
-- import Library.Tactic.ModEq
-- import Mathlib.Tactic
-- import AutograderLib

math2001_init
namespace Int

set_option trace.Meta.Tactic.simp true -- it seems to hilight tactic
                                       -- 'simp' wherever it is used?

/-
  The calculation in this problem counts the number of distinct walking
  trajectories in Manhattan that require to walk 3 blocks EAST and n
  blocks SOUTH. We assume that Manhattan streets are organized as a
  rectangular grid, with streets running from EAST to WEST and avenues
  running from NORTH to SOUTH.

  In this exercise, you are asked to prove in Lean4 that this number
  of distinct trajectories is:

  (n + 3)! / (3! * n!)
     = (1/2) * Σ { k + k*k | 1 ≤ k ≤ n+1 }
     = (1/2) * [(1 * 2) + (2 * 3) + (3 * 4) + ... + ((n + 1) * (n + 2))
     = (1/6) * (n + 1) * (n + 2) * (n + 3)

  Proofs of these three equalities can be found on the Web. In particular,
  the third and last equality can be found on the Web by searching for:
  "what is the partial sum of the series k * (k+1) as k ranges from 1 to n+1?"
-/

def A : ℕ → ℚ  -- recursive def of ∑ {1, 2, ... ,n}
  | 0 => 0
  | n + 1 => A n + (n + 1)

def B : ℕ → ℚ -- recursive def of ∑ {1*1, 2*2, ... , n*n}
  | 0 => 0
  | n + 1 => B n + (n + 1) * (n + 1)

def fact : ℕ → ℚ -- recursive def of factorial function
  | 0 => 1
  | n + 1 => (fact n) * (n+1)

def F : ℕ → ℚ -- recursive def of (n+3)! / (3! * n!) which is the number
              -- of ways of walking 3 blocks EAST and n blocks SOUTH
  | 0 => 1
  | n + 1 => (F n) * (n + 4) / (n + 1)

def G : ℕ → ℚ -- G is a simpler (non-recursive) def of F
  | n => (n + 3) * (n + 2) * (n + 1) / 6

lemma sum_A (n : ℕ) : A n = n * (n + 1) / 2 := by
  simple_induction n with k IH
  · -- base case
    calc A 0 = 0 := by rw [A]
      _ = 0 * (0 + 1) / 2 := by numbers
  · -- inductive step
    calc
      A (k + 1) = A k + (k + 1) := by rw [A]
      _ = k * (k + 1) / 2 + (k + 1) := by rw [IH]
      _ = (k + 1) * (k + 1 + 1) / 2 := by ring

lemma sum_B (n : ℕ) : B n = n * (n + 1) * (2 * n + 1) / 6 := by
  simple_induction n with k IH
  · calc
      B 0 = 0 := by rw [B]
        _ = 0 * (0 + 1) * (2 * 0 + 1) / 6 := by numbers
  · calc
      B (k + 1) = B k + (k + 1) * (k + 1) := by rw [B]
            _   = k * (k+1) * (2*k + 1) / 6 + (k+1) * (k+1) := by rw [IH]
            _   = (k+1) * (k+1+1) * (2 * (k+1) + 1) / 6 := by ring

lemma sum_AB (n : ℕ) : A (n) + B (n) = n * (n+1) / 2 + n * (n+1) * (2*n + 1) / 6 := by
   simple_induction n with k IH
   · have h1 : A 0 = 0 * (0 + 1) / 2 := by apply sum_A
     have h2 : B 0 = 0 * (0 + 1) * (2 * 0 + 1) / 6 := by apply sum_B
     calc
      A 0 + B 0 = 0 * (0 + 1) / 2 + B 0 := by rw [h1]
              _ = 0 * (0 + 1) / 2 + 0 * (0+1) * (2*0 + 1) / 6 := by rw [h2]
   · calc
      A (k+1) + B (k+1) = A (k) + (k + 1) + (B (k) + (k+1)*(k+1)) := by rw [A,B]
      _ = A (k) + B (k) + (k+1) + (k+1)*(k+1) := by ring
      _ = k * (k+1) / 2 + k * (k+1) * (2*k + 1) / 6 + (k+1) + (k+1)*(k+1) := by rw [IH]
      _ = (k+1) * (k+1+1) / 2 + (k+1)*(k+1+1)*(2*(k+1)+1) / 6 := by ring

/-
theorem problem3 (n : ℕ) : F n = (1/2) * (A (n+1) + B (n+1)) := by
  simple_induction n with k IH
  calc F 0 = 1 := by rw [F]
         _ = 1 / 2 * (0 + (0+1) + (0 + (0+1)*(0+1))) := by ring -- 'by numbers' will work too
         _ = 1 / 2 * (A 0 + (0+1) + (B 0 + (0+1)*(0+1))) := by rw [A,B]
         _ = 1 / 2 * (A (0 + 1) + (B (0+1))) := by exact rfl
  calc F (k+1) = (F k) * (k+4) / (k+1) := by rw [F]
         _  = (1/2) * (A (k+1) + B (k+1)) * (k+4) / (k+1) := by rw [IH]
         _  = (1/2) * ((k+1) * (k+1+1) / 2 + (k+1) * (k+1+1) * (2*(k+1) + 1) / 6) * (k+4) / (k+1) :=
              by rw [sum_AB] ; rw [Nat.cast_add] ; rw [Nat.cast_one]
         _  = (1/2) * (A (k + 1 + 1) + B (k + 1 + 1)) := by rw?
              -- by exact? -- rw [← sum_AB] ; rw [Nat.cast_add] ; rw [Nat.cast_one]
-/

theorem problem3_C (n : ℕ) : G n = 1 / 2 * (A (n  + 1) + B (n + 1)) := by
  simple_induction n with k IH
  · calc
      G 0 = (0 + 3) * (0 + 2) * (0 + 1) / 6 := by exact rfl
        _ = 1 := by ring
        _ = (1/2) * (1 + 1) := by ring
        _ = (1/2) * (1 * (1 + 1) / 2 + 1) := by ring
        _ = (1/2) * ((A 1) + 1) := by rw [A]; rw [A]; ring
        _ = (1/2) * ((A 1) + (B 1)) := by rw [B]; rw[B]; ring
  · calc
      G (k + 1) = (k + 1 + 3) * (k + 1 + 2) * (k + 1 + 1) / 6 :=
            by rw [G]; dsimp; rw [Nat.cast_add, Nat.cast_one]
        _ = (1/2) * ((k + 2) * (k + 3) / 2 + (k + 2) * (k + 3) * (2 * k + 5) / 6) :=
            by ring
        _ = (1/2) * (A (k + 2) + B (k + 2)) :=
            by rw [sum_A, sum_B, Nat.cast_add, Nat.cast_two]; ring

theorem problem3_A (n : ℕ) : F n = (1/2) * (A (n+1) + B (n+1)) := by
  -- qify
  simple_induction n with k IH
  · calc F 0 = 1 := by rw [F]
           _ = 1 / 2 * (0 + (0+1) + (0 + (0+1)*(0+1))) := by ring -- 'by numbers' will work too
           _ = 1 / 2 * (A 0 + (0+1) + (B 0 + (0+1)*(0+1))) := by rw [A,B]
           _ = 1 / 2 * (A (0 + 1) + (B (0+1))) := by exact rfl
  · -- qify
    calc F (k+1) = (F k) * (k+4) / (k+1) := by rw [F]
         _  = (1/2) * (A (k+1) + B (k+1)) * (k+4) / (k+1) := by rw [IH]
         _  = (1/2) * ((A (k+1) + (k+2)) + B (k+1) + (k+2)*(k+2) - (k+2)*(k+3)) * (k+4)/(k+1) := by ring
         _  = (1/2) * (A (k+2) + B (k+1) + (k+2)*(k+2) - (k+2)*(k+3)) * (k+4)/(k+1) :=
            -- by rw? -- apply_mod_cast?
            sorry

theorem problem3_B (n : ℕ) : G n = 1 / 2 * (A (n  + 1) + B (n + 1)) := by
  simple_induction n with k IH
  · -- base case
    calc G 0 = (0 + 3) * (0 + 2) * (0 + 1) / 6 := by exact rfl
           _ = 1 := by ring
           _ = (1/2) * (1 + 1) := by ring
           _ = (1/2) * ((0 + (0+1)) + (0 + (0+1)*(0+1))) := by ring
           _ = (1/2) * (((A 0) + (0+1)) + ((B 0) + (0+1)*(0+1))) := by rw [A,B]
           _ = (1/2) * ( A (0+1) + B (0+1) ) := by exact rfl
  · -- inductive step
    sorry

example (a b c : ℕ) (H1 : a = b + 1) (H2 : b = c) : a = c + 1 :=
  calc a = b + 1 := H1 -- also 'by apply H1' and 'by exact H1' work
       _ = c + 1 := by rw [H2]

example (a b c x y z : ℕ) (h : ¬ x*y*z < 0) (h1 : c < a) (h2 : 0 < b) : c < a + (b + b + b) := by
  -- qify
  -- qify at h h1 h2
  calc
    c < a := by apply h1
    _ = 0 + (a + 0 + 0)  := by exact self_eq_add_left.mpr rfl
    _ = a + 0 + 0 + 0 := by exact Nat.add_comm 0 (a + 0 + 0)
    _ = a + (0 + 0 + 0) := by exact rfl
    _ < a + (b + b + b) := by rel [h2]

example (a b c x y z : ℕ) (h : ¬ x*y*z < 0) (h1 : c < b) : c < a + 3*b := by
  -- zify
  -- zify at h h1
  calc c < b := by apply h1 --
       _ ≤ b + (b + b) := by exact Nat.le_add_right b (b + b)
       _ = b + b + b := by exact Nat.add_comm b (b + b)
       _ = 2 * b + b := by rw [Nat.two_mul]
       _ = 3 * b := by rw [← Nat.succ_mul]
       _ ≤ 3 * b + a := by extra
       _ = a + 3*b := by exact Nat.add_comm (3 * b) a

def pairs (X Y : Set ℕ) : Set (ℕ × ℕ) := { (x,y) | (x ∈ X) (y ∈ Y) }

def evens : Set ℕ := { x | ∃ (k : ℕ), x = 2 * k }
def odds  : Set ℕ := { x | ∃ (k : ℕ), x = 2 * k + 1 }
def EvensOdds := pairs evens odds
#check EvensOdds

#check (25,42)
#eval (25,42).1
#eval (25,42).2
#check [ 2 , 3 ]
#eval (2 ∣ 4)

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
