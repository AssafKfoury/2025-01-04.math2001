import Mathlib.Data.Real.Basic
import Library.Basic

-- import Mathlib.Data.Nat.Fib.Basic

math2001_init
open Nat

open Nat

/- # Fibonacci function -/
def Fib : ℕ → ℤ -- ℕ
   | 0 => 0 -- sometimes `Fib 0` is defined as returning value `1`
   | 1 => 1
   | n + 2 => Fib (n) + Fib (n+1)

theorem Fib_Cassini_id (n : ℕ) :
    Fib (n + 2) * Fib (n) - Fib (n+1) * Fib (n+1) = (-1) ^ (n+1) := by
    induction n with
    | zero =>
      calc Fib (0+2) * Fib 0 - Fib (0+1) * Fib (0+1)
                = (-1) ^ (0+1) := by exact rfl
    | succ n ih =>
      calc Fib (n+1+2) * Fib (n+1) - Fib (n+1+1) * Fib (n+1+1)
         = (Fib (n+1) + Fib (n+1+1)) * Fib (n+1) - (Fib n + Fib (n+1)) * Fib (n+1+1) := by rw [Fib,Fib]
       _ = Fib (n+1) * Fib (n+1) - Fib (n) * Fib (n+2)     := by ring
       _ = - (Fib (n+2) * Fib (n) - Fib (n+1) * Fib (n+1)) := by ring
       _ = - (-1) ^ (n+1)                                  := by rw [ih]
       _ = (-1) * (-1) ^ (n+1)                             := by ring
       _ = (-1) ^ (n+2)                                    := by ring
