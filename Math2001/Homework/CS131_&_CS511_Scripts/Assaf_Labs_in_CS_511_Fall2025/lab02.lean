-- author: Diala Lteif

import Mathlib
import Mathlib.Tactic

namespace Lean4Setup

-- 1.3.11 Exercises, exercise 1 (Macbeth)
example {x y : ℝ} (h1 : x = 3) (h2 : y = 4 * x - 3) : y = 9 :=
  calc
    y = 4 * x - 3 := by rw [h2]
    _ = 4 * 3 - 3 := by rw [h1]
    _ = 9 := by ring

-- 1.3.11 Exercises, exercise 2 (Macbeth)
example {a b : ℤ} (h : a - b = 0) : a = b :=
  calc
    a = a - b + b := by ring
    _ = 0 + b := by rw[h]
    _ = b := by ring

-- 1.3.11 Exercises, exercise 9 (Macbeth)
example {c : ℚ} (h1 : 4 * c + 1 = 3 * c - 2) : c = -3 :=
  calc
    c = 4 * c - 3 * c := by ring
    _ = 4 * c + 1 - 1 - 3 * c := by ring
    _ = 3 * c - 2 -1 - 3 * c := by rw[h1]
    _ = - 3 := by ring


-- 1.3.10 Example (Macbeth)
example {z : ℝ} (h1 : z ^ 2 - 2 = 0) : z ^ 4 - z ^ 3 - z ^ 2 + 2 * z + 1 = 3 :=
  have h2: z ^ 2 = 2 := by linarith
  calc
    z^4 - z^3 - z^2 + 2*z + 1 = (z^2) * (z^2) - z * (z ^ 2)  - (z ^ 2) + 2*z + 1 := by ring
    _ = (2) * (2) - z * (2) - (2) + 2 * z + 1 := by rw[h2]
    _ = 4 - 2 * z + 2 * z - 2 + 1  := by ring
    _ = 3 := by ring


end Lean4Setup
