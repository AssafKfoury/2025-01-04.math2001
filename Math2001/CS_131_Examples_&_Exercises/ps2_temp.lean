/- # ps2.lean:
   #
   # You can solve the Lean_4 problems in this file for up to 10 extra
   # points in the Lean_4 Playground at https://live.lean-lang.org/
   # which will spare you the need to install Lean_4 on your laptop.
   #
   # To solve the Lean_4 problems below you need to replace every
   # occurrence of 'sorry' with an appropriate expression or an
   # appropriate sequence of commands (which are called "tactics").
   # After you do this, and before submitting your Lean_4 file to
   # Gradescope, make sure to de-comment the 'imports' on line 20,
   # and the autograder instructions on lines
   # -- all these lines are commented out in this file, so you can
   # load the file to the Lean_4 Playground without triggering errors.
   #
-/

import Mathlib.Logic.Basic
import Mathlib.Tactic.Ring
import Library.Basic -- DE-COMMENT BEFORE SUBMISSION TO GRADESCOPE
import AutograderLib -- DE-COMMENT BEFORE SUBMISSION TO GRADESCOPE

open Int

/- # Use the next theorem, odd_to_odd, whose proof is given in full,
   # as a reference for how to solve theorems 'problem4' and 'problem5' -/
theorem odd_to_odd_1 {x y : ℤ} : Odd (x + y) → Odd (x ^ 2 + y ^ 2) := by
  intro h
  dsimp [Odd] at *
  obtain ⟨k,hk⟩ := h
  use 2*k^2 + 2*k - x*y
  have h_xy : x ^ 2 + y ^ 2 = (x + y) ^ 2 - 2*x*y := by ring
  rw [h_xy]
  rw [hk]
  ring
  done

/- # Another way of setting up the proof of odd_to_odd -/
theorem odd_to_odd_2 {x y : ℤ} : Odd (x + y) → Odd (x ^ 2 + y ^ 2) := by
  have h_xy : x ^ 2 + y ^ 2 = (x + y) ^ 2 - 2*x*y := by ring
  rw [h_xy]
  intro h
  dsimp [Odd] at *
  obtain ⟨m,hm⟩ := h
  use 2*m^2 + 2*m - x*y
  rw [hm]
  ring
  done

/- # You can use the tactic contrapose to prove the contrapositive instead.
   # Also, you can use rw [← Int.odd_iff_not_even] to convert proving
   # something is not even into proving that it is odd. The arrow '←' in the
   # rewrite tells Lean which direction to go. By default, it will convert
   # from left to right when using an if-and-only-if statement like
   # Int.odd_iff_not_even.
-/
@[autogradedProof 5]
theorem problem5 {a : ℤ} : Even ((a + 1) ^ 2) → Odd (a) := by
  contrapose
  intro h
  rw [← Int.odd_iff_not_even]
  rw [← Int.even_iff_not_odd] at h
  --    in the Lean_4 Playground you may wish to use the next two
  --    lines 65 and 66, instead of the preceding two lines 61 and 62
  -- rw [Int.not_even_iff_odd]
  -- rw [Int.not_odd_iff_even] at h
  dsimp [Even] at h
  obtain ⟨x,h_x⟩ := h
  dsimp [Odd]
  use 2 * x ^ 2 + 2 * x
  rw [h_x]
  ring
  done
