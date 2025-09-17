/- # ps2-solution.lean -/
import Library.Basic -- **DE-COMMENT BEFORE SUBMISSION TO GRADESCOPE**
import AutograderLib -- **DE-COMMENT BEFORE SUBMISSION TO GRADESCOPE**

open Int
 
theorem ref1 {n : ℤ} (hn : Odd n) : Odd (7 * n - 4) := by
  dsimp [Odd] at hn
  obtain ⟨m,hm⟩ := hn
  dsimp [Odd]
  use 7*m + 1
  rw [hm]
  ring
  done

theorem ref2 {x y : ℤ} (hx : Odd x) (hy : Odd y) : Odd (x * y + 2 * y) := by
  dsimp [Odd]
  dsimp [Odd] at hx
  dsimp [Odd] at hy
  obtain ⟨n,hn⟩ := hx
  obtain ⟨m,hm⟩ := hy
  use 2*n*m + n + 3*m + 1
  rw [hn,hm]
  ring
  done

theorem ref3 {n : ℤ} (hn : Even n) : Odd (n ^ 2 + 2 * n - 5) := by
  dsimp [Even] at hn
  obtain ⟨m,hm⟩ := hn
  dsimp [Odd]
  use 2*m^2 + 2*m - 3
  rw [hm]
  ring
  done

@[autogradedProof 5] 
theorem problem4 {x y : ℤ} : Odd (x + y) → Odd (x ^ 2 + y ^ 2) := by
  have h_xy : x ^ 2 + y ^ 2 = (x + y) ^ 2 - 2*x*y := by ring
  rw [h_xy]
  intro h
  dsimp [Odd] at *
  obtain ⟨m,hm⟩ := h
  use 2*m^2 + 2*m - x*y
  rw [hm]
  ring
  done

@[autogradedProof 5]  
theorem problem5 {a : ℤ} : Even ((a + 1) ^ 2) → Odd (a) := by
  contrapose
  intro h
  rw [← Int.odd_iff_not_even]
  rw [← Int.even_iff_not_odd] at h
  --    in the Lean_4 Playground you may wish to use the 
  --    next two lines instead of the preceding two lines.
  -- rw [Int.not_even_iff_odd]
  -- rw [Int.not_odd_iff_even] at h
  dsimp [Even] at h
  obtain ⟨x,h_x⟩ := h
  dsimp [Odd]
  use 2 * x ^ 2 + 2 * x
  rw [h_x]
  ring
  done
