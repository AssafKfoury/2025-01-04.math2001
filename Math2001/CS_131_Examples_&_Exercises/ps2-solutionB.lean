import Library.basic

open Int

theorem problem4 {x y : ℤ} : Odd (x + y) → Odd (x ^ 2 + y ^ 2) := by
  intro h
  dsimp [Odd] at *
  obtain ⟨k,hk⟩ := h
  use 2*k^2 + 2*k - x*y
  have h_xy : x ^ 2 + y ^ 2 = (x + y) ^ 2 - 2*x*y := by ring
  rw [h_xy]
  rw [hk]
  ring
  done
