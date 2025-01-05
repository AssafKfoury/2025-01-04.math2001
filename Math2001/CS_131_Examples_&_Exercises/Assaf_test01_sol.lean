import Mathlib.Tactic.GCongr
import Library.Basic
import AutograderLib

theorem AAA_long (a b c : Prop) :
  (a → b) → (c → a) → c → b :=
  by intro h_ab
     intro h_ac
     intro h_c
     obtain h_a := h_ac h_c
     obtain h_b := h_ab h_a
     exact h_b
     done

/-
Exercise 1 (3 points): Prove theorem AAA_long once
more with a proof that does not exceed 5 lines. The
proof of AAA_long has 7 lines.
-/

@[autograded 3] theorem AAA_short (a b c : Prop) :
  (a → b) → (c → a) → c → b :=
  by intros h_ab h_ac h_c
     obtain h_a := h_ac h_c
     obtain h_b := h_ab h_a
     apply h_b
