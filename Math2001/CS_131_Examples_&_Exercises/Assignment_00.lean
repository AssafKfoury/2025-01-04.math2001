/- # Assignment 00:
   # You can experiment with this script in the Lean_4 Playground
   # at https://live.lean-lang.org/ which will spare you the need
   # to install Lean_4 on your laptop. And if you do this, then make
   # sure to comment out the two 'imports' on lines 8 and 9, and
   # the two autograder instructions on lines 12 and 44. -/

import Library.Basic
-- import AutograderLib

/- EXERCISE 1 -/
@[autogradedProof 2]
theorem transfer_me_from_A_to_B  (Yes : True) : True := by
   apply sorry
   -- If you would like to transfer from Section A to Section B,
   -- then replace 'sorry' by 'Yes'. Otherwise, keep 'sorry' in place.

/- # Below are three theorems, named: 'thm_1', 'thm_2', and 'thm_3':

   # thm_1 shows that the hypothesis '(h : P ∧ Q)' implies the conclusion 'Q ∧ P'.
   # thm_2 shows that the hypothesis '(h : P ∧ Q)' implies the conclusion 'P ∨ Q'.
   # thm_3 shows that the hypothesis '(h : P ∧ Q)' implies the conclusion 'P ∨ Q'.

   # Note that thm_2 and thm_3 prove the same assertion. But we want you to
   # write a proof for thm_3 which is different from the proof of thm_2.
-/

theorem thm_1 { P Q : Prop } (h : P ∧ Q) : Q ∧ P := by
  obtain ⟨ h_P , h_Q ⟩ := h
  constructor
  apply h_Q
  apply h_P

theorem thm_2 {P Q : Prop} (h : P ∧ Q) : P ∨ Q := by
  obtain ⟨ h_P , h_Q ⟩ := h
  left
  apply h_P

-- For credit in EXERCISE 2, write a proof for thm_3, which is different
-- from the proof of thm_2, i.e. replace 'sorry' by the steps of a proof.
-- Read the proofs of thm_1 and thm_2 for inspiration for what to write.

/- EXERCISE 2 -/
@[autogradedProof 1]
theorem thm_3 {P Q : Prop} (h : P ∧ Q) : P ∨ Q := by
   sorry
