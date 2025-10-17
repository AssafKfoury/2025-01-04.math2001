/- # CS 511, 17 Oct 2025, hw07_solution.lean -/
import Mathlib.Data.Real.Basic
import Library.Basic

math2001_init

/- # The concept of a `group` is defined by 3 axioms, here included as hypotheses.
   # The following theorem proves that the inverse of an element in a group is unique. -/
theorem unique_inv {G : Type*} [Group G]
  (e : G)                                                          -- group identity is `e`
  (hId : ∀ a : G, e * a = a ∧ a * e = a)                           -- identity AXIOM
  (hInv : ∀ a : G, ∃ b : G, a * b = e ∧ b * a = e)                 -- inverse AXIOM
  (hAssoc : ∀ a : G, ∀ b : G, ∀ c : G, (a * b) * c = a * (b * c))  -- associativity AXIOM
     : ∀ (x : G) , ∃! (y : G), ( x * y = e ∧ y * x = e ) := by
  intro x                                -- eliminate `∀` from target, introduce arbitrary elt `x`
  have  m := hInv x                      -- new hyp `m` asserts `x` has an inverse by AXIOM `hInv`
  obtain ⟨ i , m1⟩ := m                  -- new hyp `m1` makes `i` an inverse of `x`
  obtain ⟨ m1L , m1R⟩ := m1              -- hyp `m1` is broken into two hyps, `m1L` and `m1R`
  have h_i_Id := hId i                   -- new hyp `h_i_Id` makes `i` satisfy AXIOM `hId`
  obtain ⟨h_i_IdL,h_i_IdR⟩ := h_i_Id     -- hyp `h_i_Id` is broken into two hyps
  use i                                  -- eliminate `∃!` from target
  dsimp
  constructor                            -- break up target into two goals
  · constructor                          -- break up target of first goal
    · exact m1L
    · exact m1R
  · intros b hb                          -- eliminate `∀` from target of second goal
    obtain ⟨hb1,hb2⟩ := hb
    symm
    have hAssoc' := hAssoc i x b
    have hbId := hId b
    obtain ⟨hbIdL,hbIdR⟩ := hbId
    calc
       i =  i * e := by rw [h_i_IdR]
       _ =  i * (x * b) := by rw [← hb1]
       _ = (i * x) * b := by rw [hAssoc']
       _ =  e * b := by rw [m1R]
       _ =  b := by rw [hbIdL]

/- # Alternative proof of the uniquesess of the inverse of an element in a group. -/
theorem unique_inv_2 {G : Type*} [Group G]
  (e : G)                                                          -- group identity is `e`
  (hId : ∀ a : G, e * a = a ∧ a * e = a)                           -- identity AXIOM
  (hInv : ∀ a : G, ∃ b : G, a * b = e ∧ b * a = e)                 -- inverse AXIOM
  (hAssoc : ∀ a : G, ∀ b : G, ∀ c : G, (a * b) * c = a * (b * c))  -- associativity AXIOM
     : ∀ (x y z: G) , ( x * y = e ∧ x * z = e → y = z ) := by
  sorry
