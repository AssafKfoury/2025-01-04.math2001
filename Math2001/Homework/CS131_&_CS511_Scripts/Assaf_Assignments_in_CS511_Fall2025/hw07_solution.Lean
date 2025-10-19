/- # CS 511, 17 Oct 2025, hw07_solution.lean -/
import Mathlib.Data.Real.Basic
import Library.Basic
import Library.Theory.ModEq.Defs
import Library.Tactic.ModEq
import Library.Theory.ParityModular

math2001_init

/- # EXERCISE 3 -/

/- # Example 4.5.5 -/
example (n : ℤ) : Int.Odd n ↔ ¬ Int.Even n := by
  constructor
  · intros hOdd hEven
    rw [Int.odd_iff_modEq] at hOdd
    rw [Int.even_iff_modEq] at hEven
    have h :=
    calc
      0 ≡ n [ZMOD 2] := by rel [hEven]
      _ ≡ 1 [ZMOD 2] := by rel [hOdd]
    numbers at h
  · intro hNotEven
    obtain h1 | h2 := Int.even_or_odd n
    · contradiction
    · apply h2

/- # Example 4.5.6 -/
example (n : ℤ) : ¬(n ^ 2 ≡ 2 [ZMOD 3]) := by
  intro h
  mod_cases hn : n % 3
  · have h :=
    calc (0:ℤ) = 0 ^ 2 := by numbers
      _ ≡ n ^ 2 [ZMOD 3] := by rel [hn]
      _ ≡ 2 [ZMOD 3] := by rel [h]
    numbers at h -- contradiction!
  · have h :=
    calc
      (1 : ℤ) = 1 ^ 2 := by numbers
      _ ≡ n ^ 2 [ZMOD 3] := by rel [hn]
      _ ≡ 2 [ZMOD 3] := by rel [h]
    numbers at h
  · have h' :=
    calc
      (1 : ℤ) ≡ 1 + 3*1 [ZMOD 3] := by extra
      _ = 2^2 := by ring
      _ ≡ n^2 [ZMOD 3] := by rel [hn]
      _ ≡ 2 [ZMOD 3] := h
    numbers at h'

/- # EXERCISE 4 -/

/- # Exercise 5.1.7.11 -/
example {P Q : α → Prop} (h : ∀ x, P x ↔ Q x) : (∃ x, P x) ↔ (∃ x, Q x) := by
  constructor
  · intros exP
    obtain ⟨x,hx⟩ := exP
    have h' := h x
    obtain ⟨h1,h2⟩ := h'
    use x
    exact h1 hx
  · intros exQ
    obtain ⟨x,hx⟩ := exQ
    have h' := h x
    obtain ⟨h1,h2⟩ := h'
    use x
    exact h2 hx

/- # Exercise 5.1.7.12 -/
example (P : α → β → Prop) : (∃ x y, P x y) ↔ ∃ y x, P x y := by
  constructor
  · intros pxy
    obtain ⟨x,y,hxy⟩ := pxy
    use y; use x; exact hxy
  · intros pyx
    obtain ⟨y,x,hyx⟩ := pyx
    use x; use y; exact hyx

/- # Exercise 5.1.7.14 -/
example (P : α → Prop) (Q : Prop) : ((∃ x, P x) ∧ Q) ↔ ∃ x, (P x ∧ Q) := by
  constructor
  · intros h
    obtain ⟨h,q⟩ := h
    obtain ⟨x,px⟩ := h
    use x
    constructor
    · apply px
    · apply q
  · intros h
    obtain ⟨x,hx⟩ := h
    obtain ⟨px,q⟩ := hx
    constructor
    · use x; apply px
    · apply q

/- # PROBLEM 2 -/

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
    intros x y z
    intro h_yz
    obtain ⟨ h_y , h_z ⟩ := h_yz
    -- obtain h_xLR := hInv x ;
    obtain h_yLR := hId y ; obtain h_zLR := hId z
    obtain ⟨ h_yL , h_yR ⟩ := h_yLR ; obtain ⟨ h_zL , h_zR ⟩ := h_zLR
    obtain h_Assoc_xyz := hAssoc x y z
    calc y = y * e := by rw [h_yR]
         _ = y * (x * z) := by rw [h_z]
         _ = (y * x) * z := by rw [hAssoc]
         _ = e * z := by rw? -- [hAssoc] -- [hInv]  --  [← h_Assoc_xyz]

  sorry
