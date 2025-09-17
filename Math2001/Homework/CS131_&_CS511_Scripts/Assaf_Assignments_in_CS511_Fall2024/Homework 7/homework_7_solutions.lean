import Mathlib.Data.Real.Basic
import Library.Basic
import Library.Tactic.Rel
import AutograderLib

math2001_init
set_option pp.funBinderTypes true

--Exercise 5.1.7.6

@[autograded 2]
example {P Q R : Prop} (h : P ↔ Q) : (P ∧ R) ↔ (Q ∧ R) := by
  obtain ⟨h1,h2⟩ := h
  constructor
  · intros pr
    obtain ⟨p,r⟩ := pr
    constructor
    · exact h1 p
    · exact r
  · intros qr
    obtain ⟨q,r⟩ := qr
    constructor
    · exact h2 q
    · exact r

--Exercise 5.1.7.8

@[autograded 2]
example (P Q : Prop) : (P ∨ Q) ↔ (Q ∨ P) := by
  constructor
  · intros pOrQ
    obtain p | q := pOrQ
    · right; apply p
    · left; apply q
  · intros qOrP
    obtain q | p := qOrP
    · right; apply q
    · left; apply p

--Exercise 5.1.7.9

@[autograded 2]
example (P Q : Prop) : ¬(P ∨ Q) ↔ (¬P ∧ ¬Q) := by
  constructor
  · intros notPOrQ
    constructor
    · intros p
      have pOrQ : P ∨ Q := Or.inl p
      exact notPOrQ pOrQ
    · intros q
      have pOrQ : P ∨ Q := Or.inr q
      exact notPOrQ pOrQ
  · intros nPnQ pOrQ
    obtain ⟨nP,nQ⟩ := nPnQ
    obtain p | q := pOrQ
    · contradiction
    · contradiction

--Exercise 5.1.7.11

@[autograded 2]
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

--Exercise 5.1.7.12

@[autograded 2]
example (P : α → β → Prop) : (∃ x y, P x y) ↔ ∃ y x, P x y := by
  constructor
  · intros pxy
    obtain ⟨x,y,hxy⟩ := pxy
    use y; use x; exact hxy
  · intros pyx
    obtain ⟨y,x,hyx⟩ := pyx
    use x; use y; exact hyx

--Exercise 5.1.7.13

@[autograded 2]
example (P : α → β → Prop) : (∀ x y, P x y) ↔ ∀ y x, P x y := by
  constructor
  · intros pxy y x
    exact pxy x y
  · intros pyx x y
    exact pyx y x

--Exercise 5.1.7.14

@[autograded 3]
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

--Exercise 5.2.7.2

@[autograded 3]
example (P Q : Prop) : (¬P → ¬Q) ↔ (Q → P) := by
  constructor
  · intros nPnQ q
    by_cases p : P
    · apply p
    · have contra := nPnQ p
      contradiction
  · intros qp np
    by_cases q : Q
    · have contra := qp q
      contradiction
    · apply q
