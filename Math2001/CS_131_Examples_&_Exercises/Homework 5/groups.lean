import Mathlib.Data.Real.Basic
import Library.Basic

math2001_init

theorem unique_inv {G : Type*} [Group G] (e : G)
(hId : ∀ a : G, e * a = a ∧ a * e = a)
(hInv : ∀ a : G, ∃ b : G, a * b = e ∧ b * a = e)
(hAssoc : ∀ a : G, ∀ b : G, ∀ c : G, (a * b) * c = a * (b * c))
: ∀ a : G, ∃! b : G, a * b = e ∧ b * a = e := by
  intros a
  have haInv := hInv a
  obtain ⟨aInv,haInv⟩ := haInv
  obtain ⟨haInvL,haInvR⟩ := haInv
  have haInvId := hId aInv
  obtain ⟨haInvIdL,haInvIdR⟩ := haInvId
  use aInv
  dsimp
  constructor
  · constructor
    · exact haInvL
    · exact haInvR
  · intros b hb
    obtain ⟨hb1,hb2⟩ := hb
    symm
    have hAssoc' := hAssoc aInv a b
    have hbId := hId b
    obtain ⟨hbIdL,hbIdR⟩ := hbId
    calc
      aInv = aInv * e := by rw [haInvIdR]
      _ = aInv * (a * b) := by rw [← hb1]
      _ = (aInv * a) * b := by rw [hAssoc']
      _ = e * b := by rw [haInvR]
      _ = b := by rw [hbIdL]
