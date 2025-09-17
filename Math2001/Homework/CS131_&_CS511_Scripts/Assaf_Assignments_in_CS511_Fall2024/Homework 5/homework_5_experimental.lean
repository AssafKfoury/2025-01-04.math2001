import Library.Basic
import Library.Theory.ModEq.Defs
import AutograderLib

math2001_init

open Classical

theorem dne {p : Prop} (h : ¬¬p) : p :=
  Or.elim (Classical.em p)
    (fun hp : p => hp)
    (fun hnp : ¬p => absurd hnp h)

example {x y : ℕ} (h : y = 0 ∧ y = x) : 0 = x := by
  obtain ⟨h1, h2⟩ := h
  rw [h1] at h2
  exact h2

example {t1 t2 t : ℕ} (h : t1 = t2) : (t + t1) = (t + t2) := by
  have h' : (t + t1) = (t + t1) := by rfl
  conv =>
    lhs
    rw [h]

example {S : Prop} {Q : Type → Prop} (h : ∃x, (S → Q x)) : S → ∃x , Q x := by
  intros s
  obtain ⟨x,hx⟩ := h
  have qx : Q x := hx s
  use x
  exact qx

example {x : Type} {S : Prop} {P : Type → Prop} (h : ∀x, P x → S) : ∃x, (P x → S) := by
  have h' : P x → S := h x
  use x
  apply h'

example {S : Prop} {P : Type → Prop} (h : (∀x, P x) → S) : ∃x, (P x → S) := by
  have dubneg : ¬¬∃x, (P x → S) := by
    intros neg
    have allP : ∀x, P x := by
      intros x
      have dubnegP : ¬¬P x := by
        intros negP
        have pImpS : P x → S := by
          intros hyp
          contradiction
        have exP : ∃x, P x → S := by use x; exact pImpS
        contradiction
      exact dne dubnegP
    have s : S := h allP
    have contra : ∀ x, P x → S := by
      intros x hyp
      exact s
    have ex := contra t
    exact neg ex
  exact dne dubneg
