import Mathlib.Tactic.GCongr
import Library.Basic
import AutograderLib

/- ## Question 1 (6 points): Connectives and Quantifiers

Complete the following proofs using basic tactics such as
`intro`, `apply`, and `exact`.

-/

@[autogradedProof 2] theorem AAA (a b c : Prop) :
  (a → b) → (c → a) → c → b :=
  sorry

@[autogradedProof 2] theorem BBB (a b c : Prop) :
  (a → b → c) → (a → b) → a → c :=
  sorry

@[autogradedProof 2] theorem CCC (a b c : Prop) :
  (c → (a → b) → a) → c → b → a :=
  sorry
