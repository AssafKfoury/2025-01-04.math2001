import Mathlib.Tactic.GCongr
import Library.Basic
import AutograderLib

/- ## Question 1 (6 points): Connectives and Quantifiers

Complete the following proofs using basic tactics such as
`intro`, `apply`, and `exact`.

-/

@[autogradedProof 2] theorem AAA (a b c : Prop) :
  (a → b) → (c → a) → c → b :=
  by intro h_ab ; intro h_ca ; intro h_c ; 
     apply h_ab ; apply h_ca ; exact h_c
     done

@[autogradedProof 2] theorem BBB (a b c : Prop) :
  (a → b → c) → (a → b) → a → c :=
  by intro h_abc ; intro h_ab ; intro h_a
     apply h_abc ; exact h_a  ; apply h_ab ; exact h_a 
     done 

@[autogradedProof 2] theorem CCC (a b c : Prop) :
  (c → (a → b) → a) → c → b → a :=
  by intro h_caba ; intro h_c ; intro h_b 
     apply h_caba ; exact h_c ; intro h_a ; exact h_b
     done

