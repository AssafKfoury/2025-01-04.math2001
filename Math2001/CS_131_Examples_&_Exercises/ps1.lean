/- # ps1.lean: 
   # 
   # You can solve Problem 6 of Assignment #1 in the Lean_4 Playground 
   # at https://live.lean-lang.org/ which will spare you the need 
   # to install Lean_4 on your laptop.  
   # 
   # What you need to do is to replace every occurrence of 'sorry'
   # with an appropriate expression or an appropriate sequence of
   # commands (which are called "tactics"). After you do this, and 
   # before submitting your Lean_4 file to Gradescope, make sure
   # to de-comment the two 'imports' on lines 18 and 19, and all 
   # autograder instructions on lines 33, 37, 41, 74, 86, 88, 99, 101
   # -- all these lines are commented out in this file, which would 
   # otherwise disrupt the operation of the Lean_4 Playground. 
   # 
-/

import Library.Basic -- DE-COMMENT BEFORE SUBMISSION TO GRADESCOPE
import AutograderLib -- DE-COMMENT BEFORE SUBMISSION TO GRADESCOPE
import Mathlib.Tactic.PushNeg -- needed in order to use tactic push_neg
import Mathlib.Logic.Basic -- basic facts in logic

/- # useful globally declared variables in lines 24 and 25 -/
variable (A M W : Prop)

/- # Part (a): for each of the three definitions to follow (A_says
   # on line 34, M_says on line 38, and W_says on line 42) only one
   # from the following 10 formulas is correct:
   # A ∨ M , A ∨ W , ¬ M ∨ A , ¬ M ∨ ¬ W , A ↔ M , 
   # A ↔ W , M ↔ W , A ∧ ¬ M , A ∧ ¬ W , ¬ (A ∧ M ∧ W)-/

/- # “At least one of Mike or Will didn’t write the book.”-/
@[autogradedDef 1]
def A_says (A M W : Prop) : Prop :=  sorry

/- # Mike says: “I wrote it if and only if Will wrote it.” -/
@[autogradedDef 1]
def M_says (A M W : Prop) : Prop := sorry

/- # Will says: “We didn’t all write the book.” -/
@[autogradedDef 1]
def W_says (A M W : Prop) : Prop :=   sorry

/- # The following axioms express the equivalences in Table 1.5.1 in the zyBook.
   # Use them in any way that seems appropriate. You will probably not use them all. -/

axiom associative1 {p q r : Prop} : (p ∨ q) ∨ r ↔ p ∨ (q ∨ r)
axiom associative2 {p q r : Prop} : (p ∧ q) ∧ r ↔ p ∧ (q ∧ r)
axiom distributive1 {p q r : Prop} : p ∨ (q ∧ r) ↔ (p ∨ q) ∧ (p ∨ r)
axiom distributive2 {p q r : Prop} : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r)
axiom identity1 {p : Prop} : p ∨ False ↔ p
axiom identity2 {p : Prop} : p ∧ True ↔ p
axiom domination1 {p : Prop} : p ∧ False ↔ False
axiom domination2 {p : Prop} : p ∨ True ↔ True
axiom doublenegation {p : Prop} : ¬¬p ↔ p
axiom complement1 {p : Prop} : p ∧ ¬p ↔ False
axiom complement2 {p : Prop} : p ∨ ¬p ↔ True
axiom commutative1 {p q : Prop} : p ∨ q ↔ q ∨ p
axiom commutative2 {p q : Prop} : p ∧ q ↔ q ∧ p
axiom idempotent1 {p : Prop} : p ∨ p ↔ p
axiom idempotent2 {p : Prop} : p ∧ p ↔ p
axiom demorgan1 {p q : Prop} : ¬(p ∨ q) ↔ ¬p ∧ ¬q
axiom demorgan2 {p q : Prop} : ¬(p ∧ q) ↔ ¬p ∨ ¬q
axiom absorption1 {p q : Prop} : p ∨ (p ∧ q) ↔ p
axiom absorption2 {p q : Prop} : p ∧ (p ∨ q) ↔ p
axiom conditional1 {p q : Prop} : p → q ↔ ¬p ∨ q
axiom conditional2 {p q : Prop} : (p ↔ q) ↔ (p → q) ∧ (q → p)

/- # Part (b): Aaron's and Will's statements are together equivalent to just
   # Aaron's statement. To get credit for (b), you first need to replace
   # (A_says A M W) by your definition in line 34 and (W_says A M W) by your
   # definition in line 42, and also replace 'sorry' by a sequence of tactics. -/

@[autogradedProof 5]
theorem A_says_and_W_says_equiv_A_says (A M W : Prop) : 
          (A_says A M W) ∧ (W_says A M W) ↔ (A_says A M W) := by
  sorry 

/- # Part (c): Aaron’s and Mike’s statements are together equivalent to 
   # “neither Mike nor Will wrote the book”. To get credit for (c), you first 
   # replace (A_says A M W), (M_says A M W), and (neither_M_nor_W A M W) by the
   # definitions you write for them, with the third definition being that of
   # (neither_M_nor_W A M W) below, and you replace 'sorry' by a sequence of tactics. -/

/- # "neither Mike nor Will wrote the book” -/
@[autogradedDef 1]
def neither_M_nor_W (A M W : Prop) : Prop :=  sorry
@[autogradedProof 5]
theorem A_says_and_W_says_equiv_neither_M_nor_W (A M W : Prop) : 
     (A_says A M W) ∧ (M_says A M W) ↔ (neither_M_nor_W A M W) := by
   sorry  

/- # Part (d): The statement “if any of the three wrote the book, then only
   # M wrote it” is equivalent to "neither A nor W wrote it". To get credit
   # for (d), you replace (any_Wrote_It A M W) by the definition you write
   # for it (below) and you also replace 'sorry' by a sequence of tactics. -/

/- # “if any of the three wrote the book, then only M wrote it” -/
@[autogradedDef 1]
def any_Wrote_It (A M W : Prop) : Prop := sorry
@[autogradedProof 5]
theorem any_Wrote_it_equiv_nor_A_nor_W (A M W : Prop) : (any_Wrote_It A M W) ↔ (¬ A ∧ ¬ W) := by
   sorry 
