/- # ps1-solution.lean:
   #
   # You can solve Problem 6 of Assignment #1 in the Lean_4 Playground
   # at https://live.lean-lang.org/ which will spare you the need
   # to install Lean_4 on your laptop.
   #
   # What you need to do is to replace every occurrence of 'sorry'
   # with an appropriate expression or an appropriate sequence of
   # commands (which are called "tactics"). After you do this, and
   # before submitting your Lean_4 file to Gradescope, make sure
   # to de-comment the two 'imports' on lines 17 and 18, and all the
   # autograder instructions on lines 33, 37, 41, 49, 60, 62, 73, 75
   # -- all these lines are commented out in this file, which would
   # otherwise disrupt the operation of the Lean_4 Playground.
-/

import Library.Basic -- DE-COMMENT BEFORE SUBMISSION TO GRADESCOPE
import AutograderLib -- DE-COMMENT BEFORE SUBMISSION TO GRADESCOPE
import Mathlib.Tactic.PushNeg -- needed in order to use tactic push_neg
import Mathlib.Logic.Basic -- basic facts in logic

/- # useful globally declared variables in lines 24 and 25 -/
variable (A M W : Prop)
variable (Asays Msays Wsays neitherMnorW anyWroteIt : Prop)

/- # Part (a): for each of the three definitions to follow (A_says
   # on line 34, M_says on line 38, and W_says on line 42) only one
   # from the following 10 formulas is correct:
   # A ∨ M , A ∨ W , ¬ M ∨ A , ¬ M ∨ ¬ W , A ↔ M ,
   # A ↔ W , M ↔ W , A ∧ ¬ M , A ∧ ¬ W , ¬ (A ∧ M ∧ W)-/

/- # “At least one of Mike or Will didn’t write the book.”-/
-- @[autogradedDef 1]
def A_says : Prop :=  ¬ M ∨ ¬ W

/- # Mike says: “I wrote it if and only if Will wrote it.” -/
-- @[autogradedDef 1]
def M_says : Prop :=  M ↔ W

/- # Will says: “We didn’t all write the book.” -/
-- @[autogradedDef 1]
def W_says : Prop :=  ¬ (A ∧ M ∧ W)

/- # Part (b): Aaron's and Will's statements are together equivalent
   # to just Aaron's statement. To get credit for (b), you first need to
   # replace variables Asays and Wsays by your definitions of A_says and
   # W_says, in addition to replacing 'sorry' by a sequence of tactics. -/

-- @[autogradedProof 5]
theorem A_says_and_W_says_equiv_A_says : (¬ M ∨ ¬ W) ∧ (¬ (A ∧ M ∧ W)) ↔ (¬ M ∨ ¬ W) := by
   constructor
   · intro ⟨h1,h2⟩
     exact h1
   · intro h1
     constructor
     · exact h1
     · push_neg
       intros a m
       cases h1
       contradiction
       assumption
   done

/- # Part (c): Aaron’s and Mike’s statements are together equivalent to
   # “neither Mike nor Will wrote the book”. To get credit for (c), you first
   # need to substitute for variables Asays, Msays, and neitherMnorW, your
   # definitions of A_says, M_says, and neither_M_nor_W (which you have to
   # write below), in addition to replacing 'sorry' by a tactic sequence. -/

/- # "neither Mike nor Will wrote the book” -/
-- @[autogradedDef 1]
def neither_M_nor_W : Prop := (¬ M ∧ ¬ W)
-- @[autogradedProof 5]
theorem A_says_and_W_says_equiv_neither_M_nor_W : (¬ M ∨ ¬ W) ∧ (M ↔ W) ↔ (¬ M ∧ ¬ W) := by
  constructor
  · intro ⟨h1,h2⟩
    obtain ⟨h2,h3⟩ := h2
    obtain h1 | h1 := h1
    · constructor
      · exact h1
      · intro w
        have h4 := h3 w
        contradiction
    · constructor
      · intro m
        have h4 := h2 m
        contradiction
      · exact h1
  · intro ⟨h1,h2⟩
    constructor
    · exact Or.inl h1
    · constructor
      · intro m
        exfalso
        exact h1 m
      · intro w
        exfalso
        exact h2 w
  done

/- # Part (d): The statement “if any of the three wrote the book, then only
   # M wrote it” is equivalent to "neither A nor W wrote it". To get credit
   # for (d), you first need to substitute for variable anyWroteIt your
   # definition of any_Wrote_It (see below), in addition to replacing
   # 'sorry' by a sequence of tactics. -/

/- # “if any of the three wrote the book, then only M wrote it” -/
-- @[autogradedDef 1]
def any_Wrote_It : Prop := A ∨ M ∨ W → ¬A ∧ M ∧ ¬W
-- @[autogradedProof 5]
theorem any_Wrote_it_equiv_nor_A_nor_W : (A ∨ M ∨ W → ¬A ∧ M ∧ ¬W) ↔ (¬ A ∧ ¬ W) := by
  constructor
  · intro h
    constructor
    · intro a
      have h1 := h (Or.inl a)
      obtain ⟨h1,h2,h3⟩ := h1
      contradiction
    · intro w
      have h1 := h (Or.inr (Or.inr w))
      obtain ⟨h1,h2,h3⟩ := h1
      contradiction
  · intros h1 h2
    obtain ⟨na,nw⟩ := h1
    constructor
    · exact na
    · constructor
      · obtain a | m | w := h2
        · contradiction
        · exact m
        · contradiction
      · exact nw
  done
