import Library.Basic 
import AutograderLib 
import Mathlib.Tactic.PushNeg 
import Mathlib.Logic.Basic 

/- # “At least one of Mike or Will didn’t write the book.”-/
@[autogradedDef 1]
def A_says (A M W : Prop) : Prop :=  sorry

/- # Mike says: “I wrote it if and only if Will wrote it.” -/
@[autogradedDef 1]
def M_says (A M W : Prop) : Prop := sorry

/- # Will says: “We didn’t all write the book.” -/
@[autogradedDef 1]
def W_says (A M W : Prop) : Prop :=   sorry
