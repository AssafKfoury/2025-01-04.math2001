/-
2025-08-27
Dependent types are types that contain non-type expressions.
A common source of dependent types is a named argument to a function.

In the following example, the type "if b then Nat else String"
contains the argument "b" as a non-type expression.
-/

def natOrStringThree (b : Bool) : if b then Nat else String :=
  match b with
  | true => (3 : Nat)
  | false => "three"

#check [3 , 5 , 8]
#check [3 , 5.0 , 8]
#check (3 , 5 , 8)
#check (3 , 5.0 , 8)
#check (3 , 5 , 8).fst
#eval (3 , 5 , 8).snd.fst

#check natOrStringThree
#check natOrStringThree true
#eval natOrStringThree true
#check natOrStringThree false
#eval natOrStringThree false
