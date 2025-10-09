import Library.Basic
import Std.Data.List.Lemmas

math2001_init
namespace Nat

namespace PL

-- Propositional logic
inductive PL_wff where
| var : Nat → PL_wff
| not : PL_wff → PL_wff
| and : PL_wff → PL_wff → PL_wff
| or  : PL_wff → PL_wff → PL_wff
| imp : PL_wff → PL_wff → PL_wff
| iff : PL_wff → PL_wff → PL_wff

abbrev myVar := PL_wff.var
abbrev myNot := PL_wff.not
abbrev myAnd := PL_wff.and
abbrev myOr  := PL_wff.or
abbrev myImp := PL_wff.imp
abbrev myIff := PL_wff.iff

#check PL_wff.var 3
#check myVar 3

abbrev Valuation := Nat → Bool

def evalProp : PL_wff → Valuation → Bool
  | .var i    => fun v => v i
  | .not φ    => fun v => !(evalProp φ v)
  | .and φ ψ  => fun v => evalProp φ v && evalProp ψ v
  | .or φ ψ   => fun v => evalProp φ v || evalProp ψ v
  | .imp φ ψ  => fun v => !evalProp φ v || evalProp ψ v
  | .iff φ ψ  => fun v => evalProp φ v == evalProp ψ v

-- Test examples
def φ1 : PL_wff := .not (.var 0)
#eval evalProp φ1 (fun i => i = 0)   -- expect false
#eval evalProp φ1 (fun i => i ≠ 0)   -- expect true

def φ2 : PL_wff := .imp (.var 0) (.var 1)
#eval evalProp φ2 (fun i => if i = 0 then true else false)  -- expect false when var1=false

end PL
end Nat
