import AdjointTypesLean.Syntax
import Mathlib.Order.Defs.PartialOrder

namespace Adjoint

inductive Formula (Mode : Type) [Preorder Mode] : Mode → Type where

  | atom (m : Mode) (name : String) : Formula Mode m

  | arr {m : Mode} : Formula Mode m → Formula Mode m → Formula Mode m

  | prod {m : Mode} : Formula Mode m → Formula Mode m → Formula Mode m

  | up {m k : Mode} 
      (allowed : k ≤ m) 
      (body : Formula Mode k) : 
    Formula Mode m

  | tensor {m : Mode} : Formula Mode m → Formula Mode m → Formula Mode m

  | unit (m : Mode) : Formula Mode m

  | sum {m : Mode} : Formula Mode m → Formula Mode m → Formula Mode m

  | down {n m : Mode} 
      (allowed : m ≤ n) 
      (body : Formula Mode n) :
    Formula Mode m

-- AnyFormula = {(m,A) | m : Mode, A : Formula Mode m}
abbrev AnyFormula (Mode : Type) [Preorder Mode] :=
  Sigma (Formula Mode)

end Adjoint
