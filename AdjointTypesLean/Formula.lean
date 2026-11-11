module

public import AdjointTypesLean.Syntax
public import Mathlib.Order.Defs.PartialOrder

public section
namespace Adjoint

-- Raw syntax: mode constraints are checked separately by WellFormed.
inductive Formula (Mode : Type) : Type where
  | atom (m : Mode) (name : String) : Formula Mode

  -- Aₘ ⊸ Bₘ
  | arr : Formula Mode → Formula Mode → Formula Mode

  | prod : Formula Mode → Formula Mode → Formula Mode

  | up (m : Mode) (body : Formula Mode) : Formula Mode

  | tensor : Formula Mode → Formula Mode → Formula Mode

  | unit (m : Mode) : Formula Mode

  | sum : Formula Mode → Formula Mode → Formula Mode

  | down (m : Mode) (body : Formula Mode) : Formula Mode

namespace Formula

variable {Mode : Type}

-- Binary connectives take their mode from the left operand. WellFormed
-- requires the right operand to have the same mode.
def mode : Formula Mode → Mode
  | .atom m _ => m

  | .arr A _ | .prod A _ | .tensor A _ | .sum A _ => A.mode

  | .up m _ | .unit m | .down m _ => m

inductive WellFormed [Preorder Mode] : Formula Mode → Prop where
  | atom {m name} : WellFormed (.atom m name)

  | arr {A B} :
    WellFormed A → WellFormed B → A.mode = B.mode →
    WellFormed (.arr A B)

  | prod {A B} :
    WellFormed A → WellFormed B → A.mode = B.mode →
    WellFormed (.prod A B)

  | up {m A} :
    WellFormed A → A.mode ≤ m → WellFormed (.up m A)

  | tensor {A B} :
    WellFormed A → WellFormed B → A.mode = B.mode →
    WellFormed (.tensor A B)

  | unit {m} : WellFormed (.unit m)

  | sum {A B} :
    WellFormed A → WellFormed B → A.mode = B.mode →
    WellFormed (.sum A B)

  | down {m A} :
    WellFormed A → m ≤ A.mode → WellFormed (.down m A)

end Formula

end Adjoint
