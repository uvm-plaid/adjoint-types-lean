import AdjointTypesLean.Formula
import Mathlib.Data.List.Nodup
import Mathlib.Data.List.Perm.Basic

namespace Adjoint

-- x : Aₘ
abbrev Binding (Mode : Type) [Preorder Mode] :=
  Var × AnyFormula Mode

-- Γ ::= · | Γ, x : Aₘ
abbrev Context (Mode : Type) [Preorder Mode] :=
  List (Binding Mode)

variable {Mode : Type} [Preorder Mode]

-- No repeat var names
def ContextWF (Γ : Context Mode) : Prop :=
  (Γ.map Prod.fst).Nodup 

-- Γ ≥ m
def Above (Γ : Context Mode) (m : Mode) : Prop :=
  ∀ b ∈ Γ, m ≤ b.2.1

def Valid (Γ : Context Mode) (m : Mode) : Prop :=
  ContextWF Γ ∧ Above Γ m

def Fresh (x : Var) (Γ : Context Mode) : Prop :=
  x ∉ Γ.map Prod.fst


-- C ∈ σ(m) = canContract
inductive Merge (canContract : Mode → Prop) :
    Context Mode → Context Mode → Context Mode → Prop where

  | nil : Merge canContract [] [] []

  | left {Γ₁ Γ₂ Γ : Context Mode}
      {x : Var} {A : AnyFormula Mode} :
    Merge canContract Γ₁ Γ₂ Γ →
    Fresh x Γ →
    Merge canContract
      ((x, A) :: Γ₁)
      Γ₂
      ((x, A) :: Γ)

  | right {Γ₁ Γ₂ Γ : Context Mode}
      {x : Var} {A : AnyFormula Mode} :
    Merge canContract Γ₁ Γ₂ Γ →
    Fresh x Γ →
    Merge canContract
      Γ₁
      ((x, A) :: Γ₂)
      ((x, A) :: Γ)


  | both {Γ₁ Γ₂ Γ : Context Mode}
      {x : Var} {A : AnyFormula Mode} :
    canContract A.1 →
    Merge canContract Γ₁ Γ₂ Γ →
    Fresh x Γ →
    Merge canContract
      ((x, A) :: Γ₁)
      ((x, A) :: Γ₂)
      ((x, A) :: Γ)

  | perm {Γ₁ Γ₂ Γ Δ₁ Δ₂ Δ : Context Mode} :
    Merge canContract Γ₁ Γ₂ Γ →
    List.Perm Γ₁ Δ₁ →
    List.Perm Γ₂ Δ₂ →
    List.Perm Γ Δ →
    Merge canContract Δ₁ Δ₂ Δ

end Adjoint
