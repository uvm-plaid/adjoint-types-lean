module

public import AdjointTypesLean.Formula
public import Mathlib.Data.Multiset.Basic

public section

namespace Adjoint

-- x : Aₘ
abbrev Binding (Mode : Type) :=
  Var × Formula Mode

-- Γ ::= · | Γ, x : Aₘ
abbrev Context (Mode : Type) :=
  Multiset (Binding Mode)

variable {Mode : Type}


def Fresh (x : Var) (Γ : Context Mode) : Prop :=
  ∀ b ∈ Γ, b.1 ≠ x


inductive Merge (canContract : Mode → Prop) :
    Context Mode → Context Mode → Context Mode → Prop where

  | nil : Merge canContract 0 0 0

  | left {Γ₁ Γ₂ Γ : Context Mode}
      {x : Var} {A : Formula Mode} :
    Merge canContract Γ₁ Γ₂ Γ →
    Fresh x Γ →
    Merge canContract
      ((x, A) ::ₘ Γ₁)
      Γ₂
      ((x, A) ::ₘ Γ)

  | right {Γ₁ Γ₂ Γ : Context Mode}
      {x : Var} {A : Formula Mode} :
    Merge canContract Γ₁ Γ₂ Γ →
    Fresh x Γ →
    Merge canContract
      Γ₁
      ((x, A) ::ₘ Γ₂)
      ((x, A) ::ₘ Γ)

  | both {Γ₁ Γ₂ Γ : Context Mode}
      {x : Var} {A : Formula Mode} :
    canContract A.mode →
    Merge canContract Γ₁ Γ₂ Γ →
    Fresh x Γ →
    Merge canContract
      ((x, A) ::ₘ Γ₁)
      ((x, A) ::ₘ Γ₂)
      ((x, A) ::ₘ Γ)

end Adjoint
