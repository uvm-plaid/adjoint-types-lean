module

public import AdjointTypesLean.Syntax
public import AdjointTypesLean.Formula
public import AdjointTypesLean.Context
public import Mathlib.Data.Multiset.MapFold

public section

namespace Adjoint

variable {Mode : Type} [Preorder Mode]

def AllWeak (W : Mode → Prop) (Γ : Context Mode) : Prop :=
  ∀ b ∈ Γ, W b.2.mode

def Above (Γ : Context Mode) (m : Mode) : Prop :=
  ∀ b ∈ Γ, m ≤ b.2.mode

def ContextWF {Mode : Type} [Preorder Mode]
    (Γ : Context Mode) : Prop :=
  (Γ.map Prod.fst).Nodup ∧
  ∀ b ∈ Γ, b.2.WellFormed

mutual

inductive Checks (W C : Mode → Prop) :
    Context Mode →
    Check (Formula Mode) →
    Formula Mode → Prop where

  | embed { Γ s } { A : Formula Mode } :
    Synthesizes W C Γ s A →
    Checks W C Γ (.embed s) A

  | lam { Γ x e } { A B : Formula Mode } :
    -- Look into this
    A.WellFormed →
    A.mode = B.mode →
    Fresh x Γ →
    Checks W C ((x, A) ::ₘ Γ) e B →
    Checks W C Γ (.lam x e) (.arr A B)

  | prod { Γ e₁ e₂ } { A B : Formula Mode } :
    A.mode = B.mode →
    Checks W C Γ e₁ A →
    Checks W C Γ e₂ B →
    Checks W C Γ (.prod e₁ e₂) (.prod A B)

  | susp { Γ e m } { A : Formula Mode } :
    A.mode ≤ m →
    Above Γ m →
    Checks W C Γ e A →
    Checks W C Γ (.susp e) (.up m A)

  | pair { Γ Γ₁ Γ₂ e₁ e₂ } { A B : Formula Mode } :
    A.mode = B.mode →
    Merge C Γ₁ Γ₂ Γ →
    Checks W C Γ₁ e₁ A →
    Checks W C Γ₂ e₂ B →
    Checks W C Γ (.pair e₁ e₂) (.tensor A B)

  -- Γ₁ ⊢ s ⇒ Aₘ ⨂  Bₘ  Γ₂, y:Bₘ ⊢ e₂ ⇐ Cᵣ  Γ₁ ≥ m ≥ r
  --                    Γ₂, x:Aₘ ⊢ e₁ ⇐ Cᵣ
  -- __________________________________________________
  -- Γ₁; Γ₂ ⊢ match s {(x, y) ⇒ e} ⇐ Cᵣ
  | matchPair { Γ Γ₁ Γ₂ s x y e } { A B R : Formula Mode } :
    R.mode ≤ A.mode →
    Merge C Γ₁ Γ₂ Γ →
    Fresh y Γ₂ →
    Fresh x ((y, B) ::ₘ Γ₂) →
    Synthesizes W C Γ₁ s (.tensor A B) →
    Checks W C ((x, A) ::ₘ (y, B) ::ₘ Γ₂) e R →
    Checks W C Γ (.matchPair s (x, y) e) R

  | empty { Γ m } :
    ContextWF Γ →
    Above Γ m →
    AllWeak W Γ →
    Checks W C Γ .empty (.unit m)

  | matchEmpty { Γ Γ₁ Γ₂ s e m } { R : Formula Mode } :
    Above Γ R.mode →
    R.mode ≤ m →
    Merge C Γ₁ Γ₂ Γ →
    Synthesizes W C Γ₁ s (.unit m) →
    Checks W C Γ₂ e R →
    Checks W C Γ (.matchEmpty s e) R

  | left { Γ e } { A B : Formula Mode } :
    A.mode = B.mode →
    B.WellFormed →
    Checks W C Γ e A →
    Checks W C Γ (.left e) (.sum A B)

  | right { Γ e } { A B : Formula Mode } :
    A.mode = B.mode →
    A.WellFormed →
    Checks W C Γ e B →
    Checks W C Γ (.right e) (.sum A B)

  -- Γ₁ ⊢ s ⇒ Aₘ ⊕ Bₘ   Γ₂, y:Bₘ ⊢ e₂ ⇐ Cᵣ  Γ₁ ≥ m ≥ r
  --                    Γ₂, x:Aₘ ⊢ e₁ ⇐ Cᵣ
  -- __________________________________________________
  -- Γ₁; Γ₂ ⊢ match s {left x ⇒ e₁ | right y ⇒ e₂} ⇐ Cᵣ
  | matchSum { Γ₁ Γ₂ Γ s x y e₁ e₂} { A B R : Formula Mode } :
    R.mode ≤ A.mode →
    Merge C Γ₁ Γ₂ Γ →
    Fresh x Γ₂ → -- x and y are bound in seperate branches
    Fresh y Γ₂ →
    Synthesizes W C Γ₁ s (.sum A B) →
    Checks W C ((x, A) ::ₘ Γ₂) e₁ R → -- left branch
    Checks W C ((y, B) ::ₘ Γ₂) e₂ R → -- right branch
    Checks W C Γ (.matchSum s (x, e₁) (y, e₂)) R

  | down { Γ₁ Γ₂ Γ e m } { A : Formula Mode } :
    m ≤ A.mode →
    ContextWF Γ →
    Above Γ m →
    AllWeak W Γ₁ →
    Merge C Γ₁ Γ₂ Γ →
    Checks W C Γ₂ e A →
    Checks W C Γ (.down e) (.down m A)

  | matchDown { Γ₁ Γ₂ Γ s x e m} { A R : Formula Mode } :
    R.mode ≤ m →
    Merge C Γ₁ Γ₂ Γ →
    Synthesizes W C Γ₁ s (.down m A) →
    Checks W C ((x, A) ::ₘ Γ₂) e R →
    Checks W C Γ (.matchDown s x e) R

inductive Synthesizes (W C : Mode → Prop) :
    Context Mode →
    Synth (Formula Mode) →
    Formula Mode → Prop where

  | var { ΓW Γ x  } { A : Formula Mode } :
    ContextWF Γ →
    Above Γ A.mode →
    AllWeak W ΓW →
    Merge C ΓW ((x, A) ::ₘ 0) Γ →
    Synthesizes W C Γ (.var x) A

  | ann { Γ e } { A : Formula Mode } :
    Checks W C Γ e A →
    Synthesizes W C Γ (.ann e A) A

  -- s e
  | app { Γ Γ₁ Γ₂ s e } { A B : Formula Mode } :
    Merge C Γ₁ Γ₂ Γ →
    Synthesizes W C Γ₁ s (.arr A B) →
    Checks W C Γ₂ e A →
    Synthesizes W C Γ (.app s e) B

  -- s.first
  | first { Γ s } { A B : Formula Mode } :
    Synthesizes W C Γ s (.prod A B) →
    Synthesizes W C Γ (.first s) A

  -- s.second
  | second { Γ s } { A B : Formula Mode } :
    Synthesizes W C Γ s (.prod A B) →
    Synthesizes W C Γ (.second s) B

  -- force s (lazy eval)
  | force { Γ₁ Γ₂ Γ s m } { A : Formula Mode } :
    ContextWF Γ →
    Above Γ A.mode →
    Above Γ₂ m →
    AllWeak W Γ₁ →
    Merge C Γ₁ Γ₂ Γ →
    Synthesizes W C Γ₂ s (.up m A) →
    Synthesizes W C Γ (.force s) A


end

-- If Δ ⊢ e ⇐ A then A is well-formed ⊸

end Adjoint
