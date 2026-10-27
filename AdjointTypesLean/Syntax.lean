namespace Adjoint

abbrev Var := String

-- m,k,n,r : modes
-- Δ ⊢ e ⇐ Aₘ : expression e checks against Aₘ
-- Δ ⊢ s ⇒ Aₘ : expression s synthesizes Aₘ

-- We need mutual recursive definitions here
-- https://lean-lang.org/theorem_proving_in_lean4/Induction-and-Recursion/#mutual-recursion
mutual

inductive Check (τ : Type) : Type where
  -- λx. e
  | lam : Var → Check τ → Check τ

  -- {first ⇒ e₁, second ⇒ e₂}
  | prod : Check τ → Check τ → Check τ

  -- susp e (lazy upshift)
  | susp : Check τ → Check τ

  -- (e₁, e₂)
  | pair : Check τ → Check τ → Check τ

  -- match s ((x₁, x₂) ⇒ e')
  -- expression s produces the pair
  -- (Var, Var) 
  -- which is checkable against e'
  | matchPair : Synth τ → (Var × Var) → Check τ → Check τ

  -- (1) 'empty'
  | empty : Check τ

  -- match s (() ⇒ e')
  -- expression s produces the empty state
  -- (1)
  -- which is checkable against e'
  | matchEmpty : Synth τ → Check τ → Check τ
  
  -- left e (binary sum introduction)
  | left : Check τ → Check τ

  -- right e (binary sum introduction)
  | right : Check τ → Check τ

  -- match s (left x ⇒ e₁ | right y ⇒ e₂)
  -- Each branch contains a bound variable and a checkable expression.
  -- The first branch handles left; the second handles right.
  | matchSum : Synth τ → (Var × Check τ) → (Var × Check τ) → Check τ

  -- down e
  -- e is a checkable expr
  | down : Check τ → Check τ

  -- match s (down x ⇒ e')
  -- s produces a bound var checkable
  | matchDown : Synth τ → Var → Check τ → Check τ

  | embed : Synth τ → Check τ

inductive Synth (τ : Type) : Type where
  -- x
  | var : Var → Synth τ

  -- s e
  | app : Synth τ → Check τ → Synth τ

  -- s.first
  | first : Synth τ → Synth τ

  -- s.second
  | second : Synth τ → Synth τ

  -- force s (lazy eval)
  | force : Synth τ → Synth τ

  -- (e : Aₘ)
  | ann : Check τ → τ → Synth τ

end

end Adjoint
