namespace Adjoint

abbrev Var := String

-- m,k,n,r : modes
-- Δ ⊢ e ⇐ Aₘ : expression e checks against Aₘ
-- Δ ⊢ s ⇒ Aₘ : expression s synthesizes Aₘ

-- We need mutual recursive definitions here
-- https://lean-lang.org/theorem_proving_in_lean4/Induction-and-Recursion/#mutual-recursion
mutual


inductive Check (m : Type) : Type where
  -- λx. e
  | lam : Var → Check m → Check m

  -- {first ⇒ e₁, second ⇒ e₂}
  | prod : Check m → Check m → Check m

  -- susp e (lazy upshift)
  | susp : Check m → Check m

  -- (e₁, e₂)
  | pair : Check m → Check m → Check m

  -- match s ((x₁, x₂) ⇒ e')
  -- expression s produces the pair
  -- (Var, Var) 
  -- which is checkable against e'
  | matchPair : Synth m → (Var × Var) → Check m → Check m

  -- (1) 'empty'
  | empty : Check m

  -- match s (() ⇒ e')
  -- expression s produces the empty state
  -- (1)
  -- which is checkable against e'
  | matchEmpty : Synth m → Check m → Check m

  -- left e (binary sum introduction)
  | left : Check m → Check m

  -- right e (binary sum introduction)
  | right : Check m → Check m

  -- match s (left x ⇒ e₁ | right y ⇒ e₂)
  -- Each branch contains a bound variable and a checkable expression.
  -- The first branch handles left; the second handles right.
  | matchSum :
      Synth m → (Var × Check m) → (Var × Check m) → Check m

  -- down e
  -- e is a checkable expr
  | down : Check m → Check m

  -- match s (down x ⇒ e')
  -- s produces a bound var checkable
  | matchDown : Synth m → Var → Check m → Check m

  | embed : Synth m → Check m

inductive Synth (m : Type) : Type where
  -- x
  | var : Var → Synth m

  -- s e
  | app : Synth m → Check m → Synth m
  
  -- s.first
  | first : Synth m → Synth m

  -- s.second
  | second : Synth m → Synth m

  -- force s (lazy eval)
  | force : Synth m → Synth m

  -- (e : Aₘ)
  | ann : Check m → m → Synth m

end

end Adjoint
