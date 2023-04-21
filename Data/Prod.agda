module Data.Prod where

infixr 20 _,_
record Σ (A : Set) (B : A → Set) : Set where
  constructor _,_
  field
    proj₁ : A
    proj₂ : B proj₁
open Σ public

syntax Σ A (λ x → B) = Σ[ x ∈ A ] B

_×_ : ∀ (A B : Set) → Set
A × B = Σ[ x ∈ A ] B