module Chapter2.Exercises where

open import Data.Prod
open import Data.Sum
open import Data.Eq
open import Data.Function

postulate funext : {A B : Set} {f g : A → B} → (∀(x) → f x ≡ g x) → f ≡ g

variable
  A : Set
  B : Set
  X : Set

ex1-9 : (A + B → X) ≃ (A → X) × (B → X)
ex1-9 = fwd , bwd , fwd-bwd , bwd-fwd
  where
  fwd : (A + B → X) → (A → X) × (B → X)
  fwd h = (h ∘ inl) , (h ∘ inr)

  bwd : (A → X) × (B → X) → (A + B → X)
  bwd (f , g) (inl a) = f a
  bwd (f , g) (inr b) = g b

  fwd-bwd : fwd ∘ bwd ~ id
  fwd-bwd (f , g) = refl

  pointwise : ∀{h} (x) → bwd ((h ∘ inl) , (h ∘ inr)) x ≡ h x
  pointwise (inl a) = refl
  pointwise (inr b) = refl

  bwd-fwd : bwd ∘ fwd ~ id
  bwd-fwd h =
    begin
      bwd (fwd h)
    ≡[ refl ]
      bwd ((h ∘ inl) , (h ∘ inr))
    ≡[ funext pointwise ]
      h
    ∎