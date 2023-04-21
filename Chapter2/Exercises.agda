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

ex2-6 : (x y z : A) (p : x ≡ y) → is-equiv (λ(q : y ≡ z) → trans p q)
ex2-6 x y z p = trans (sym p) , pp⁻¹q , p⁻¹pq
  where
  pp⁻¹q : ∀(q) → p ∙ (sym p ∙ q) ≡ q
  pp⁻¹q q = begin
    p ∙ (sym p ∙ q)       ≡[ sym (trans-assoc _ _ _) ]
    (p ∙ sym p) ∙ q       ≡[ cong (_∙ q) (trans-sym _) ]
    refl ∙ q              ≡[ refl-trans _ ]
    q                     ∎
  
  p⁻¹pq : ∀(q) → sym p ∙ (p ∙ q) ≡ q
  p⁻¹pq q = begin
    sym p ∙ (p ∙ q)       ≡[ sym (trans-assoc _ _ _) ]
    (sym p ∙ p) ∙ q       ≡[ cong (_∙ q) (sym-trans _) ]
    refl ∙ q              ≡[ refl-trans _ ]
    q                     ∎

  

ex2-9 : (A + B → X) ≃ (A → X) × (B → X)
ex2-9 = fwd , bwd , fwd-bwd , bwd-fwd
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