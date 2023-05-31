module Data.Units where

open import Data.Sum
open import Data.Prod

data 𝟘 : Set where

ex-falso : ∀{A : Set} → 𝟘 → A
ex-falso ()

infix 15 ¬_
¬_ : Set → Set
¬ A = A → 𝟘

distr-¬-over-+ : ∀{A B} →
  ¬ (A + B) → ((¬ A) × (¬ B))
distr-¬-over-+ f = ((λ a → f (inl a)) , λ b → f (inr b))


data 𝟙 : Set where
  ⋆ : 𝟙