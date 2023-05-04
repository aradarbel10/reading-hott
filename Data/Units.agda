module Data.Units where

open import Data.Sum
open import Data.Prod

data ⊥ : Set where

ex-falso : ∀{A : Set} → ⊥ → A
ex-falso ()

infix 15 ¬_
¬_ : Set → Set
¬ A = A → ⊥

distr-¬-over-+ : ∀{A B} →
  ¬ (A + B) → ((¬ A) × (¬ B))
distr-¬-over-+ f = ((λ a → f (inl a)) , λ b → f (inr b))


data ⊤ : Set where
  ⋆ : ⊤