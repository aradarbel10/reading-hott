module Data.Logic where

open import Data.Sum
open import Data.Prod

data ⊥ : Set where

infix 15 ¬_
¬_ : Set → Set
¬ A = A → ⊥

distr-¬-over-+ : ∀{A B} →
  ¬ (A + B) → ((¬ A) × (¬ B))
distr-¬-over-+ f = ((λ a → f (inl a)) , λ b → f (inr b))