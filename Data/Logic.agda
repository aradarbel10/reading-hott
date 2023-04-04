module Data.Logic where

data ⊥ : Set where

infix 15 ¬_
¬_ : Set → Set
¬ A = A → ⊥