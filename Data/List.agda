module Data.List where

open import Data.Function
open import Data.Eq

data List (A : Set) : Set where
  [] : List A
  _∷_ : A → List A → List A

map : ∀{A B} → (A → B) → List A → List B
map f [] = []
map f (x ∷ xs) = f x ∷ map f xs
