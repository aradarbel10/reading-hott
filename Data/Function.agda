module Data.Function where

id : {A : Set} → A → A
id a = a

infixl 21 _∘_
_∘_ : {A B C : Set} → (B → C) → (A → B) → (A → C)
f ∘ g = λ x → f (g x)