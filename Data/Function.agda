module Data.Function where

_$_ : {A B : Set} → (A → B) → A → B
f $ x = f x

id : {A : Set} → A → A
id a = a

infixl 21 _∘_
_∘_ : {A B C : Set} → (B → C) → (A → B) → (A → C)
f ∘ g = λ x → f (g x)