module Data.Data where

data ⊥ : Set where

¬_ : Set → Set
¬ A = A → ⊥

infix 15 ¬_
infixl 16 _×_
record _×_ (A B : Set) : Set where
  constructor _,_
  field
    proj₁ : A
    proj₂ : B

data _+_ : Set → Set → Set where
  inl : ∀{A B} → A → A + B
  inr : ∀{A B} → B → A + B