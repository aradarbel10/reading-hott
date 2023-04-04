module Data.Sum where

data _+_ : Set → Set → Set where
  inl : ∀{A B} → A → A + B
  inr : ∀{A B} → B → A + B

rec-+ : {A B C : Set} → (A → C) → (B → C) → A + B → C
rec-+ lcase rcase (inl x) = lcase x
rec-+ lcase rcase (inr x) = rcase x