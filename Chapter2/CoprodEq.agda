module Chapter2.CoprodEq where

open import Data.Sum
open import Data.Eq
open import Data.Units
open import Data.Function

module _ {A B : Set} where
  code : A + B → A + B → Set
  code (inl a) (inl a′) = a ≡ a′
  code (inr b) (inr b′) = b ≡ b′
  code (inl a) (inr b) = ⊥
  code (inr b) (inl a) = ⊥

  code-faithful : ∀(w w′ : A + B) → code w w′ ≃ (w ≡ w′)
  code-faithful w w′ = an-equiv (decode w w′) (encode w w′) (f∘g w w′) (g∘f w w′)
    where
    decode : ∀(w w′ : A + B) → code w w′ → (w ≡ w′)
    decode (inl a) (inl a′) = ap inl
    decode (inr b) (inr b′) = ap inr

    encode : ∀(w w′ : A + B) → (w ≡ w′) → code w w′
    encode (inl a) (inl a) refl = refl
    encode (inr b) (inr b) refl = refl

    f∘g : ∀(w w′ : A + B) → decode w w′ ∘ encode w w′ ~ id
    f∘g (inl a) (inl a) refl = refl
    f∘g (inr b) (inr b) refl = refl

    g∘f : ∀(w w′ : A + B) → encode w w′ ∘ decode w w′ ~ id
    g∘f (inl a) (inl a) refl = refl
    g∘f (inr b) (inr b) refl = refl