module Chapter2.CoprodEq where

open import Data.Sum
open import Data.Eq
open import Data.Units
open import Data.Function

module _ {A B : Set} where
  code : A + B → A + B → Set
  code (inl a) (inl a′) = a ≡ a′
  code (inr b) (inr b′) = b ≡ b′
  code (inl a) (inr b) = 𝟘
  code (inr b) (inl a) = 𝟘

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

-- as a corollary, we can prove tt ‌/≡ ff
open import Data.Bool

𝟙+𝟙≃𝟚 : 𝟙 + 𝟙 ≃ 𝟚
𝟙+𝟙≃𝟚 = an-equiv f g f∘g g∘f
  where
  f : 𝟙 + 𝟙 → 𝟚
  f (inl ⋆) = tt
  f (inr ⋆) = ff

  g : 𝟚 → 𝟙 + 𝟙
  g tt = inl ⋆
  g ff = inr ⋆

  f∘g : f ∘ g ~ id
  f∘g tt = refl
  f∘g ff = refl

  g∘f : g ∘ f ~ id
  g∘f (inl ⋆) = refl
  g∘f (inr ⋆) = refl

tt/≡ff : ¬ (tt ≡ ff)
tt/≡ff tt≡ff =
  let inl≡inr = ap (𝟙+𝟙≃𝟚 ._≃_.fwd-is-equiv .is-equiv.bwd) tt≡ff in
  let code-inl-inr = (code-faithful (inl ⋆) (inr ⋆)) ._≃_.fwd-is-equiv .is-equiv.bwd inl≡inr in
  code-inl-inr