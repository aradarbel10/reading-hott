module Chapter2.PathInduction where

open import Data.Eq hiding (_⁻¹)

-- refl with an explicit parameter
pattern refl′ x = refl {x = x}

-- path induction
ind-≡ : (A : Set) → (C : ∀(x y : A) (p : x ≡ y) → Set) → (∀(x : A) → C x x (refl′ x))
  → ∀(x y : A) (p : x ≡ y) → C x y p
ind-≡ A C Crefl x x (refl′ x) = Crefl x

-- reversal
_⁻¹ : ∀{A : Set} {x y : A} → x ≡ y → y ≡ x
_⁻¹ {A} {x} {y} p =
  let
    C : ∀(x y : A) (p : x ≡ y) → Set
    C x y _ = y ≡ x

    Crefl : ∀(x : A) → C x x (refl′ x)
    Crefl x = refl′ x
  in
  ind-≡ A C Crefl x y p

-- different ways to define transitivity
trans₁ : ∀(A : Set) (x y z : A) → x ≡ y → y ≡ z → x ≡ z
trans₁ A x y z p =
  let
    C : ∀(x y : A) (p : x ≡ y) → Set
    C x y p = (y ≡ z → x ≡ z)

    Crefl : ∀(x : A) → C x x (refl′ x)
    Crefl x = λ q → q
  in
  ind-≡ A C Crefl x y p

trans₂ : ∀(A : Set) (x y z : A) → x ≡ y → y ≡ z → x ≡ z
trans₂ A x y z p =
  let
    C : ∀(x y : A) (p : x ≡ y) → Set
    C x y p = (y ≡ z → x ≡ z)

    Crefl : ∀(x : A) → C x x (refl′ x)
    Crefl x q =
      let
        D : ∀(y z : A) (q : y ≡ z) → Set
        D x z q = x ≡ z

        Drefl : ∀(y : A) → D y y (refl′ y)
        Drefl x = refl′ x
      in
      ind-≡ A D Drefl x z q
  in
  ind-≡ A C Crefl x y p

trans₁≡trans₂ : ∀(A : Set) (x y z : A) → (p : x ≡ y) → (q : y ≡ z)
  → trans₁ _ _ _ _ p q ≡ trans₂ _ _ _ _ p q
trans₁≡trans₂ A x .x .x refl refl = refl


-- proof with explicit path induction
trans-refl′ : ∀(A : Set) (a b : A) (q : a ≡ b) → q ∙ refl′ b ≡ q
trans-refl′ A a b q =
  let
    C : ∀(x y : A) (p : x ≡ y) → Set
    C x y p = p ∙ refl′ y ≡ p
    
    Crefl : ∀(x : A) → C x x (refl′ x)
    Crefl x = refl′ (refl′ x)
  in
  ind-≡ A C Crefl a b q