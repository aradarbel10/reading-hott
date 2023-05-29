module Data.Nat where

open import Data.Eq
open import Data.Algebra

data ℕ : Set where
    zero : ℕ
    suc : ℕ → ℕ

infixl 15 _+_
_+_ : ℕ → ℕ → ℕ
zero + n = n
(suc m) + n = suc (m + n)

zero-+ : ∀ (m : ℕ) → zero + m ≡ m
zero-+ _ = refl

+-zero : ∀ (m : ℕ) → m + zero ≡ m
+-zero zero = refl
+-zero (suc m) = ap suc (+-zero m)

+-suc : ∀ (m n : ℕ) → m + suc n ≡ suc (m + n)
+-suc zero n = refl
+-suc (suc m) n = ap suc (+-suc m n) 

--- ex 1.16 ---
+-comm : ∀ (m n : ℕ) → m + n ≡ n + m
+-comm zero n = sym (+-zero n) 
+-comm (suc m) n = trans (ap suc (+-comm m n)) (sym (+-suc n m))

+-assoc : ∀ (a b c : ℕ) → (a + b) + c ≡ a + (b + c)
+-assoc zero b c = refl
+-assoc (suc a) b c = ap suc (+-assoc a b c)


-- _+_ forms a monoid
instance
  zero-pointed-ℕ : Pointed ℕ
  zero-pointed-ℕ = record { 𝟎 = zero }

  additive-magma-ℕ : Magma ℕ
  additive-magma-ℕ = record { _⊙_ = _+_ }

  additive-semigroup-ℕ : Semigroup ℕ
  additive-semigroup-ℕ = record { assoc = +-assoc }

  additive-monoid-ℕ : Monoid ℕ
  additive-monoid-ℕ = record { left-unit = zero-+; right-unit = +-zero }


instance
  ℕ-is-set : is-set ℕ
  uip ⦃ ℕ-is-set ⦄ x .x refl refl = refl


--- ex 1.8 ---
infixl 16 _*_
_*_ : ℕ → ℕ → ℕ
zero * n = zero
suc m * n = m * n + n

infixl 17 _^_
_^_ : ℕ → ℕ → ℕ
m ^ zero = suc zero
m ^ suc n = m * m ^ n

*-zero : ∀(x : ℕ) → zero ≡ x * zero
*-zero zero = refl
*-zero (suc x) = ap (_+ zero) (*-zero x)