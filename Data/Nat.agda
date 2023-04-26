module Data.Nat where

open import Data.Eq
open import Data.Algebra

data ℕ : Set where
    zero : ℕ
    suc : ℕ → ℕ

_+_ : ℕ → ℕ → ℕ
zero + n = n
(suc m) + n = suc (m + n)

zero-+ : ∀ (m : ℕ) → zero + m ≡ m
zero-+ _ = refl

+-zero : ∀ (m : ℕ) → m + zero ≡ m
+-zero zero = refl
+-zero (suc m) = cong suc (+-zero m)

+-suc : ∀ (m n : ℕ) → m + suc n ≡ suc (m + n)
+-suc zero n = refl
+-suc (suc m) n = cong suc (+-suc m n) 

--- ex 1.16 ---
+-comm : ∀ (m n : ℕ) → m + n ≡ n + m
+-comm zero n = sym (+-zero n) 
+-comm (suc m) n = trans (cong suc (+-comm m n)) (sym (+-suc n m))

+-assoc : ∀ (a b c : ℕ) → (a + b) + c ≡ a + (b + c)
+-assoc zero b c = refl
+-assoc (suc a) b c = cong suc (+-assoc a b c)


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