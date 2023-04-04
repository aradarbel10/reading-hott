module Data.Nat where

open import Data.Eq

data ℕ : Set where
    zero : ℕ
    suc : ℕ → ℕ

_+_ : ℕ → ℕ → ℕ
zero + n = n
(suc m) + n = suc (m + n)

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