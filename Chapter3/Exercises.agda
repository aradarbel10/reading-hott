{-# OPTIONS --type-in-type #-}

module Chapter3.Exercises where

open import Data.Prod
open import Data.Sum
open import Data.Eq
open import Data.Function
open import Data.Units

open import Chapter1.Exercises using (ex1-13)

LEM : Set
LEM = (A : Set) → is-prop A → (A + (¬ A))

¬¬LEM : ¬ ¬ LEM
¬¬LEM ¬LEM = ¬LEM (λ A A-is-prop → inr (λ x → {!   !})) -- f (inr (λ x → f (inl x)))

DNE : Set₁
DNE = ∀(A : Set) → is-prop A → ((¬ ¬ A) → A)

ex3-18a : LEM → DNE
ex3-18a lem A f g = helper (lem A f)
  where
  helper : A + (¬ A) → A
  helper (inl a) = a
  helper (inr b) = ex-falso (g b)

ex3-18b : DNE → LEM
ex3-18b dne A f =
  {! dne LEM f  !}

  -- dne A _    : ¬¬A → A
  -- dne (¬A) _ : ¬¬¬A → ¬A

  where
  lemma : ∀(A : Set) → (¬ A) + (¬ ¬ A)
  lemma A = {!   !}