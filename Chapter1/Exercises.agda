module Chapter1.Exercises where

open import Data.Prod
open import Data.Sum
open import Data.Units

--- ex 1.11 ---
DNI : ∀{A : Set} → A → ¬ ¬ A
DNI a ¬a = ¬a a

ex1-11 : ∀{A : Set} → ¬ ¬ ¬ A → ¬ A
ex1-11 ¬¬¬a a = ¬¬¬a (DNI a)

--- ex 1.13 ---
ex1-13 : ∀{P : Set} →
  ¬ (¬ (P + (¬ P)))
ex1-13 e =
  let (¬p , ¬¬p) = distr-¬-over-+ e in
  ¬¬p ¬p

ex1-13′ : ∀{P : Set} →
  ¬ (¬ (P + (¬ P)))
ex1-13′ f = f (inr (λ x → f (inl x)))