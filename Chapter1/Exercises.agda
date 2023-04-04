module Chapter1.Exercises where

open import Data.Data

--- ex 1.11 ---
DNI : ∀{A : Set} → A → ¬ ¬ A
DNI a ¬a = ¬a a

ex1-11 : ∀{A : Set} → ¬ ¬ ¬ A → ¬ A
ex1-11 ¬¬¬a a = ¬¬¬a (DNI a)

--- ex 1.13 ---
ex1-13 : ∀{P : Set} →
  ¬ (¬ (P + (¬ P)))
ex1-13 e =
  let (¬p , ¬¬p) = lemma e in
  ¬¬p ¬p
  
  where
  lemma : ∀{A B} →
    ¬ (A + B) → ((¬ A) × (¬ B))
  lemma f = ((λ a → f (inl a)) , λ b → f (inr b))


ex1-13′ : ∀{P : Set} →
  ¬ (¬ (P + (¬ P)))
ex1-13′ f = f (inr (λ x → f (inl x)))