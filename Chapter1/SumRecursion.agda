module Chapter1.SumRecursion where

open import Data.Sum

left-assoc : {A B C : Set} → (A + B) + C → A + (B + C)
left-assoc (inl (inl a)) = inl a
left-assoc (inl (inr b)) = inr (inl b)
left-assoc (inr c) = inr (inr c)

left-assoc′ : (A B C : Set) → (A + B) + C → A + (B + C)
left-assoc′ A B C abc =
  let
    Motive : Set
    Motive = A + (B + C)

    when-it's-ab : (A + B) → Motive
    when-it's-ab ab = rec-+ (λ a → inl a) (λ b → inr (inl b)) ab

    when-it's-c : C → Motive
    when-it's-c c = inr (inr c)
  in
  rec-+ when-it's-ab when-it's-c abc