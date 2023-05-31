module Chapter2.Exercises where

open import Data.Prod
open import Data.Sum
open import Data.Eq
open import Data.Function

variable
  A A′ : Set
  B B′ : Set
  X : Set

ex2-6 : (x y z : A) (p : x ≡ y) → is-equiv (λ(q : y ≡ z) → trans p q)
ex2-6 x y z p = an-is-equiv (trans (sym p)) pp⁻¹q p⁻¹pq
  where
  pp⁻¹q : ∀(q) → p ∙ (sym p ∙ q) ≡ q
  pp⁻¹q q = begin
    p ∙ (sym p ∙ q)       ≡[ sym (trans-assoc _ _ _) ]
    (p ∙ sym p) ∙ q       ≡[ ap (_∙ q) (trans-sym _) ]
    refl ∙ q              ≡[ refl-trans _ ]
    q                     ∎
  
  p⁻¹pq : ∀(q) → sym p ∙ (p ∙ q) ≡ q
  p⁻¹pq q = begin
    sym p ∙ (p ∙ q)       ≡[ sym (trans-assoc _ _ _) ]
    (sym p ∙ p) ∙ q       ≡[ ap (_∙ q) (sym-trans _) ]
    refl ∙ q              ≡[ refl-trans _ ]
    q                     ∎
  

ex2-9 : (A + B → X) ≃ (A → X) × (B → X)
ex2-9 = an-equiv f b fb bf
  where
  f : (A + B → X) → (A → X) × (B → X)
  f h = (h ∘ inl) , (h ∘ inr)

  b : (A → X) × (B → X) → (A + B → X)
  b (f , g) (inl a) = f a
  b (f , g) (inr b) = g b

  fb : f ∘ b ~ id
  fb (f , g) = refl

  pointwise : ∀{h} (x) → b ((h ∘ inl) , (h ∘ inr)) x ≡ h x
  pointwise (inl a) = refl
  pointwise (inr b) = refl

  bf : b ∘ f ~ id
  bf h =
    begin
      b (f h)
    ≡[ refl ]
      b ((h ∘ inl) , (h ∘ inr))
    ≡[ funext pointwise ]
      h
    ∎


ex2-17-i : (A ≃ A′) → (B ≃ B′) → (A × B) ≃ (A′ × B′)
ex2-17-i {A = A} {A′ = A′} {B = B} {B′ = B′}
  (an-equiv fwdA bwdA fbA bfA) (an-equiv fwdB bwdB fbB bfB) =
    an-equiv f b fb bf
  where
  f : A × B → A′ × B′
  f (a , b) = fwdA a , fwdB b

  b : A′ × B′ → A × B
  b (a′ , b′) = bwdA a′ , bwdB b′

  fb : (x : A′ × B′) → f (b x) ≡ x
  fb (a′ , b′) = eq-, (fbA a′) (fbB b′)

  bf : (x : A × B) → b (f x) ≡ x
  bf (a , b) = eq-, (bfA a) (bfB b)


-- characterizing equalities in Sigma types
Σ-eq : ∀(A : Set) (P : A → Set) (w w′ : Σ[ x ∈ A ] P x)
  → (w ≡ w′) ≃ Σ[ p ∈ proj₁ w ≡ proj₁ w′ ] (transp P p (proj₂ w) ≡ proj₂ w′)
Σ-eq A P w w′ = an-equiv f g f∘g g∘f
  where
  f : (w ≡ w′) → Σ[ p ∈ proj₁ w ≡ proj₁ w′ ] (transp P p (proj₂ w) ≡ proj₂ w′)
  f refl = refl , refl

  g : Σ[ p ∈ proj₁ w ≡ proj₁ w′ ] (transp P p (proj₂ w) ≡ proj₂ w′) → (w ≡ w′)
  g (refl , refl) = refl

  f∘g : f ∘ g ~ id
  f∘g (refl , refl) = refl

  g∘f : g ∘ f ~ id
  g∘f refl = refl