open import Data.Algebra
open import Data.Eq
open import Data.Function using (_∘_)

module Tactics.Semigroups (A : Set) {{is-semigroup : Semigroup A}} where

-- symbolic expressions in a semigroup
data Expr : Set where
  _↑ : A → Expr
  _‵⊙_ : Expr → Expr → Expr

embed : Expr → A
embed (x ↑) = x
embed (e₁ ‵⊙ e₂) = embed e₁ ⊙ embed e₂

-- normal forms are nonempty lists of values
data Nf : Set where
  [_] : A → Nf
  _∷_ : A → Nf → Nf

_++_ : Nf → Nf → Nf
[ x ] ++ ys = x ∷ ys
(x ∷ xs) ++ ys = x ∷ (xs ++ ys)

++-assoc : ∀(xs ys zs : Nf) → (xs ++ ys) ++ zs ≡ xs ++ (ys ++ zs)
++-assoc [ x ] ys zs = refl
++-assoc (x ∷ xs) ys zs = cong (x ∷_) (++-assoc xs ys zs)

-- evaluate into a normal form
eval : Expr → Nf
eval (x ↑) = [ x ]
eval (e₁ ‵⊙ e₂) = eval e₁ ++ eval e₂

reflect : Nf → A
reflect [ x ] = x
reflect (x ∷ xs) = x ⊙ reflect xs

nf : Expr → A
nf = reflect ∘ eval

-- property of reflect
reflect-++ : ∀(n₁ n₂ : Nf) → reflect (n₁ ++ n₂) ≡ reflect n₁ ⊙ reflect n₂
reflect-++ [ x ] n = refl
reflect-++ (x ∷ n₁) n₂ = begin
  (x ⊙ (reflect (n₁ ++ n₂)))           ≡[ cong (x ⊙_) (reflect-++ n₁ n₂) ]
  (x ⊙ (reflect n₁ ⊙ reflect n₂))     ≡[ sym (assoc _ _ _) ]
  ((x ⊙ reflect n₁) ⊙ reflect n₂)     ∎

--- soundness of normalization ---
sound : ∀(e : Expr) → nf e ≡ embed e
sound (x ↑) = refl
-- we split on the left expression, because _++_ scrutinizes it
sound ((x ↑) ‵⊙ e) = nf-↑-‵⊙ ∙ ⊙-reflect-eval ∙ sym embed-↑-‵⊙
  where
  nf-↑-‵⊙ : nf ((x ↑) ‵⊙ e) ≡ x ⊙ reflect (eval e)
  nf-↑-‵⊙ = begin
    nf ((x ↑) ‵⊙ e)                 ≡[]
    reflect (eval ((x ↑) ‵⊙ e))     ≡[]
    reflect (eval (x ↑) ++ eval e)  ≡[]
    reflect ([ x ] ++ eval e)       ≡[]
    reflect (x ∷ eval e)            ≡[]
    x ⊙ reflect (eval e)           ∎

  ⊙-reflect-eval : x ⊙ reflect (eval e) ≡ x ⊙ embed e
  ⊙-reflect-eval = cong (x ⊙_) (sound e)

  embed-↑-‵⊙ : embed ((x ↑) ‵⊙ e) ≡ x ⊙ embed e
  embed-↑-‵⊙ = begin
    embed ((x ↑) ‵⊙ e)              ≡[]
    x ⊙ embed e                     ∎
    
sound ((e₁ ‵⊙ e₂) ‵⊙ e₃) = nf-‵⊙ ∙ reflect-eval-⊙ ∙ embed-comm-‵⊙
  where
  nf-‵⊙ : nf ((e₁ ‵⊙ e₂) ‵⊙ e₃) ≡ (reflect (eval e₁) ⊙ reflect (eval e₂)) ⊙ reflect (eval e₃)
  nf-‵⊙ = begin
    nf ((e₁ ‵⊙ e₂) ‵⊙ e₃)
      ≡[ refl ]
    reflect (eval (e₁ ‵⊙ e₂) ++ eval e₃)
      ≡[ refl ]
    reflect ((eval e₁ ++ eval e₂) ++ eval e₃)
      ≡[ cong reflect (++-assoc (eval e₁) (eval e₂) (eval e₃)) ]
    reflect (eval e₁ ++ (eval e₂ ++ eval e₃))
      ≡[ reflect-++ (eval e₁) (eval e₂ ++ eval e₃) ]
    reflect (eval e₁) ⊙ reflect (eval e₂ ++ eval e₃)
      ≡[ cong (_ ⊙_) (reflect-++ (eval e₂) (eval e₃)) ]
    (reflect (eval e₁) ⊙ (reflect (eval e₂) ⊙ reflect (eval e₃)))
      ≡[ sym (assoc _ _ _) ]
    ((reflect (eval e₁) ⊙ reflect (eval e₂)) ⊙ reflect (eval e₃))
      ∎

  reflect-eval-⊙ : (reflect (eval e₁) ⊙ reflect (eval e₂)) ⊙ reflect (eval e₃) ≡ (embed e₁ ⊙ embed e₂) ⊙ embed e₃
  reflect-eval-⊙ = ap2 _⊙_ (ap2 _⊙_ (sound e₁) (sound e₂)) (sound e₃)

  embed-comm-‵⊙ : embed ((e₁ ‵⊙ e₂) ‵⊙ e₃) ≡ (embed e₁ ⊙ embed e₂) ⊙ embed e₃
  embed-comm-‵⊙ = begin
    embed ((e₁ ‵⊙ e₂) ‵⊙ e₃)              ≡[ refl ]
    embed (e₁ ‵⊙ e₂) ⊙ embed e₃          ≡[ refl ]
    (embed e₁ ⊙ embed e₂) ⊙ embed e₃     ∎

--- solver ---
solve : ∀(e₁ e₂ : Expr) → nf e₁ ≡ nf e₂ → embed e₁ ≡ embed e₂
solve e₁ e₂ eq = (sound e₁) ⁻¹ ∙ eq ∙ sound e₂



--- example ---
example : ∀(w x y z : A) → (((w ⊙ x) ⊙ y) ⊙ z) ≡ (w ⊙ (x ⊙ (y ⊙ z)))
example w x y z = solve
  (((((w ↑) ‵⊙ (x ↑)) ‵⊙ (y ↑)) ‵⊙ (z ↑)))
  (((w ↑) ‵⊙ ((x ↑) ‵⊙ ((y ↑) ‵⊙ (z ↑)))))
  refl