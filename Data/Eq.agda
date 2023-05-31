{-# OPTIONS --type-in-type #-}

module Data.Eq where

open import Data.Prod
open import Data.Function
open import Data.Units

infix 4 _≡_
data _≡_ {A : Set} : A → A → Set where
  refl : {x : A} → x ≡ x


sym : ∀{A : Set} {x y : A} → x ≡ y → y ≡ x
sym refl = refl

_⁻¹ = sym


trans : ∀ {A : Set} {x y z : A} → x ≡ y → y ≡ z → x ≡ z
trans refl refl = refl

infixl 20 _∙_
_∙_ = trans


ap : ∀ {A B : Set} (f : A → B) {x y : A} → x ≡ y → f x ≡ f y
ap f refl = refl

ap2 : ∀ {A B C : Set} → (f : A → B → C) {a₁ a₂ : A} {b₁ b₂ : B} →
  a₁ ≡ a₂ → b₁ ≡ b₂ → f a₁ b₁ ≡ f a₂ b₂
ap2 f refl refl = refl

--- equational reasoning ---
infix 1 begin_
infixr 2 _≡[_]_ _̌≡[_]_ _≡[]_
infix 3 _∎

begin_ : ∀{A : Set} {x y : A} → x ≡ y → x ≡ y
begin p = p

_≡[_]_ : ∀{A : Set} → (x : A) → {y z : A} → x ≡ y → y ≡ z → x ≡ z
x ≡[ p ] q = p ∙ q

_̌≡[_]_ : ∀{A : Set} → (x : A) → {y z : A} → y ≡ x → y ≡ z → x ≡ z
x ̌≡[ p ] q = sym p ∙ q

_≡[]_ : ∀{A : Set} → (x : A) → x ≡ x → x ≡ x
x ≡[] p = x ≡[ refl ] p

_∎ : ∀{A : Set} (x : A) → x ≡ x
x ∎ = refl

--- properties ---
trans-refl : ∀{A : Set} {x y : A} (p : x ≡ y) → p ∙ refl ≡ p
trans-refl refl = refl

refl-trans : ∀{A : Set} {x y : A} (p : x ≡ y) → trans refl p ≡ p
refl-trans refl = refl

trans-sym : ∀{A : Set} {x y : A} (p : x ≡ y) → trans p (sym p) ≡ refl
trans-sym refl = refl

sym-trans : ∀{A : Set} {x y : A} (p : x ≡ y) → trans (sym p) p ≡ refl
sym-trans refl = refl

sym-sym : ∀{A : Set} {x y : A} (p : x ≡ y) → sym (sym p) ≡ p
sym-sym refl = refl

trans-assoc : ∀{A : Set} {w x y z : A} (p : w ≡ x) (q : x ≡ y) (r : y ≡ z)
  → (p ∙ q) ∙ r ≡ p ∙ (q ∙ r)
trans-assoc refl refl refl = refl


--- funext ---
postulate funext : {A B : Set} {f g : A → B} → (∀(x) → f x ≡ g x) → f ≡ g

--- characterization in products ---
eq-, : {A B : Set} {a a′ : A} {b b′ : B} →
  a ≡ a′ → b ≡ b′ → (a , b) ≡ (a′ , b′)
eq-, = ap2 _,_

--- homotopy ---
_~_ : {A B : Set} (f g : A → B) → Set
f ~ g = ∀(x) → f x ≡ g x

--- equivalence ---
record is-equiv {A B : Set} (fwd : A → B) : Set where
  constructor an-is-equiv
  field
    bwd : B → A
    fwd∘bwd : fwd ∘ bwd ~ id
    bwd∘fwd : bwd ∘ fwd ~ id
open is-equiv {{...}} public

infix 18 _≃_
record _≃_ (A B : Set) : Set where
  field
    fwd : A → B
    {{fwd-is-equiv}} : is-equiv fwd

pattern an-equiv f b fb bf = record { fwd = f; fwd-is-equiv = record { bwd = b; bwd∘fwd = bf; fwd∘bwd = fb } }

--- transport ---
transp : ∀{A : Set} {x y : A} (P : A → Set) → x ≡ y → (P x → P y)
transp P refl = id

transp-is-equiv : ∀(A : Set) (x y : A) (P : A → Set) (p : x ≡ y)
  → is-equiv (transp P p)
transp-is-equiv A x x P refl = an-is-equiv id (λ a → refl) (λ a → refl)

--- hsets ---
record is-set (A : Set) : Set where
  field
    uip : ∀(x y : A) (p q : x ≡ y) → p ≡ q
open is-set {{...}} public

is-prop : ∀(A : Set) → Set
is-prop A = ∀(x y : A) → x ≡ y

instance
  𝟙-is-set : is-set 𝟙
  uip ⦃ 𝟙-is-set ⦄ ⋆ ⋆ refl refl = refl

  𝟘-is-set : is-set 𝟘
  uip ⦃ 𝟘-is-set ⦄ x y p q = ex-falso x


record is-1-type (A : Set) : Set where
  field
    path-of-paths : ∀(x y : A) (p q : x ≡ y) (r s : p ≡ q) → r ≡ s
open is-1-type {{...}} public

-- instance
--   set→1-type : ∀{A : Set} {{_ : is-set A}} → is-1-type A
--   path-of-paths ⦃ set→1-type {A} ⦄ x .x refl = _ 