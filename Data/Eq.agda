module Data.Eq where

open import Data.Prod
open import Data.Function

infix 4 _≡_
data _≡_ {A : Set} (x : A) : A → Set where
    refl : x ≡ x

sym : ∀ {A : Set} {x y : A} → x ≡ y → y ≡ x
sym refl = refl

trans : ∀ {A : Set} {x y z : A} → x ≡ y → y ≡ z → x ≡ z
trans refl refl = refl

infixl 20 _∙_
_∙_ = trans

cong : ∀ {A B : Set} (f : A → B) {x y : A} → x ≡ y → f x ≡ f y
cong f refl = refl

--- equational reasoning ---
infix 1 begin_
infixr 2 _≡[_]_ _≡[]_
infix 3 _∎

begin_ : ∀{A : Set} {x y : A} → x ≡ y → x ≡ y
begin p = p

_≡[_]_ : ∀{A : Set} → (x : A) → {y z : A} → x ≡ y → y ≡ z → x ≡ z
x ≡[ p ] q = p ∙ q

_≡[]_ : ∀{A : Set} → (x : A) → x ≡ x → x ≡ x
x ≡[] p = p

_∎ : ∀{A : Set} (x : A) → x ≡ x
x ∎ = refl

--- properties ---
trans-refl : ∀{A : Set} {x y : A} (p : x ≡ y) → trans p refl ≡ p
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

--- whiskering ---
infixl 17 _∙r_
infixl 17 _∙l_
infixl 18 _∗_

_∙r_ : ∀{A : Set} {x y z : A} {p q : x ≡ y} (α : p ≡ q) (r : y ≡ z) → p ∙ r ≡ q ∙ r
_∙r_ {p = p} {q = q} α refl = trans-refl p ∙ α ∙ sym (trans-refl q)

_∙l_ : ∀{A : Set} {x y z : A} (p : x ≡ y) {r s : y ≡ z} (β : r ≡ s) → p ∙ r ≡ p ∙ s
_∙l_ refl {r = r} {s = s} β = refl-trans r ∙ β ∙ sym (refl-trans s)

_∗_ : ∀{A : Set} {x y z : A} {p q : x ≡ y} {r s : y ≡ z} (α : p ≡ q) (β : r ≡ s) → p ∙ r ≡ q ∙ s
_∗_ {q = q} {r = r} α β = (α ∙r r) ∙ (q ∙l β)


--- homotopy ---
_~_ : {A B : Set} (f g : A → B) → Set
f ~ g = ∀(x) → f x ≡ g x

--- equivalence ---
is-equiv : {A B : Set} → (f : A → B) → Set
is-equiv {A} {B} f = Σ[ g ∈ (B → A) ] ((f ∘ g ~ id) × (g ∘ f ~ id))

infix 18 _≃_
_≃_ : (A B : Set) → Set
A ≃ B = Σ[ f ∈ (A → B) ] (is-equiv f) 