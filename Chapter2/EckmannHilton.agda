module Chapter2.EckmannHilton where

open import Data.Eq

variable
  A : Set
  x y z : A

infixl 17 _∙r_
infixl 17 _∙l_

--- the sandwich lemma ---
refl-sandwich : ∀{A : Set} → {a b : A} → (p : a ≡ b)
  → refl ∙ p ∙ refl ≡ p
refl-sandwich p = trans-refl _ ∙ refl-trans p

--- whiskering ---
_∙r_ : ∀{p q : x ≡ y} (α : p ≡ q) (r : y ≡ z) → p ∙ r ≡ q ∙ r
_∙r_ {p = p} {q = q} α refl = trans-refl p ∙ α ∙ sym (trans-refl q)

_∙l_ : ∀(p : x ≡ y) {r s : y ≡ z} (β : r ≡ s) → p ∙ r ≡ p ∙ s
_∙l_ refl {r = r} {s = s} β = refl-trans r ∙ β ∙ sym (refl-trans s)

-- whiskering an identity 2-path is reflexive
refl∙r : ∀{p : x ≡ y} (q : y ≡ z) → refl {x = p} ∙r q ≡ refl
refl∙r {p = refl} refl = refl

refl∙l : ∀(p : x ≡ y) {q : y ≡ z} → p ∙l refl {x = q} ≡ refl
refl∙l refl {q = refl} = refl

--- horizontal compositions ---
module _ {p q : x ≡ y} {r s : y ≡ z} where
  infixl 18 _∗_ _∗′_

  _∗_ : (α : p ≡ q) (β : r ≡ s) → p ∙ r ≡ q ∙ s
  _∗_ α β = (α ∙r r) ∙ (q ∙l β)

  _∗′_ : (α : p ≡ q) (β : r ≡ s) → p ∙ r ≡ q ∙ s
  _∗′_ α β = (p ∙l β) ∙ (α ∙r s)

-- horizontally composing reflexive 2-paths is reflexive
refl∗refl : ∀(p : x ≡ y) (q : y ≡ z) → refl {x = p} ∗ refl {x = q} ≡ refl {x = p ∙ q}
refl∗refl p q = ap2 _∙_ (refl∙r q) (refl∙l p)

refl∗′refl : ∀(p : x ≡ y) (q : y ≡ z) → refl {x = p} ∗′ refl {x = q} ≡ refl {x = p ∙ q}
refl∗′refl p q = ap2 _∙_ (refl∙l p) (refl∙r q)

-- the two orders of horizontal composition are equal
∗≡∗′ : ∀{p q : x ≡ y} {r s : y ≡ z} → (α : p ≡ q) (β : r ≡ s) → α ∗ β ≡ α ∗′ β
∗≡∗′ refl refl = refl∗refl _ _ ∙ sym (refl∗′refl _ _)

-- horizontally composing loops of refl is the same as composing them
∗-refl-loop≡∙ : ∀(α β : refl {x = x} ≡ refl {x = x}) → α ∗ β ≡ α ∙ β
∗-refl-loop≡∙ α β = begin
  -- unfold definitions
  α ∗ β                       ≡[ refl ]
  (α ∙r refl) ∙ (refl ∙l β)   ≡[ refl ]
  -- cancel all reflexivities
  (refl ∙ α ∙ refl) ∙ (refl ∙ β ∙ refl) ≡[ ap2 _∙_ (refl-sandwich α) (refl-sandwich β) ]
  α ∙ β ∎

∗′-refl-loop≡∙ : ∀(α β : refl {x = x} ≡ refl {x = x}) → α ∗′ β ≡ β ∙ α
∗′-refl-loop≡∙ α β = begin
  -- unfold definitions
  (α ∗′ β)                    ≡[ refl ]
  (refl ∙l β) ∙ (α ∙r refl)   ≡[ refl ]
  -- cancel all reflexivities
  (refl ∙ β ∙ refl) ∙ (refl ∙ α ∙ refl) ≡[ ap2 _∙_ (refl-sandwich β) (refl-sandwich α) ]
  β ∙ α ∎

-- we finally conclude: the second loop space at any point is a commutative group
eckmann-hilton : ∀(α β : refl {x = x} ≡ refl {x = x})
  → α ∙ β ≡ β ∙ α
eckmann-hilton α β = sym (∗-refl-loop≡∙ _ _) ∙ ∗≡∗′ _ _ ∙ ∗′-refl-loop≡∙ _ _