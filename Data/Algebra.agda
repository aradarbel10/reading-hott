module Data.Algebra where

open import Data.Eq

record Pointed (A : Set) : Set where
  field
    𝟎 : A
open Pointed {{...}} public

record Magma (A : Set) : Set where
  field
    _⊙_ : A → A → A
open Magma {{...}} public

record Semigroup (A : Set) : Set where
  field
    {{magma}} : Magma A
    assoc : ∀(x y z : A) → (x ⊙ y) ⊙ z ≡ x ⊙ (y ⊙ z)
open Semigroup {{...}} public

record Monoid (A : Set) : Set where
  field
    {{pointed}} : Pointed A
    {{semigroup}} : Semigroup A
    left-unit : ∀(x : A) → 𝟎 ⊙ x ≡ x
    right-unit : ∀(x : A) → x ⊙ 𝟎 ≡ x
open Monoid {{...}} public