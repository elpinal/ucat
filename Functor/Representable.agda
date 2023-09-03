open import Category

module Functor.Representable {o h} (𝒞 : Category o h) where

open import Cubical.Core.Everything
open import Cubical.Foundations.Prelude

open import Category.Sets
open import Category.Functors
open import Functor
open import Functor.Hom 𝒞
open import NaturalTransformation

open import LevelUtil

private
  module 𝒞 = Category.Category 𝒞

record Representation (F : Functor 𝒞 (Sets h)) : Type (o ⊔ h) where
  field
    ob : 𝒞.Ob
    iso : Iso (Functors 𝒞 (Sets h)) F Hom[ ob ,-]

record Representable : Type (o ⊔ ℓ-suc h) where
  field
    F : Functor 𝒞 (Sets h)
    representation : Representation F

record Representation′ (F : Functor (opposite 𝒞) (Sets h)) : Type (o ⊔ h) where
  field
    ob : 𝒞.Ob
    iso : Iso (Functors (opposite 𝒞) (Sets h)) F Hom[-, ob ]

record Representable′ : Type (o ⊔ ℓ-suc h) where
  field
    F : Functor (opposite 𝒞) (Sets h)
    representation : Representation′ F
