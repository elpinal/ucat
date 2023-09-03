module Functor.Presheaf where

open import Cubical.Core.Everything
open import Cubical.Foundations.Prelude

open import Category
open import Category.Sets
open import Functor

open import LevelUtil

private variable o h o′ h′ : Level

Presheaf : Category o h -> (ℓ : Level) -> Type (o ⊔ h ⊔ ℓ-suc ℓ)
Presheaf 𝒞 ℓ = Functor (opposite 𝒞) (Sets ℓ)
