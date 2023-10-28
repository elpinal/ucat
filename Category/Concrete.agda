module Category.Concrete where

open import Cubical.Core.Everything
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

open import Category
open import Functor

open import LevelUtil

private
  variable o h : Level

record ConcreteCategory (𝒞 : Category o h) o′ h′ : Type (o ⊔ h ⊔ ℓ-suc (o′ ⊔ h′)) where
  field
    𝒟 : Category o′ h′
    U : FaithfulFunctor 𝒟 𝒞
