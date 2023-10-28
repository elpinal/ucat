module Functor.Concrete where

open import Cubical.Core.Everything
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

open import Category
open import Category.Concrete
open import Functor

open import LevelUtil

private
  variable
    o h o₁ h₁ o₂ h₂ : Level
    𝒞 : Category o h

record ConcreteFunctor {𝒞 : Category o h} (isS : isStrictCategory 𝒞) (𝒟₁ : ConcreteCategory 𝒞 o₁ h₁) (𝒟₂ : ConcreteCategory 𝒞 o₂ h₂) : Type (o ⊔ h ⊔ o₁ ⊔ h₁ ⊔ o₂ ⊔ h₂) where
  private
    module 𝒟₁ = ConcreteCategory 𝒟₁
    module 𝒟₂ = ConcreteCategory 𝒟₂

  field
    F : Functor 𝒟₁.𝒟 𝒟₂.𝒟

    -- This is a proposition because 𝒞 is a strict category.
    commute : 𝒟₁.U .fst ≡ 𝒟₂.U .fst ∘F F
