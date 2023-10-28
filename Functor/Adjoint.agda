module Functor.Adjoint where

open import Cubical.Core.Everything
open import Cubical.Foundations.Prelude

open import Category
open import Functor
open import NaturalTransformation

open import LevelUtil

private variable
  o h o′ h′ : Level
  𝒞 𝒟 : Category o h

record isLeftAdjoint {𝒞 : Category o h} {𝒟 : Category o′ h′} (F : Functor 𝒞 𝒟) : Type (o ⊔ h ⊔ o′ ⊔ h′) where
  private
    module 𝒞 = Category.Category 𝒞
    module 𝒟 = Category.Category 𝒟
    module F = Functor.Functor F

  field
    G : Functor 𝒟 𝒞
    η : NaturalTransformation idFunctor (G ∘F F)
    ϵ : NaturalTransformation (F ∘F G) idFunctor

  module G = Functor.Functor G
  module η = NaturalTransformation.NaturalTransformation η
  module ϵ = NaturalTransformation.NaturalTransformation ϵ

  field
    zigzag1 : ∀ (A : 𝒞.Ob) → ϵ.component (F.₀ A) 𝒟.∘ F.₁ (η.component A) ≡ 𝒟.id
    zigzag2 : ∀ (B : 𝒟.Ob) → G.₁ (ϵ.component B) 𝒞.∘ η.component (G.₀ B) ≡ 𝒞.id
