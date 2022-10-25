module Functor.Diagonal where

open import Cubical.Core.Everything
open import Cubical.Foundations.Prelude

open import Category
open import Functor

module _ {o h} (𝒞 : Category o h) {o′ h′} (𝒟 : Category o′ h′) where
  private
    module 𝒞 = Category.Category 𝒞
    module 𝒟 = Category.Category 𝒟

  Δ : 𝒟.Ob → Functor 𝒞 𝒟
  Δ X = record
    { F₀ = λ _ → X
    ; F₁ = λ _ → 𝒟.id {X}
    ; identity = refl
    ; compose = sym 𝒟.identˡ
    }
