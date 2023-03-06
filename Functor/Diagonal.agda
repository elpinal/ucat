module Functor.Diagonal where

open import Cubical.Core.Everything
open import Cubical.Foundations.Prelude

open import Category
open import Functor

private variable o h o′ h′ : Level

module _ (𝒞 : Category o h) (𝒟 : Category o′ h′) where
  private
    module 𝒞 = Category.Category 𝒞
    module 𝒟 = Category.Category 𝒟

  -- The constant functor.
  Δ : 𝒟.Ob → Functor 𝒞 𝒟
  Δ X = record
    { F₀ = λ _ → X
    ; F₁ = λ _ → 𝒟.id {X}
    ; identity = refl
    ; compose = sym 𝒟.ident²
    }

module _ (𝒞 : Category o h) (𝒟 : Category o′ h′) where
  private
    module 𝒞 = Category.Category 𝒞
    module 𝒟 = Category.Category 𝒟

  _ : ∀ {X : 𝒟.Ob} → oppositeF (Δ (opposite 𝒞) (opposite 𝒟) X) ≡ Δ 𝒞 𝒟 X
  _ = refl
