module Functor where

open import Cubical.Core.Everything
open import Cubical.Foundations.Prelude

open import Category

record Functor {o h} (𝒞 : Category o h) {o′ h′} (𝒟 : Category o′ h′) : Type (ℓ-max o (ℓ-max h (ℓ-max o′ h′))) where
  private
    module 𝒞 = Category.Category 𝒞
    module 𝒟 = Category.Category 𝒟

  field
    F₀ : 𝒞.Ob → 𝒟.Ob
    F₁ : ∀ {A B : 𝒞.Ob} → 𝒞 [ A , B ] → 𝒟 [ F₀ A , F₀ B ]
    identity : ∀ {A : 𝒞.Ob} → F₁ (𝒞.id {A}) ≡ 𝒟.id
    compose : ∀ {A B C : 𝒞.Ob} {f : 𝒞 [ A , B ]} {g : 𝒞 [ B , C ]} → F₁ (𝒞 [ g ∘ f ]) ≡ 𝒟 [ F₁ g ∘ F₁ f ]

  ₀ = F₀
  ₁ = F₁
