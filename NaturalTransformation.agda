module NaturalTransformation where

open import Cubical.Core.Everything
open import Cubical.Foundations.Prelude

open import Category
open import Functor

module _ {o h} (𝒞 : Category o h) {o′ h′} (𝒟 : Category o′ h′) where
  private
    module 𝒞 = Category.Category 𝒞
    module 𝒟 = Category.Category 𝒟

  record NaturalTransformation (F G : Functor 𝒞 𝒟) : Type (ℓ-max o (ℓ-max h (ℓ-max o′ h′))) where
    private
      module F = Functor.Functor F
      module G = Functor.Functor G

    field
      component : ∀ {A : 𝒞.Ob} → 𝒟 [ F.₀ A , G.₀ A ]
      commute : ∀ {A B : 𝒞.Ob} {f : 𝒞 [ A , B ]} → 𝒟 [ component {B} ∘ F.₁ f ] ≡ 𝒟 [ G.₁ f ∘ component {A} ]
