module Fibration where

open import Cubical.Core.Everything
open import Cubical.Foundations.Prelude

open import Category
open import Displayed

module _ {o h} (𝒞 : Category o h) {o₁ h₁} (𝒟 : Displayed 𝒞 o₁ h₁) where
  private module 𝒟 = Displayed.Displayed 𝒟

  record isCartesian′ {A B} {f : 𝒞 [ A , B ]} {X Y} (f′ : 𝒟.Hom f X Y) {C} (g : 𝒞 [ C , A ]) {Z : 𝒟.Ob C} (h′ : 𝒟.Hom (𝒞 [ f ∘ g ]) Z Y) : Type h₁ where
    field
      g′ : 𝒟.Hom g Z X
      factorize : f′ 𝒟.∘ g′ ≡ h′
      unique : ∀ g″ → f′ 𝒟.∘ g″ ≡ h′ → g′ ≡ g″

  record isCartesian {A B} {f : 𝒞 [ A , B ]} {X Y} (f′ : 𝒟.Hom f X Y) : Type (ℓ-max o (ℓ-max h (ℓ-max o₁ h₁))) where
    field
      prf : ∀ {C} (g : 𝒞 [ C , A ]) {Z : 𝒟.Ob C} (h′ : 𝒟.Hom (𝒞 [ f ∘ g ]) Z Y) → isCartesian′ f′ g h′

  record cartesianLift {A B} (f : 𝒞 [ A , B ]) (Y : 𝒟.Ob B) : Type (ℓ-max o (ℓ-max h (ℓ-max o₁ h₁))) where
    field
      X : 𝒟.Ob A
      f′ : 𝒟.Hom f X Y
      is-cartesian : isCartesian f′

  record Fibration : Type (ℓ-max o (ℓ-max h (ℓ-max o₁ h₁))) where
    field
      prf : ∀ {A B} (f : 𝒞 [ A , B ]) (Y : 𝒟.Ob B) → cartesianLift f Y
