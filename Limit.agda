open import Category
open import Cubical.Core.Everything

module Limit {o h o′ h′ : Level} (𝕀 : Category o h) (𝒞 : Category o′ h′) where

open import Cubical.Foundations.Prelude

open import Functor
open import Functor.Diagonal
open import NaturalTransformation

open import LevelUtil

private
  module 𝒞 = Category.Category 𝒞

open 𝒞

Cone⟨_,_⟩ : 𝒞.Ob → Functor 𝕀 𝒞 → Type (o ⊔ h ⊔ h′)
Cone⟨ a , F ⟩ = NaturalTransformation (Δ 𝕀 𝒞 a) F

record Cone (F : Functor 𝕀 𝒞) : Type (o ⊔ h ⊔ o′ ⊔ h′) where
  field
    X : 𝒞.Ob
    proj : Cone⟨ X , F ⟩

module _ {a : 𝒞.Ob} {F : Functor 𝕀 𝒞} where
  precompose : ∀ {x} → 𝒞.Hom x a → Cone⟨ a , F ⟩ → Cone⟨ x , F ⟩
  precompose f α = record { component = λ A → component A 𝒞.∘ f ; commute = λ A B → λ {f = g} →
      (𝒞 [ component B 𝒞.∘ f ∘ 𝒞.id ])
    ≡⟨ 𝒞.identʳ ⟩
      (𝒞 [ component B ∘ f ])
    ≡⟨ cong (𝒞._∘ f) (sym 𝒞.identʳ) ⟩
      (𝒞 [ component B 𝒞.∘ 𝒞.id ∘ f ])
    ≡⟨ cong (𝒞._∘ f) (commute A B) ⟩
      (𝒞 [ Functor.₁ F g 𝒞.∘ component A ∘ f ])
    ≡⟨ 𝒞.assoc ⟩
      (𝒞 [ Functor.₁ F g ∘ component A 𝒞.∘ f ])
    ∎
    }
    where open NaturalTransformation.NaturalTransformation α

  isLimit : Cone⟨ a , F ⟩ → Type (o ⊔ h ⊔ o′ ⊔ h′)
  isLimit α = ∀ (x : 𝒞.Ob) → isEquiv (λ f → precompose {x = x} f α)

record Limit⟨_,_⟩ (a : Ob) (F : Functor 𝕀 𝒞) : Type (o ⊔ h ⊔ o′ ⊔ h′) where
  field
    cone : Cone⟨ a , F ⟩
    is-limit : isLimit cone

record Limit (F : Functor 𝕀 𝒞) : Type (o ⊔ h ⊔ o′ ⊔ h′) where
  field
    X : Ob
    limit : Limit⟨ X , F ⟩
