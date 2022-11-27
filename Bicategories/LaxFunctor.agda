module Bicategories.LaxFunctor where

open import Cubical.Core.Everything
open import Cubical.Foundations.Prelude

open import Bicategories.Bicategory

open import LevelUtil

private
  variable o c d o′ c′ d′ : Level

record LaxFunctor (𝔹 : Bicategory o c d) (ℂ : Bicategory o′ c′ d′) : Type (levelOfTerm 𝔹 ⊔ levelOfTerm ℂ) where
  private
    module 𝔹 = Bicategory 𝔹
    module ℂ = Bicategory ℂ

  field
    F₀ : 𝔹.Ob → ℂ.Ob
    F₁ : ∀ {A B} → 𝔹.1Cell A B → ℂ.1Cell (F₀ A) (F₀ B)
    F₂ : ∀ {A B} {f g : 𝔹.1Cell A B} → 𝔹.2Cell f g → ℂ.2Cell (F₁ f) (F₁ g)

    identitor : ∀ A → ℂ.2Cell (ℂ.id₁ {A = F₀ A}) (F₁ 𝔹.id₁)
    compositor : ∀ {A B C} (f : 𝔹.1Cell A B) (g : 𝔹.1Cell B C) → ℂ.2Cell (F₁ g ℂ.∘₁ F₁ f) (F₁ (g 𝔹.∘₁ f))

    identity : ∀ {A B} (f : 𝔹.1Cell A B) → F₂ (𝔹.id₂ {f = f}) ≡ ℂ.id₂
    compose : ∀ {A B} {f g h : 𝔹.1Cell A B} (θ : 𝔹.2Cell f g) (γ : 𝔹.2Cell g h) → F₂ (γ 𝔹.· θ) ≡ F₂ γ ℂ.· F₂ θ

  ₀ = F₀
  ₁ = F₁
  ₂ = F₂

  field
    compositor·▹ : ∀ {A B C} (f : 𝔹.1Cell A B) {g₁ g₂ : 𝔹.1Cell B C} (θ : 𝔹.2Cell g₁ g₂)
      → compositor f g₂ ℂ.· (F₂ θ ℂ.▹ F₁ f) ≡ (F₂ (θ 𝔹.▹ f) ℂ.· compositor f g₁)
    compositor·◃ : ∀ {A B C} (f₁ f₂ : 𝔹.1Cell A B) {g : 𝔹.1Cell B C} (θ : 𝔹.2Cell f₁ f₂)
      → compositor f₂ g ℂ.· (F₁ g ℂ.◃ F₂ θ) ≡ (F₂ (g 𝔹.◃ θ) ℂ.· compositor f₁ g)
    unitorʳ·compositor·identitor : ∀ {A B} (f : 𝔹.1Cell A B)
      → (F₂ (𝔹.unitorʳ _) ℂ.· compositor 𝔹.id₁ f) ℂ.· (F₁ f ℂ.◃ identitor _) ≡ ℂ.unitorʳ (F₁ f)
    unitorˡ·compositor·identitor : ∀ {A B} (f : 𝔹.1Cell A B)
      → (F₂ (𝔹.unitorˡ _) ℂ.· compositor f 𝔹.id₁) ℂ.· (identitor _ ℂ.▹ F₁ f) ≡ ℂ.unitorˡ (F₁ f)
    associator·compositor·compositor : ∀ {A B C D} (f : 𝔹.1Cell A B) {g : 𝔹.1Cell B C} {h : 𝔹.1Cell C D}
      → (F₂ (𝔹.associator f g h) ℂ.· compositor f (h 𝔹.∘₁ g)) ℂ.· (compositor g h ℂ.▹ F₁ f)
      ≡ (compositor (g 𝔹.∘₁ f) h ℂ.· (F₁ h ℂ.◃ compositor f g)) ℂ.· ℂ.associator (F₁ f) (F₁ g) (F₁ h)
