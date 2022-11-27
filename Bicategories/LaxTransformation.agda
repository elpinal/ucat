module Bicategories.LaxTransformation where

open import Cubical.Core.Everything
open import Cubical.Foundations.Prelude

open import Bicategories.Bicategory
open import Bicategories.LaxFunctor

open import LevelUtil

private
  variable
    o c d : Level
    𝔹 ℂ : Bicategory o c d

record LaxTransformation (F G : LaxFunctor 𝔹 ℂ) : Type (levelOfTerm 𝔹 ⊔ levelOfTerm ℂ) where
  private
    module 𝔹 = Bicategory 𝔹
    module ℂ = Bicategory ℂ
    module F = LaxFunctor F
    module G = LaxFunctor G

  field
    component : ∀ A → ℂ.1Cell (F.₀ A) (G.₀ A)
    square-filler : ∀ {A B} (f : 𝔹.1Cell A B) → ℂ.2Cell (G.₁ f ℂ.∘₁ component A) (component B ℂ.∘₁ F.₁ f)

    square-filler·identitor▹component : ∀ {A}
      → square-filler (𝔹.id₁ {A = A}) ℂ.· (G.identitor A ℂ.▹ component A)
      ≡ (component A ℂ.◃ F.identitor A) ℂ.· ℂ.unitorʳ⁻¹ (component A) ℂ.· (ℂ.unitorˡ (component A))

    square-filler·compositor▹component : ∀ {A B C} (f : 𝔹.1Cell A B) (g : 𝔹.1Cell B C)
      → Path (ℂ.2Cell ((G.₁ g ℂ.∘₁ G.₁ f) ℂ.∘₁ component A) (component C ℂ.∘₁ (F.₁ (g 𝔹.∘₁ f))))
        (square-filler (g 𝔹.∘₁ f) ℂ.· (G.compositor f g ℂ.▹ component A))
        ((component C ℂ.◃ F.compositor f g) ℂ.· ℂ.associator (F.₁ f) (F.₁ g) (component C) ℂ.· (square-filler g ℂ.▹ F.₁ f) ℂ.· ℂ.associator⁻¹ (F.₁ f) (component B) (G.₁ g) ℂ.· (G.₁ g ℂ.◃ square-filler f) ℂ.· ℂ.associator (component A) (G.₁ f) (G.₁ g))
