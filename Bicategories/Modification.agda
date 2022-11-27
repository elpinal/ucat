module Bicategories.Modification where

open import Cubical.Core.Everything
open import Cubical.Foundations.Prelude

open import Bicategories.Bicategory
open import Bicategories.LaxFunctor
open import Bicategories.LaxTransformation

open import LevelUtil

private
  variable
    o c d : Level
    𝔹 ℂ : Bicategory o c d

record Modification {F G : LaxFunctor 𝔹 ℂ} (α β : LaxTransformation F G) : Type (levelOfTerm 𝔹 ⊔ levelOfTerm ℂ) where
  private
    module 𝔹 = Bicategory 𝔹
    module ℂ = Bicategory ℂ
    module F = LaxFunctor F
    module G = LaxFunctor G
    module α = LaxTransformation α
    module β = LaxTransformation β

  field
    component : ∀ A → ℂ.2Cell (α.component A) (β.component A)

    square-filler·◃component : ∀ {A B} (f : 𝔹.1Cell A B)
      → Path (ℂ.2Cell (G.₁ f ℂ.∘₁ α.component A) (β.component B ℂ.∘₁ F.₁ f))
        (β.square-filler f ℂ.· (G.₁ f ℂ.◃ component A))
        ((component B ℂ.▹ F.₁ f) ℂ.· α.square-filler f)
