open import Category

module Category.Morphism {o h} (𝒞 : Category o h) where

open import Cubical.Core.Everything
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

open import Category.Concrete
open import Functor

open import LevelUtil

open Category.Category 𝒞

private
  variable A B : Ob    

mono : Hom A B → Type (o ⊔ h)
mono {A = A} f = ∀ C (g h : Hom C A) → f ∘ g ≡ f ∘ h → g ≡ h

epi : Hom A B → Type (o ⊔ h)
epi {B = B} f = ∀ C (g h : Hom B C) → g ∘ f ≡ h ∘ f → g ≡ h
