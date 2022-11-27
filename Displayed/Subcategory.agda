module Displayed.Subcategory where

open import Cubical.Core.Everything
open import Cubical.Foundations.Prelude
open import Cubical.Data.Unit

open import Category
open import Displayed

private
  variable
    o h ℓ : Level
    𝒞 : Category o h

dispFullSubcat : (Category.Ob 𝒞 → Type ℓ) → Displayed 𝒞 ℓ ℓ-zero
dispFullSubcat {𝒞 = 𝒞} P = record
             { Ob = P
             ; Hom = λ _ _ _ → Unit
             ; isSetHom = isSetUnit
             ; id = tt
             ; _∘_ = λ _ _ → tt
             ; identˡ = refl
             ; identʳ = refl
             ; assoc = refl
             }

fullSubcat : (Category.Ob 𝒞 → Type ℓ) → Category _ _
fullSubcat {𝒞 = 𝒞} P = ∫ {𝒞 = 𝒞} (dispFullSubcat P)
