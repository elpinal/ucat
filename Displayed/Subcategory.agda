module Displayed.Subcategory where

open import Cubical.Core.Everything
open import Cubical.Foundations.Prelude
open import Cubical.Data.Unit

open import Category
open import Displayed

private
  variable
    o h β : Level
    π : Category o h

dispFullSubcat : (Category.Ob π β Type β) β Displayed π β β-zero
dispFullSubcat {π = π} P = record
             { Ob = P
             ; Hom = Ξ» _ _ _ β Unit
             ; isSetHom = isSetUnit
             ; id = tt
             ; _β_ = Ξ» _ _ β tt
             ; identΛ‘ = refl
             ; identΚ³ = refl
             ; assoc = refl
             }

fullSubcat : (Category.Ob π β Type β) β Category _ _
fullSubcat {π = π} P = β« {π = π} (dispFullSubcat P)
