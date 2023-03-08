module Category.One where

open import Cubical.Core.Everything
open import Cubical.Foundations.Prelude
open import Cubical.Data.Unit

open import Category

one : Category ℓ-zero ℓ-zero
one = record
        { Ob = Unit
        ; Hom = λ _ _ → Unit
        ; isSetHom = isSetUnit
        ; id = tt
        ; _∘_ = λ _ _ → tt
        ; identˡ = refl
        ; identʳ = refl
        ; ident² = refl
        ; assoc = refl
        }
