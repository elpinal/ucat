{- The discrete category with 2 objects. -}
module Category.Two where

open import Cubical.Core.Everything
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.GroupoidLaws
open import Cubical.Data.Bool

open import Category

two : Category ℓ-zero ℓ-zero
two = record
        { Ob = Bool
        ; Hom = λ A B → A ≡ B
        ; isSetHom = isProp→isSet (isSetBool _ _)
        ; id = refl
        ; _∘_ = λ x y → y ∙ x
        ; identˡ = sym (rUnit _)
        ; identʳ = sym (lUnit _)
        ; ident² = sym (rUnit _)
        ; assoc = λ { {f = f} → assoc f _ _ }
        }
