module Category.Zero where

open import Cubical.Core.Everything
open import Cubical.Foundations.Prelude
open import Cubical.Data.Empty renaming (rec to ⊥-rec)

open import Category

zero : Category ℓ-zero ℓ-zero
zero = record
         { Ob = ⊥
         ; Hom = λ _ _ → ⊥
         ; isSetHom = λ {A} → ⊥-rec A
         ; id = λ {A} → ⊥-rec A
         ; _∘_ = λ x _ → ⊥-rec x
         ; identˡ = λ {A} → ⊥-rec A
         ; identʳ = λ {A} → ⊥-rec A
         ; ident² = λ {A} → ⊥-rec A
         ; assoc = λ {A} → ⊥-rec A
         }
