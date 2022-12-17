module Category.Sets where

open import Cubical.Core.Everything
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Structure
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.Equiv
import Cubical.Foundations.Isomorphism as I
open import Cubical.Data.Sigma

open import Category

Sets : (ℓ : Level) → Category (ℓ-suc ℓ) ℓ
Sets ℓ = record
           { Ob = hSet ℓ
           ; Hom = λ A B → typ A → typ B
           ; isSetHom = λ {B = B} → isSetΠ λ x → str B
           ; id = λ x → x
           ; _∘_ = λ g f x → g (f x)
           ; identˡ = refl
           ; identʳ = refl
           ; assoc = refl
           }

-- The univalence axiom implies that `Sets ℓ` is univalent.
