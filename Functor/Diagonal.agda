module Functor.Diagonal where

open import Cubical.Core.Everything
open import Cubical.Foundations.Prelude

open import Category
open import Functor

module _ {o h} (π : Category o h) {oβ² hβ²} (π : Category oβ² hβ²) where
  private
    module π = Category.Category π
    module π = Category.Category π

  Ξ : π.Ob β Functor π π
  Ξ X = record
    { Fβ = Ξ» _ β X
    ; Fβ = Ξ» _ β π.id {X}
    ; identity = refl
    ; compose = sym π.identΛ‘
    }
