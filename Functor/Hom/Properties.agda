open import Category

module Functor.Hom.Properties {o h} (𝒞 : Category o h) where

open import Cubical.Core.Everything
open import Cubical.Foundations.Prelude

open import Category.Sets
open import Category.Functors
open import Functor
import Functor.Hom
open import NaturalTransformation

module Hom1 = Functor.Hom 𝒞
module Hom2 = Functor.Hom (opposite 𝒞)

-- Every covariant hom-functor is the dual of a contravariant hom-functor.
_ : ∀ {a} → Hom1.Hom[ a ,-] ≡ Hom2.Hom[-, a ]
_ = refl

_ : Hom1.よ ≡ Hom2.ヨ
_ = refl
