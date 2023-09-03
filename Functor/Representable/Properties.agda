open import Category

module Functor.Representable.Properties {o h} (𝒞 : Category o h) where

open import Cubical.Core.Everything
open import Cubical.Foundations.Prelude

open import Category.Sets
open import Category.Functors
open import Functor
open import Functor.Hom 𝒞
open import Functor.Representable
open import NaturalTransformation

open import LevelUtil

private
  module 𝒞 = Category.Category 𝒞

thm1 : (F : Functor 𝒞 (Sets h)) → Representation 𝒞 F → Representation′ (opposite 𝒞) F
thm1 F R = record
  { ob = R.ob
  ; iso = record { f = Iso.f R.iso ; is-iso = record { inv = Iso.inv R.iso ; isoˡ = II.isoˡ ; isoʳ = II.isoʳ } }
  }
  where
    module R = Representation R
    module I = Iso R.iso
    module II = isIso I.is-iso

thm2 : (F : Functor 𝒞 (Sets h)) → Representation′ (opposite 𝒞) F → Representation 𝒞 F
thm2 F R = record
  { ob = R.ob
  ; iso = record { f = Iso.f R.iso ; is-iso = record { inv = Iso.inv R.iso ; isoˡ = II.isoˡ ; isoʳ = II.isoʳ } }
  }
  where
    module R = Representation′ R
    module I = Iso R.iso
    module II = isIso I.is-iso

-- It may be possible to prove these are mutual inverses,
-- but `Representation` and `Representation′` are propositions for univalent categories.
