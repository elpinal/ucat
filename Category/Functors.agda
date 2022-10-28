open import Category

module Category.Functors {o h} (𝒞 : Category o h) {o′ h′} (𝒟 : Category o′ h′) where

open import Cubical.Core.Everything
open import Cubical.Foundations.Prelude

open import Functor
open import NaturalTransformation

Functors : Category (ℓ-max (ℓ-max (ℓ-max o h) o′) h′) (ℓ-max (ℓ-max o h) h′)
Functors = record
             { Ob = Functor 𝒞 𝒟
             ; Hom = NaturalTransformation
             ; isSetHom = isSetNaturalTransformation
             ; id = idNatTrans
             ; _∘_ = vertComp
             ; identˡ = vertCompIdentˡ
             ; identʳ = vertCompIdentʳ
             ; assoc = λ where {f = α} {g = β} {h = γ} → vertCompAssoc {α = α} {β = β} {γ = γ}
             }
