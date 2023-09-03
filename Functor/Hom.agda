open import Category

module Functor.Hom {o h} (𝒞 : Category o h) where

open import Cubical.Core.Everything
open import Cubical.Foundations.Prelude

open import Category.Sets
open import Category.Functors
open import Functor
open import NaturalTransformation

module 𝒞 = Category.Category 𝒞

private variable
  ℓ : Level
  B C : 𝒞.Ob

Hom[-,_] : 𝒞.Ob → Functor (opposite 𝒞) (Sets h)
Hom[-, B ] = record
  { F₀ = λ A → 𝒞.Hom A B , 𝒞.isSetHom
  ; F₁ = λ f g → 𝒞 [ g ∘ f ]
  ; identity = λ i f → 𝒞.identʳ {f = f} i
  ; compose = λ { {f = f} {g = g} i h → 𝒞.assoc {f = g} {g = f} {h = h} (~ i) }
  }

Hom[_,-] : 𝒞.Ob → Functor 𝒞 (Sets h)
Hom[ A ,-] = record
  { F₀ = λ B → 𝒞.Hom A B , 𝒞.isSetHom
  ; F₁ = λ f g → 𝒞 [ f ∘ g ]
  ; identity = λ i f → 𝒞.identˡ {f = f} i
  ; compose = λ { {f = f} {g = g} i h → 𝒞.assoc {f = h} {g = f} {h = g} i }
  }

Hom₁[-,_] : (f : 𝒞.Hom B C) → NaturalTransformation Hom[-, B ] Hom[-, C ]
Hom₁[-, f ] = record
  { component = λ A g → 𝒞 [ f ∘ g ]
  ; commute = λ A B {f = f′} i g → 𝒞.assoc {f = f′} {g = g} {h = f} (~ i)
  }

Hom₁[_,-] : (f : 𝒞.Hom B C) → NaturalTransformation Hom[ C ,-] Hom[ B ,-]
Hom₁[ f ,-] = record
  { component = λ A g → 𝒞 [ g ∘ f ]
  ; commute = λ A B {f = f′} i g → 𝒞.assoc {f = f} {g = g} {h = f′} i
  }

-- Hom embedding.
よ : Functor 𝒞 (Functors (opposite 𝒞) (Sets h))
よ = record
  { F₀ = λ B → Hom[-, B ]
  ; F₁ = λ f → Hom₁[-, f ]
  ; identity = componentEmbed (Hom₁[-,_] 𝒞.id) _ λ i A f → 𝒞.identˡ {f = f} i
  ; compose = λ { {f = f} {g = g} → componentEmbed (Hom₁[-,_] (𝒞 [ _ ∘ _ ])) _ λ i A h → 𝒞.assoc {f = h} {g = f} {h = g} i }
  }

-- Katakana notation for よ. Not to be confused with existential quantifier!
ヨ : Functor (opposite 𝒞) (Functors 𝒞 (Sets h))
ヨ = record
  { F₀ = λ A → Hom[ A ,-]
  ; F₁ = λ f → Hom₁[ f ,-]
  ; identity = componentEmbed Hom₁[ 𝒞.id ,-] _ λ i A f → 𝒞.identʳ {f = f} i
  ; compose = λ { {f = f} {g = g} → componentEmbed Hom₁[ (𝒞 [ _ ∘ _ ]) ,-] _ (λ i A h → 𝒞.assoc {f = g} {g = f} {h = h} ((~ i)))}
  }
