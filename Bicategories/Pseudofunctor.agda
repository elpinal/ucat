module Bicategories.Pseudofunctor where

open import Cubical.Core.Everything
open import Cubical.Foundations.Prelude

open import Bicategories.Bicategory
open import Bicategories.LaxFunctor

open import LevelUtil

private
  variable o c d o′ c′ d′ : Level

record Pseudofunctor (𝔹 : Bicategory o c d) (ℂ : Bicategory o′ c′ d′) : Type (levelOfTerm 𝔹 ⊔ levelOfTerm ℂ) where
  private
    module 𝔹 = Bicategory 𝔹
    module ℂ = Bicategory ℂ

  field
    lax-functor : LaxFunctor 𝔹 ℂ

  open LaxFunctor lax-functor public

  field
    is-inv-identitor : ∀ A → isInv ℂ (identitor A)
    is-inv-compositor : ∀ {A B C} (f : 𝔹.1Cell A B) (g : 𝔹.1Cell B C) → isInv ℂ (compositor f g)
