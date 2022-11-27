module Bicategories.Pseudotransformation where

open import Cubical.Core.Everything
open import Cubical.Foundations.Prelude

open import Bicategories.Bicategory
open import Bicategories.LaxFunctor
open import Bicategories.LaxTransformation

open import LevelUtil

private
  variable
    o c d : Level
    𝔹 ℂ : Bicategory o c d

record Pseudotransformation (F G : LaxFunctor 𝔹 ℂ) : Type (levelOfTerm 𝔹 ⊔ levelOfTerm ℂ) where
  private
    module 𝔹 = Bicategory 𝔹
    module ℂ = Bicategory ℂ
    module F = LaxFunctor F
    module G = LaxFunctor G

  field
    lax-transformation : LaxTransformation F G

  open LaxTransformation lax-transformation public

  field
    is-inv-square-filler : ∀ {A B} (f : 𝔹.1Cell A B) → isInv ℂ (square-filler f)
