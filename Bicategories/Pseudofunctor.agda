module Bicategories.Pseudofunctor where

open import Cubical.Core.Everything
open import Cubical.Foundations.Prelude

open import Bicategories.Bicategory
open import Bicategories.LaxFunctor

open import LevelUtil

private
  variable o c d oā² cā² dā² : Level

record Pseudofunctor (š¹ : Bicategory o c d) (ā : Bicategory oā² cā² dā²) : Type (levelOfTerm š¹ ā levelOfTerm ā) where
  private
    module š¹ = Bicategory š¹
    module ā = Bicategory ā

  field
    lax-functor : LaxFunctor š¹ ā

  open LaxFunctor lax-functor public

  field
    is-inv-identitor : ā A ā isInv ā (identitor A)
    is-inv-compositor : ā {A B C} (f : š¹.1Cell A B) (g : š¹.1Cell B C) ā isInv ā (compositor f g)
