module Bicategories.Modification where

open import Cubical.Core.Everything
open import Cubical.Foundations.Prelude

open import Bicategories.Bicategory
open import Bicategories.LaxFunctor
open import Bicategories.LaxTransformation

open import LevelUtil

private
  variable
    o c d : Level
    ð¹ â : Bicategory o c d

record Modification {F G : LaxFunctor ð¹ â} (Î± Î² : LaxTransformation F G) : Type (levelOfTerm ð¹ â levelOfTerm â) where
  private
    module ð¹ = Bicategory ð¹
    module â = Bicategory â
    module F = LaxFunctor F
    module G = LaxFunctor G
    module Î± = LaxTransformation Î±
    module Î² = LaxTransformation Î²

  field
    component : â A â â.2Cell (Î±.component A) (Î².component A)

    square-fillerÂ·âcomponent : â {A B} (f : ð¹.1Cell A B)
      â Path (â.2Cell (G.â f â.ââ Î±.component A) (Î².component B â.ââ F.â f))
        (Î².square-filler f â.Â· (G.â f â.â component A))
        ((component B â.â¹ F.â f) â.Â· Î±.square-filler f)
