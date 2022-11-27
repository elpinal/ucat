module LevelUtil where

open import Cubical.Core.Everything

-- Copied from the standard library.
levelOfTerm : ∀ {a} {A : Type a} → A → Level
levelOfTerm {a} _ = a

infixr 8 _⊔_

_⊔_ : Level → Level → Level
_⊔_ = ℓ-max
