module Data.Monoid where

open import Cubical.Core.Everything
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Structure
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Data.Sigma

private variable ℓ : Level

record isSemigroup {ℓ} (A : Type ℓ) (f : A → A → A) : Type ℓ where
  field
    assoc : ∀ x y z → f (f x y) z ≡ f x (f y z)
    isSetA : isSet A

isPropIsSemigroup : ∀ (A : Type ℓ) f → isProp (isSemigroup A f)
isPropIsSemigroup A f s t i = record
  { assoc = isPropΠ3 (λ x y z → s.isSetA _ _) s.assoc t.assoc i
  ; isSetA = isPropIsSet s.isSetA t.isSetA i
  }
  where
    module s = isSemigroup s
    module t = isSemigroup t

SemigroupStr : ∀ {ℓ} (A : Type ℓ) → Type ℓ
SemigroupStr A = Σ (A → A → A) (isSemigroup A)

isSetSemigroupStr : ∀ {ℓ} (A : Type ℓ) → isSet (SemigroupStr A)
isSetSemigroupStr A x y = isSetΣSndProp (isSetΠ2 (λ _ _ → S.isSetA)) (isPropIsSemigroup A) x y
  where module S = isSemigroup (x .snd)

Semigroup : ∀ ℓ → Type (ℓ-suc ℓ)
Semigroup ℓ = TypeWithStr ℓ SemigroupStr

private
  Semigroup′ : ∀ ℓ → Type (ℓ-suc ℓ)
  Semigroup′ ℓ = Σ[ A ∈ hSet ℓ ] SemigroupStr (typ A)

  helper1 : ∀ ℓ → Semigroup ℓ → Semigroup′ ℓ
  helper1 ℓ (A , S) = (A , (isSemigroup.isSetA (S .snd))) , S

  helper2 : ∀ ℓ → Semigroup′ ℓ → Semigroup ℓ
  helper2 ℓ ((A , isSetA) , S)= A , S

  isGroupoidSemigroup′ : ∀ ℓ → isGroupoid (Semigroup′ ℓ)
  isGroupoidSemigroup′ ℓ = isGroupoidΣ isGroupoidHSet (λ A → isSet→isGroupoid (isSetSemigroupStr (typ A)))

isGroupoidSemigroup : ∀ ℓ → isGroupoid (Semigroup ℓ)
isGroupoidSemigroup ℓ = isGroupoidRetract (helper1 ℓ) (helper2 ℓ) (λ _ → refl) (isGroupoidSemigroup′ ℓ)

record isMonoid {ℓ} (A : Semigroup ℓ) (e : typ A) : Type ℓ where
  f : typ A → typ A → typ A
  f = str A .fst

  field
    lunit : ∀ x → f e x ≡ x
    runit : ∀ x → f x e ≡ x

isPropIsMonoid : ∀ {ℓ} (A : Semigroup ℓ) e → isProp (isMonoid A e)
isPropIsMonoid A e m n i = record
  { lunit = λ x → s.isSetA _ _ (m.lunit x) (n.lunit x) i
  ; runit = λ x → s.isSetA _ _ (m.runit x) (n.runit x) i
  }
  where
    module s = isSemigroup (str A .snd)
    module m = isMonoid m
    module n = isMonoid n

MonoidStr : ∀ {ℓ} (A : Semigroup ℓ) → Type ℓ
MonoidStr A = Σ (typ A) (isMonoid A)

isPropMonoidStr : ∀ {ℓ} (A : Semigroup ℓ) → isProp (MonoidStr A)
isPropMonoidStr A (e , m) (f , n) = ΣPathP (p , isProp→PathP (λ i → isPropIsMonoid A (p i)) m n)
  where
    module m = isMonoid m
    module n = isMonoid n
    p = sym (n.runit e) ∙ m.lunit f

Monoid : ∀ ℓ → Type (ℓ-suc ℓ)
Monoid ℓ = Σ (Semigroup ℓ) MonoidStr

isGroupoidMonoid : ∀ ℓ → isGroupoid (Monoid ℓ)
isGroupoidMonoid ℓ = isGroupoidΣ (isGroupoidSemigroup ℓ) λ S → isSet→isGroupoid (isProp→isSet (isPropMonoidStr S))
