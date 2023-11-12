-- Categories whose types of objects are contractible.
module Category.ObContr where

open import Cubical.Core.Everything
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism
open import Cubical.Functions.FunExtEquiv
open import Cubical.Data.Unit
open import Cubical.Data.Sigma

open import Data.Monoid
open import Category

open import LevelUtil

CategoryObContr : ∀ (o h : Level) → Type (ℓ-suc (o ⊔ h))
CategoryObContr o h = Σ[ 𝒞 ∈ Category o h ] (isContr (Category.Ob 𝒞))

private variable ℓ o h : Level

fromMonoid′ : Monoid h → Category o h
fromMonoid′ M = record
                 { Ob = Unit*
                 ; Hom = λ A B → M .fst .fst
                 ; isSetHom = S.isSetA
                 ; id = M .snd .fst
                 ; _∘_ = M .fst .snd .fst
                 ; identˡ = M.lunit _
                 ; identʳ = M.runit _
                 ; ident² = M.lunit _
                 ; assoc = S.assoc _ _ _
                 }
  where
    module M = isMonoid (M .snd .snd)
    module S = isSemigroup (M .fst .snd .snd)

fromMonoid : Monoid h → CategoryObContr o h
fromMonoid M = fromMonoid′ M , isContrUnit*

toMonoid : CategoryObContr o h → Monoid h
toMonoid (𝒞 , (c , p)) = (𝒞.Hom c c , 𝒞._∘_ , record { assoc = λ _ _ _ → 𝒞.assoc ; isSetA = 𝒞.isSetHom }) , 𝒞.id , record { lunit = λ _ → 𝒞.identˡ ; runit = λ _ → 𝒞.identʳ }
  where
    module 𝒞 = Category.Category 𝒞

sectionFromMonoid : section {A = CategoryObContr o h} toMonoid fromMonoid
sectionFromMonoid _ = refl

-- retractFromMonoid : retract {A = CategoryObContr o h} toMonoid fromMonoid
-- retractFromMonoid (𝒞 , (c , p)) = Σ≡Prop (λ _ → isPropIsContr) (CategoryPath _ 𝒞 λ i → record
--   { Ob = q i
--   ; Hom = r i
--   ; id = λ { {A = A} → s i {A = A} }
--   ; _∘_ = {!!}
--   })
--   where
--     module 𝒞 = Category.Category 𝒞

--     q : Unit* ≡ 𝒞.Ob
--     q = sym (isContr→≡Unit* (c , p))

--     r : PathP (λ i → ∀ (A B : q i) → Type _) (Category.Hom (fromMonoid′ (toMonoid (𝒞 , (c , p))))) 𝒞.Hom
--     r = toPathP (funExt (λ A → funExt (λ B → fromPathP {A = λ i → Type _} λ i → 𝒞.Hom (p A i) (p B i))))

--     s : PathP (λ i → ∀ {A : q i} → r i A A) 𝒞.id 𝒞.id
--     s = {!!}
