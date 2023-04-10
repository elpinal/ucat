open import Category

module Limit {o h o′ h′} (𝕀 : Category o h) (𝒞 : Category o′ h′) where

open import Cubical.Core.Everything
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Equiv
import Cubical.Foundations.Isomorphism as Isomorphism
open import Cubical.Data.Sigma
open import Cubical.Reflection.RecordEquiv

open import Functor
open import Functor.Diagonal
open import NaturalTransformation

open import LevelUtil

private
  module 𝒞 = Category.Category 𝒞

open 𝒞

Cone⟨_,_⟩ : 𝒞.Ob → Functor 𝕀 𝒞 → Type (o ⊔ h ⊔ h′)
Cone⟨ a , F ⟩ = NaturalTransformation (Δ 𝕀 𝒞 a) F

record Cone (F : Functor 𝕀 𝒞) : Type (o ⊔ h ⊔ o′ ⊔ h′) where
  field
    X : 𝒞.Ob
    proj : Cone⟨ X , F ⟩

module _ {a : 𝒞.Ob} {F : Functor 𝕀 𝒞} where
  precompose : ∀ {x} → 𝒞.Hom x a → Cone⟨ a , F ⟩ → Cone⟨ x , F ⟩
  precompose f α = record { component = λ A → component A 𝒞.∘ f ; commute = λ A B → λ {f = g} →
      (𝒞 [ component B 𝒞.∘ f ∘ 𝒞.id ])
    ≡⟨ 𝒞.identʳ ⟩
      (𝒞 [ component B ∘ f ])
    ≡⟨ cong (𝒞._∘ f) (sym 𝒞.identʳ) ⟩
      (𝒞 [ component B 𝒞.∘ 𝒞.id ∘ f ])
    ≡⟨ cong (𝒞._∘ f) (commute A B) ⟩
      (𝒞 [ Functor.₁ F g 𝒞.∘ component A ∘ f ])
    ≡⟨ 𝒞.assoc ⟩
      (𝒞 [ Functor.₁ F g ∘ component A 𝒞.∘ f ])
    ∎
    }
    where open NaturalTransformation.NaturalTransformation α

  isLimit : Cone⟨ a , F ⟩ → Type (o ⊔ h ⊔ o′ ⊔ h′)
  isLimit α = ∀ (x : 𝒞.Ob) → isEquiv (λ f → precompose {x = x} f α)

  isPropIsLimit : ∀ α → isProp (isLimit α)
  isPropIsLimit α = isPropΠ λ x → isPropIsEquiv λ f → precompose f α

record Limit⟨_,_⟩ (a : Ob) (F : Functor 𝕀 𝒞) : Type (o ⊔ h ⊔ o′ ⊔ h′) where
  field
    cone : Cone⟨ a , F ⟩
    is-limit : isLimit cone

unquoteDecl Limit⟨⟩IsoΣ = declareRecordIsoΣ Limit⟨⟩IsoΣ (quote Limit⟨_,_⟩)
module Limit⟨⟩IsoΣ {a} {F} = Isomorphism.Iso (Limit⟨⟩IsoΣ {a} {F})

isSetLimit⟨⟩ : ∀ a F → isSet (Limit⟨ a , F ⟩)
isSetLimit⟨⟩ a F =
  isSetRetract Limit⟨⟩IsoΣ.fun Limit⟨⟩IsoΣ.inv Limit⟨⟩IsoΣ.leftInv
    (isSetΣSndProp isSetNaturalTransformation isPropIsLimit)

Limit⟨⟩≡ : ∀ {a F} {L M : Limit⟨ a , F ⟩} → Limit⟨_,_⟩.cone L ≡ Limit⟨_,_⟩.cone M → L ≡ M
Limit⟨⟩≡ {L = L} {M} p = Isomorphism.isoFunInjective Limit⟨⟩IsoΣ L M (Σ≡Prop isPropIsLimit p)

LimitUniqueUpToIso : ∀ a b F → Limit⟨ a , F ⟩ → Limit⟨ b , F ⟩ → Iso 𝒞 a b
LimitUniqueUpToIso a b F L M = record
  { f = invIsEq (M.is-limit a) L.cone
  ; is-iso = record
    { inv = invIsEq (L.is-limit b) M.cone
    ; isoˡ = Isomorphism.isoFunInjective (equivToIso (_ , M.is-limit b)) _ _ (p1 ∙ q1)
    ; isoʳ = Isomorphism.isoFunInjective (equivToIso (_ , L.is-limit a)) _ _ (p2 ∙ q2)
    }
  }
  where
    module L = Limit⟨_,_⟩ L
    module M = Limit⟨_,_⟩ M

    p1 : precompose (invIsEq (M.is-limit a) L.cone ∘ invIsEq (L.is-limit b) M.cone) M.cone ≡ M.cone
    p1 = componentEmbed _ M.cone (funExt λ A →
      let k = secIsEq (M.is-limit a) L.cone
      in
        NaturalTransformation.component M.cone A ∘ (invIsEq (M.is-limit a) L.cone ∘ invIsEq (L.is-limit b) M.cone)
      ≡⟨ sym assoc ⟩
        (NaturalTransformation.component M.cone A ∘ invIsEq (M.is-limit a) L.cone) ∘ invIsEq (L.is-limit b) M.cone
      ≡⟨ cong (_∘ invIsEq (L.is-limit b) M.cone) (cong (λ w → NaturalTransformation.component w A) k) ⟩
        NaturalTransformation.component L.cone A ∘ invIsEq (L.is-limit b) M.cone
      ≡⟨ cong (λ w → NaturalTransformation.component w A) (secIsEq (L.is-limit b) M.cone) ⟩
        NaturalTransformation.component M.cone A
      ∎)

    q1 : M.cone ≡ precompose id M.cone
    q1 = componentEmbed M.cone (precompose id M.cone) (funExt (λ A → sym identʳ))

    p2 : precompose (invIsEq (L.is-limit b) M.cone ∘ invIsEq (M.is-limit a) L.cone) L.cone ≡ L.cone
    p2 = componentEmbed _ L.cone (funExt λ A →
      let k = secIsEq (L.is-limit b) M.cone
      in
        NaturalTransformation.component L.cone A ∘ (invIsEq (L.is-limit b) M.cone ∘ invIsEq (M.is-limit a) L.cone)
      ≡⟨ sym assoc ⟩
        (NaturalTransformation.component L.cone A ∘ invIsEq (L.is-limit b) M.cone) ∘ invIsEq (M.is-limit a) L.cone
      ≡⟨ cong (_∘ invIsEq (M.is-limit a) L.cone) (cong (λ w → NaturalTransformation.component w A) k) ⟩
        NaturalTransformation.component M.cone A ∘ invIsEq (M.is-limit a) L.cone
      ≡⟨ cong (λ w → NaturalTransformation.component w A) (secIsEq (M.is-limit a) L.cone) ⟩
        NaturalTransformation.component L.cone A
      ∎)

    q2 : L.cone ≡ precompose id L.cone
    q2 = componentEmbed L.cone (precompose id L.cone) (funExt (λ A → sym identʳ))

record Limit (F : Functor 𝕀 𝒞) : Type (o ⊔ h ⊔ o′ ⊔ h′) where
  field
    X : Ob
    limit : Limit⟨ X , F ⟩

isPropLimit : isUnivCategory 𝒞 → ∀ F → isProp (Limit F)
isPropLimit u F L M i = record
  { X = p i
  ; limit = toPathP {A = λ i → Limit⟨ p i , F ⟩} {x = L.limit} (Limit⟨⟩≡ {M = M.limit} (fromPathP q)) i
  }
  where
    module L = Limit L
    module M = Limit M
    LCone = Limit⟨_,_⟩.cone L.limit
    MCone = Limit⟨_,_⟩.cone M.limit
    module F = Functor.Functor F

    p : L.X ≡ M.X
    p = isoToId 𝒞 u (LimitUniqueUpToIso L.X M.X F L.limit M.limit)

    r : ∀ A → subst (λ x → Hom x (F.₀ A)) p (NaturalTransformation.component LCone A) ≡ NaturalTransformation.component MCone A
    r A =
        subst (λ x → Hom x (F.₀ A)) p (NaturalTransformation.component LCone A)
      ≡⟨ lemmaIdToIso 𝒞 p refl _ ⟩
        Iso.f (idToIso 𝒞 refl) ∘ (NaturalTransformation.component LCone A ∘ Iso.inv (idToIso 𝒞 p))
      ≡⟨ cong
           (_∘
            (NaturalTransformation.component LCone A ∘ Iso.inv (idToIso 𝒞 p)))
           (transportRefl id) ⟩
        id ∘ (NaturalTransformation.component LCone A ∘ Iso.inv (idToIso 𝒞 p))
      ≡⟨ identˡ ⟩
        NaturalTransformation.component LCone A ∘ Iso.inv (idToIso 𝒞 p)
      ≡⟨ cong (λ w → NaturalTransformation.component LCone A ∘ (Iso.inv w)) (secIsEq u _) ⟩
        NaturalTransformation.component (precompose (invIsEq (Limit⟨_,_⟩.is-limit L.limit M.X) MCone) LCone) A
      ≡⟨ cong (λ w → NaturalTransformation.component w A) (secIsEq (Limit⟨_,_⟩.is-limit L.limit M.X) MCone) ⟩
        NaturalTransformation.component MCone A
      ∎

    helper : ∀ A → NaturalTransformation.component (subst Cone⟨_, F ⟩ p LCone) A
                 ≡ subst (λ x → Hom x (F.₀ A)) p (NaturalTransformation.component LCone A)
    helper A = J P base p
      where
        P : ∀ y (q : L.X ≡ y) → Type h′
        P y q = NaturalTransformation.component (subst Cone⟨_, F ⟩ q LCone) A
                 ≡ subst (λ x → Hom x (F.₀ A)) q (NaturalTransformation.component LCone A)
        base : P L.X refl
        base =
            NaturalTransformation.component (subst Cone⟨_, F ⟩ refl LCone) A
          ≡⟨ cong (λ w → NaturalTransformation.component w A) (transportRefl LCone) ⟩
            NaturalTransformation.component LCone A
          ≡⟨ sym (transportRefl _) ⟩
            subst (λ x → Hom x (F.₀ A)) refl (NaturalTransformation.component LCone A)
          ∎

    q : PathP (λ i → Cone⟨ p i , F ⟩) LCone MCone
    q = toPathP (componentEmbed (subst (Cone⟨_, F ⟩) p LCone) MCone
      (funExt (λ A → helper A ∙ r A)))
