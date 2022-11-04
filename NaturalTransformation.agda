module NaturalTransformation where

open import Cubical.Core.Everything
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv.Properties
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism using (isoToPath; isoToEquiv)
open import Cubical.Functions.Embedding
open import Cubical.Reflection.RecordEquiv

open import Category
open import Functor

module _ {o h} {𝒞 : Category o h} {o′ h′} {𝒟 : Category o′ h′} where
  private
    module 𝒞 = Category.Category 𝒞
    module 𝒟 = Category.Category 𝒟

  record NaturalTransformation (F G : Functor 𝒞 𝒟) : Type (ℓ-max o (ℓ-max h h′)) where
    private
      module F = Functor.Functor F
      module G = Functor.Functor G

    field
      component : ∀ (A : 𝒞.Ob) → 𝒟 [ F.₀ A , G.₀ A ]
      commute : ∀ (A B : 𝒞.Ob) {f : 𝒞 [ A , B ]} → 𝒟 [ component B ∘ F.₁ f ] ≡ 𝒟 [ G.₁ f ∘ component A ]

  unquoteDecl NaturalTransformationIsoΣ = declareRecordIsoΣ NaturalTransformationIsoΣ (quote NaturalTransformation)

  module _ {F G : Functor 𝒞 𝒟} where
    private
      module F = Functor.Functor F
      module G = Functor.Functor G

    isSetNaturalTransformation : isSet (NaturalTransformation F G)
    isSetNaturalTransformation =
      subst isSet
        (sym (isoToPath NaturalTransformationIsoΣ))
        (isSetisProp⇒isSetΣ (isSetΠ λ A → 𝒟.isSetHom) λ component → isPropΠ2 λ A B → isPropImplicitΠ λ f → 𝒟.isSetHom _ _)

    componentEmbed : ∀ (α β : NaturalTransformation F G)
      → NaturalTransformation.component α ≡ NaturalTransformation.component β
      → α ≡ β
    componentEmbed α β p i = record { component = p i ; commute = λ A B {f} → a i}
      where
        module α = NaturalTransformation α
        module β = NaturalTransformation β

        a : ∀ {A B f} → PathP (λ i → 𝒟 [ p i B ∘ F.₁ f ] ≡ 𝒟 [ G.₁ f ∘ p i A ]) (α.commute A B {f}) (β.commute A B {f})
        a {A} {B} {f} = toPathP (𝒟.isSetHom _ _ _ _)

  idNatTrans : ∀ {F : Functor 𝒞 𝒟} → NaturalTransformation F F
  idNatTrans {F} = record { component = λ A → 𝒟.id ; commute = λ A B {f} → 𝒟.identˡ ∙ sym 𝒟.identʳ }

  module _ {F G H : Functor 𝒞 𝒟} where
    private
      module F = Functor.Functor F
      module G = Functor.Functor G
      module H = Functor.Functor H

    vertComp : NaturalTransformation G H → NaturalTransformation F G → NaturalTransformation F H
    vertComp β α = record
      { component = λ A → β.component A 𝒟.∘ α.component A
      ; commute = λ A B {f} →
            (𝒟 [ β.component B 𝒟.∘ α.component B ∘ F.₁ f ])
          ≡⟨  𝒟.assoc ⟩
            (𝒟 [ β.component B ∘ α.component B 𝒟.∘ F.₁ f ])
          ≡⟨ cong (β.component B 𝒟.∘_) (α.commute A B) ⟩
            (𝒟 [ β.component B ∘ G.₁ f 𝒟.∘ α.component A ])
          ≡⟨ sym 𝒟.assoc ⟩
            (𝒟 [ β.component B 𝒟.∘ G.₁ f ∘ α.component A ])
          ≡⟨ cong (𝒟._∘ α.component A) (β.commute A B) ⟩
            (𝒟 [ H.₁ f 𝒟.∘ β.component A ∘ α.component A ])
          ≡⟨ 𝒟.assoc ⟩
            (𝒟 [ H.₁ f ∘ β.component A 𝒟.∘ α.component A ])
          ∎
      }
      where
        module α = NaturalTransformation α
        module β = NaturalTransformation β

  module _ {F G : Functor 𝒞 𝒟} where
    private
      module F = Functor.Functor F
      module G = Functor.Functor G

    vertCompIdentˡ : ∀ {α : NaturalTransformation F G} → vertComp idNatTrans α ≡ α
    vertCompIdentˡ {α} = componentEmbed (vertComp idNatTrans α) α (λ i → λ A → 𝒟.identˡ {f = component A} i)
      where open NaturalTransformation α

    vertCompIdentʳ : ∀ {α : NaturalTransformation F G} → vertComp α idNatTrans ≡ α
    vertCompIdentʳ {α} = componentEmbed (vertComp α idNatTrans) α (λ i → λ A → 𝒟.identʳ {f = component A} i)
      where open NaturalTransformation α

  module _ {F G H J : Functor 𝒞 𝒟} where
    private
      module F = Functor.Functor F
      module G = Functor.Functor G
      module H = Functor.Functor H
      module J = Functor.Functor J

    vertCompAssoc : ∀ {α : NaturalTransformation F G} {β : NaturalTransformation G H} {γ : NaturalTransformation H J}
      → vertComp (vertComp γ β) α ≡ vertComp γ (vertComp β α)
    vertCompAssoc {α} {β} {γ} = componentEmbed _ _ λ i A → 𝒟.assoc {f = α.component A} {g = β.component A} {h = γ.component A} i
      where
        module α = NaturalTransformation α
        module β = NaturalTransformation β
        module γ = NaturalTransformation γ

