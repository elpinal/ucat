open import Category

module Category.Functors {o h} (𝒞 : Category o h) {o′ h′} (𝒟 : Category o′ h′) where

open import Cubical.Core.Everything
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Transport
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism using (isoToIsEquiv)
open import Cubical.Foundations.HLevels
open import Cubical.Data.Unit

open import Functor
open import NaturalTransformation

private
  module 𝒞 = Category.Category 𝒞
  module 𝒟 = Category.Category 𝒟

Functors : Category (ℓ-max (ℓ-max (ℓ-max o h) o′) h′) (ℓ-max (ℓ-max o h) h′)
Functors = record
             { Ob = Functor 𝒞 𝒟
             ; Hom = NaturalTransformation
             ; isSetHom = isSetNaturalTransformation
             ; id = idNatTrans
             ; _∘_ = vertComp
             ; identˡ = vertCompIdentˡ
             ; identʳ = vertCompIdentʳ
             ; ident² = vertCompIdentˡ
             ; assoc = λ where {f = α} {g = β} {h = γ} → vertCompAssoc {α = α} {β = β} {γ = γ}
             }

module _ {F G : Functor 𝒞 𝒟} where
  private
    module F = Functor.Functor F
    module G = Functor.Functor G

  isIsoAllComponents : ∀ (α : NaturalTransformation F G)
    → isIso Functors α
    → ∀ A
    → isIso 𝒟 (NaturalTransformation.component α A)
  isIsoAllComponents α is-iso A = record
    { inv = α⁻¹.component A
    ; isoˡ = λ i → NaturalTransformation.component (is-iso.isoˡ i) A
    ; isoʳ = λ i → NaturalTransformation.component (is-iso.isoʳ i) A
    }
    where
      module is-iso = isIso is-iso
      module α⁻¹ = NaturalTransformation.NaturalTransformation is-iso.inv

  isoOb : Iso Functors F G → ∀ A → Iso 𝒟 (F.₀ A) (G.₀ A)
  isoOb iso A = record
    { f = α.component A
    ; is-iso = record
      { inv = α⁻¹.component A
      ; isoˡ = l A
      ; isoʳ = m A }
    }
    where
      module iso = Iso iso
      module is-iso = isIso iso.is-iso
      module α = NaturalTransformation.NaturalTransformation iso.f
      module α⁻¹ = NaturalTransformation.NaturalTransformation iso.inv
      l : ∀ A → 𝒟 [ α.component A ∘ α⁻¹.component A ] ≡ Category.id 𝒟
      l A j = NaturalTransformation.component (is-iso.isoˡ j) A

      m : ∀ A → 𝒟 [ α⁻¹.component A ∘ α.component A ] ≡ Category.id 𝒟
      m A j = NaturalTransformation.component (is-iso.isoʳ j) A

module _ {F G : Functor 𝒞 𝒟} where
  private
    module F = Functor.Functor F
    module G = Functor.Functor G

  idToIsoComponent : ∀ (p : F ≡ G) A
    → isoOb (idToIso Functors p) A ≡ idToIso 𝒟 (λ j → Functor.₀ (p j) A)
  idToIsoComponent p A = J P base p
    where
      P : ∀ F′ (p : F ≡ F′) → Type h′
      P F′ p = isoOb (idToIso Functors p) A ≡ idToIso 𝒟 (λ j → Functor.₀ (p j) A)

      base-f : NaturalTransformation.component (Iso.f (idToIso Functors (λ _ → F))) A ≡ Iso.f (idToIso 𝒟 refl)
      base-f =
          NaturalTransformation.component (Iso.f (idToIso Functors (λ _ → F))) A
        ≡⟨ cong (λ (w : Iso Functors F F) → NaturalTransformation.component (Iso.f w) A) (transportRefl (isoId Functors)) ⟩
          NaturalTransformation.component (idNatTrans {F = F}) A
        ≡⟨ refl ⟩
          Iso.f (isoId 𝒟)
        ≡⟨ sym (cong Iso.f (transportRefl (isoId 𝒟))) ⟩
          Iso.f (idToIso 𝒟 refl)
        ∎

      base-inv : transport (λ j → 𝒟 [ F.₀ (transportRefl A j) , F.₀ (transportRefl A j) ]) 𝒟.id
               ≡ transport (λ _ → 𝒟 [ F.₀ A , F.₀ A ]) 𝒟.id
      base-inv =
          transport (λ j → 𝒟 [ F.₀ (transportRefl A j) , F.₀ (transportRefl A j) ]) 𝒟.id
        ≡⟨ refl ⟩
          subst (λ x → 𝒟 [ F.₀ x , F.₀ x ]) (transportRefl A) (𝒟.id {A = F.₀ (transport refl A)})
        ≡⟨ substCommSlice {A = 𝒞.Ob} (λ _ → Unit*) (λ x → 𝒟 [ F.₀ x , F.₀ x ]) (λ A′ b → 𝒟.id {A = F.₀ A′}) (transportRefl A) tt* ⟩
          𝒟.id {A = F.₀ A}
        ≡⟨ sym (transportRefl _) ⟩
          transport (λ _ → 𝒟 [ F.₀ A , F.₀ A ]) 𝒟.id
        ∎

      isoˡ : PathP (λ i → base-f i 𝒟.∘ base-inv i ≡ 𝒟.id)
        (isoOb (idToIso Functors (λ _ → F)) A .Iso.is-iso .isIso.isoˡ)
        (idToIso 𝒟 (λ _ → F.₀ A) .Iso.is-iso .isIso.isoˡ)
      isoˡ = isSet→isSet' 𝒟.isSetHom _ _ _ _

      isoʳ : PathP (λ i → base-inv i 𝒟.∘ base-f i ≡ 𝒟.id)
        (isoOb (idToIso Functors (λ _ → F)) A .Iso.is-iso .isIso.isoʳ)
        (idToIso 𝒟 (λ _ → F.₀ A) .Iso.is-iso .isIso.isoʳ)
      isoʳ = isSet→isSet' 𝒟.isSetHom _ _ _ _

      base : P F refl
      base i = record
        { f = base-f i
        ; is-iso = record
          { inv = base-inv i
          ; isoˡ = isoˡ i
          ; isoʳ = isoʳ i
          }
        }

  idToIsoComponent-f : ∀ (p : F ≡ G) (A : 𝒞.Ob)
    → NaturalTransformation.component (Iso.f (idToIso Functors p)) A ≡ Iso.f (idToIso 𝒟 (λ j → Functor.₀ (p j) A))
  idToIsoComponent-f p A i = idToIsoComponent p A i .Iso.f

module _ (u : isUnivCategory 𝒟) where
  pathOb : ∀ {F G} → Iso Functors F G → ∀ A → Functor.₀ F A ≡ Functor.₀ G A
  pathOb iso A = isoToId 𝒟 u (isoOb iso A)

  NatIsoToId : ∀ {F G : Functor 𝒞 𝒟}
    → Iso Functors F G
    → F ≡ G
  NatIsoToId {F} {G} iso i = record
    { F₀ = λ A → pathOb iso A i
    ; F₁ = λ {A} {B} f → p f i
    ; identity = λ {A} → toPathP {A = (λ i → p (𝒞.id {A}) i ≡ 𝒟.id)} identity i
    ; compose = λ where {f = f} {g = g} → toPathP {A = (λ i → p (𝒞 [ g ∘ f ]) i ≡ 𝒟 [ p g i ∘ p f i ])} compose i
    }
    where
      module iso = Iso iso
      module is-iso = isIso iso.is-iso
      module α = NaturalTransformation.NaturalTransformation iso.f
      module α⁻¹ = NaturalTransformation.NaturalTransformation iso.inv
      module F = Functor.Functor F
      module G = Functor.Functor G
      p : ∀ {A B} (f : 𝒞 [ A , B ]) → PathP (λ i → 𝒟 [ pathOb iso A i , pathOb iso B i ]) (F.₁ f) (G.₁ f)
      p {A} {B} f = toPathP (
          transport (λ i → 𝒟 [ pathOb iso A i , pathOb iso B i ]) (F.₁ f)
        ≡⟨ lemmaIdToIso 𝒟 (pathOb iso A) (pathOb iso B) _ ⟩
          𝒟 [ Iso.f (idToIso 𝒟 (pathOb iso B)) ∘ (𝒟 [ F.₁ f ∘ Iso.inv (idToIso 𝒟 (pathOb iso A)) ]) ]
        ≡⟨ sym 𝒟.assoc ⟩
          𝒟 [ Iso.f (idToIso 𝒟 (pathOb iso B)) 𝒟.∘ F.₁ f ∘ Iso.inv (idToIso 𝒟 (pathOb iso A)) ]
        ≡⟨ cong (λ w → 𝒟 [ Iso.f w 𝒟.∘ F.₁ f ∘ Iso.inv (idToIso 𝒟 (pathOb iso A)) ]) (secIsEq u _) ⟩
          𝒟 [ α.component B 𝒟.∘ F.₁ f ∘ Iso.inv (idToIso 𝒟 (pathOb iso A)) ]
        ≡⟨ cong (𝒟._∘ Iso.inv (idToIso 𝒟 (pathOb iso A))) (α.commute A B) ⟩
          𝒟 [ G.₁ f 𝒟.∘ α.component A ∘ Iso.inv (idToIso 𝒟 (pathOb iso A)) ]
        ≡⟨ 𝒟.assoc ⟩
          𝒟 [ G.₁ f ∘ α.component A 𝒟.∘ Iso.inv (idToIso 𝒟 (pathOb iso A)) ]
        ≡⟨ cong (λ w → 𝒟 [ G.₁ f ∘ α.component A 𝒟.∘ Iso.inv w ]) (secIsEq u _) ⟩
          𝒟 [ G.₁ f ∘ α.component A 𝒟.∘ α⁻¹.component A ]
        ≡⟨ cong (G.₁ f 𝒟.∘_) (λ i → NaturalTransformation.component (is-iso.isoˡ i) A) ⟩
          𝒟 [ G.₁ f ∘ 𝒟.id ]
        ≡⟨ 𝒟.identʳ ⟩
          G.₁ f
        ∎)

      identity : ∀ {A} → transport (λ i → p (𝒞.id {A}) i ≡ 𝒟.id) F.identity ≡ G.identity
      identity = 𝒟.isSetHom _ _ _ _

      compose : ∀ {A B C} {f : 𝒞 [ A , B ]} {g : 𝒞 [ B , C ]}
        → transport (λ i → p (𝒞 [ g ∘ f ]) i ≡ 𝒟 [ p g i ∘ p f i ]) F.compose ≡ G.compose
      compose = 𝒟.isSetHom _ _ _ _

  NatIsoToId∘idToIso≡id : ∀ {F G : Functor 𝒞 𝒟} (F≡G : F ≡ G) → cong Functor.₀ (NatIsoToId (idToIso Functors F≡G)) ≡ cong Functor.₀ F≡G
  NatIsoToId∘idToIso≡id {F} {G} F≡G i = funExt λ A → k A i
    where
      module F = Functor.Functor F
      module G = Functor.Functor G
      module iso = Iso (idToIso Functors F≡G)
      module is-iso = isIso iso.is-iso
      module α = NaturalTransformation.NaturalTransformation iso.f
      module α⁻¹ = NaturalTransformation.NaturalTransformation iso.inv

      k : ∀ (A : 𝒞.Ob) → cong₂ Functor.₀ (NatIsoToId (idToIso Functors F≡G)) (λ _ → A) ≡ cong₂ Functor.₀ F≡G (λ _ → A)
      k A =
          cong₂ Functor.₀ (NatIsoToId (idToIso Functors F≡G)) (λ _ → A)
        ≡⟨ refl ⟩
          (λ i → Functor.₀ (NatIsoToId (idToIso Functors F≡G) i) A)
        ≡⟨ refl ⟩
          pathOb (idToIso Functors F≡G) A
        ≡⟨ refl ⟩
          isoToId 𝒟 u (isoOb (idToIso Functors F≡G) A)
        ≡⟨ cong (isoToId 𝒟 u) (idToIsoComponent F≡G A) ⟩
          isoToId 𝒟 u (idToIso 𝒟 (λ j → Functor.₀ (F≡G j) A))
        ≡⟨ retIsEq u (cong₂ Functor.₀ F≡G (λ _ → A)) ⟩
          (λ i → Functor.₀ (F≡G i) A)
        ≡⟨ refl ⟩
          cong₂ Functor.₀ F≡G (λ _ → A)
        ∎

  idToIso∘NatIsoToId≡id : ∀ {F G} (iso : Iso Functors F G) A
    → NaturalTransformation.component (Iso.f (idToIso Functors (NatIsoToId iso))) A
    ≡ NaturalTransformation.component (Iso.f iso) A
  idToIso∘NatIsoToId≡id iso A =
      NaturalTransformation.component (Iso.f (idToIso Functors (NatIsoToId iso))) A
    ≡⟨ idToIsoComponent-f (NatIsoToId iso) A ⟩
      Iso.f (idToIso 𝒟 (λ j → Functor.₀ (NatIsoToId iso j) A))
    ≡⟨ refl ⟩
      Iso.f (idToIso 𝒟 (λ j → pathOb iso A j))
    ≡⟨ refl ⟩
      Iso.f (idToIso 𝒟 (λ j → isoToId 𝒟 u (isoOb iso A) j))
    ≡⟨ refl ⟩
      Iso.f (idToIso 𝒟 (isoToId 𝒟 u (isoOb iso A)))
    ≡⟨ cong Iso.f (secIsEq u _) ⟩
      Iso.f (isoOb iso A)
    ≡⟨ refl ⟩
      NaturalTransformation.component (Iso.f iso) A
    ∎

  isUnivFunctors : isUnivCategory Functors
  isUnivFunctors {A = F} {B = G} = isoToIsEquiv (record
    { fun = idToIso Functors
    ; inv = NatIsoToId
    ; rightInv = λ iso → PathIso _ _ iso (componentEmbed _ _ λ i A → idToIso∘NatIsoToId≡id iso A i)
    ; leftInv = λ F≡G → FunctorPath 𝒞 𝒟 F G _ F≡G (NatIsoToId∘idToIso≡id F≡G)
    })
