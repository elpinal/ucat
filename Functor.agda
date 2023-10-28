module Functor where

open import Cubical.Core.Everything
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Functions.Surjection

open import HLevelUtil
open import LevelUtil

open import Category

private variable o h o′ h′ : Level

record Functor (𝒞 : Category o h) (𝒟 : Category o′ h′) : Type (o ⊔ h ⊔ o′ ⊔ h′) where
  private
    module 𝒞 = Category.Category 𝒞
    module 𝒟 = Category.Category 𝒟

  field
    F₀ : 𝒞.Ob → 𝒟.Ob
    F₁ : ∀ {A B : 𝒞.Ob} → (f : 𝒞 [ A , B ]) → 𝒟 [ F₀ A , F₀ B ]
    identity : ∀ {A : 𝒞.Ob} → F₁ (𝒞.id {A}) ≡ 𝒟.id
    compose : ∀ {A B C : 𝒞.Ob} {f : 𝒞 [ A , B ]} {g : 𝒞 [ B , C ]} → F₁ (𝒞 [ g ∘ f ]) ≡ 𝒟 [ F₁ g ∘ F₁ f ]

  ₀ = F₀
  ₁ = F₁

oppositeF : ∀ {𝒞 : Category o h} {𝒟 : Category o′ h′} → Functor 𝒞 𝒟 → Functor (opposite 𝒞) (opposite 𝒟)
oppositeF F = record { F₀ = F₀ ; F₁ = F₁ ; identity = identity ; compose = compose }
  where open Functor F

StrictFunctor : StrictCategory o h → StrictCategory o′ h′ → Type (o ⊔ h ⊔ o′ ⊔ h′)
StrictFunctor 𝒞 𝒟 = Functor (StrictCategory.𝒞 𝒞) (StrictCategory.𝒞 𝒟)

module _ {𝒞 : Category o h} where
  idFunctor : Functor 𝒞 𝒞
  idFunctor = record { F₀ = λ A → A ; F₁ = λ f → f ; identity = refl ; compose = refl }

module _ {o″ h″} {𝒞 : Category o h} {𝒟 : Category o′ h′} {ℰ : Category o″ h″} where
  _∘F_ : Functor 𝒟 ℰ → Functor 𝒞 𝒟 → Functor 𝒞 ℰ
  G ∘F F = record
    { F₀ = λ A → G.₀ (F.₀ A)
    ; F₁ = λ f → G.₁ (F.₁ f)
    ; identity = cong G.₁ F.identity ∙ G.identity
    ; compose = cong G.₁ F.compose ∙ G.compose
    }
    where
      module F = Functor F
      module G = Functor G

module _ {𝒞 : Category o h} {𝒟 : Category o′ h′} where
  private
    module 𝒟 = Category.Category 𝒟

  -- Even if the codomain category is not univalent, unicity and
  -- associativity laws hold up to *path*, not just natural
  -- isomorphism.

  identFˡ : (F : Functor 𝒞 𝒟) → idFunctor ∘F F ≡ F
  identFˡ F i = record
    { F₀ = F.₀
    ; F₁ = F.₁
    ; identity = 𝒟.isSetHom _ _ (F.identity ∙ refl) F.identity i
    ; compose = 𝒟.isSetHom _ _ (F.compose ∙ refl) F.compose i
    }
    where
      module F = Functor F

  identFʳ : (F : Functor 𝒞 𝒟) → F ∘F idFunctor ≡ F
  identFʳ F i = record
    { F₀ = F.₀
    ; F₁ = F.₁
    ; identity = 𝒟.isSetHom _ _ (refl ∙ F.identity) F.identity i
    ; compose = 𝒟.isSetHom _ _ (refl ∙ F.compose) F.compose i
    }
    where
      module F = Functor F

module _ {o″ h″ o‴ h‴} {𝒞 : Category o h} {𝒟 : Category o′ h′} {ℰ : Category o″ h″} {ℱ : Category o‴ h‴} where
  private
    module ℱ = Category.Category ℱ

  assocFʳ : (F : Functor 𝒞 𝒟) (G : Functor 𝒟 ℰ) (H : Functor ℰ ℱ) → (H ∘F G) ∘F F ≡ H ∘F (G ∘F F)
  assocFʳ F G H i = record
    { F₀ = λ A → H.₀ (G.₀ (F.₀ A))
    ; F₁ = λ f → H.₁ (G.₁ (F.₁ f))
    ; identity = ℱ.isSetHom _ _ (cong (λ f → H.₁ (G.₁ f)) F.identity ∙ (cong H.₁ G.identity ∙ H.identity)) (cong H.₁ (cong G.₁ F.identity ∙ G.identity) ∙ H.identity) i
    ; compose = ℱ.isSetHom _ _ (cong (λ f → H.₁ (G.₁ f)) F.compose ∙ (cong H.₁ G.compose ∙ H.compose)) (cong H.₁ (cong G.₁ F.compose ∙ G.compose) ∙ H.compose) i
    }
    where
      module F = Functor F
      module G = Functor G
      module H = Functor H

module _ (𝒞 : Category o h) (𝒟 : Category o′ h′) where
  private
    module 𝒞 = Category.Category 𝒞
    module 𝒟 = Category.Category 𝒟

    helper : ∀ {A}
      → isOfHLevelDep2 2 {A = 𝒞.Ob → 𝒟.Ob} (λ F₀ → ∀ {A B : 𝒞.Ob} → 𝒞 [ A , B ] → 𝒟 [ F₀ A , F₀ B ])
        (λ F₀ F₁ → F₁ (𝒞.id {A}) ≡ 𝒟.id)
    helper = isOfHLevel→isOfHLevelDep2 2 {B = λ F₀ → ∀ {A B} → 𝒞 [ A , B ] → 𝒟 [ F₀ A , F₀ B ]} λ F₀ F₁ → isOfHLevelSuc 1 (𝒟.isSetHom _ _)

    helper′ : ∀ {A B C} {f : 𝒞 [ A , B ]} {g : 𝒞 [ B , C ]}
      → isOfHLevelDep2 2 {A = 𝒞.Ob → 𝒟.Ob} (λ F₀ → ∀ {A B : 𝒞.Ob} → 𝒞 [ A , B ] → 𝒟 [ F₀ A , F₀ B ])
        (λ F₀ F₁ → F₁ (𝒞 [ g ∘ f ]) ≡ 𝒟 [ F₁ g ∘ F₁ f ])
    helper′ = isOfHLevel→isOfHLevelDep2 2 {B = λ F₀ → ∀ {A B} → 𝒞 [ A , B ] → 𝒟 [ F₀ A , F₀ B ]} λ F₀ F₁ → isOfHLevelSuc 1 (𝒟.isSetHom _ _)

  FunctorPath : ∀ (F G : Functor 𝒞 𝒟)
    → (p q : F ≡ G)
    → cong Functor.₀ p ≡ cong Functor.₀ q
    → p ≡ q
  FunctorPath F G p q r i j = record
    { F₀ = r i j
    ; F₁ = λ f → F₁ f i j
    ; identity = identity i j
    ; compose = compose i j
    }
    where
      module F = Functor F
      module G = Functor G

      F₁ : ∀ {A B} (f : 𝒞 [ A , B ])
        → PathP (λ i → PathP (λ j → 𝒟 [ r i j A , r i j B ]) (F.₁ f) (G.₁ f)) (λ k → Functor.₁ (p k) f) (λ k → Functor.₁ (q k) f)
      F₁ f = isSet→SquareP (λ i j → 𝒟.isSetHom) (λ k → Functor.₁ (p k) f) (λ k → Functor.₁ (q k) f) (λ i₂ → F.₁ f) λ i₂ → G.₁ f

      identity : ∀ {A} → PathP (λ i → PathP (λ j → Path (𝒟 [ r i j A , r i j A ]) (F₁ (𝒞.id {A}) i j) 𝒟.id) F.identity G.identity) (λ k → Functor.identity (p k)) (λ k → Functor.identity (q k))
      identity = helper F.identity G.identity (λ k → Functor.identity (p k)) (λ k → Functor.identity (q k)) r λ i j f → F₁ f i j

      compose : ∀ {A B C} {f : 𝒞 [ A , B ]} {g : 𝒞 [ B , C ]}
        → PathP (λ i → PathP (λ j → Path (𝒟 [ r i j A , r i j C ]) (F₁ (𝒞 [ g ∘ f ]) i j) (𝒟 [ F₁ g i j ∘ F₁ f i j ])) F.compose G.compose) (λ k → Functor.compose (p k)) (λ k → Functor.compose (q k))
      compose = helper′ F.compose G.compose (λ k → Functor.compose (p k)) (λ k → Functor.compose (q k)) r λ i j f → F₁ f i j

private
  variable
    𝒞 𝒟 : Category o h

isFull : (F : Functor 𝒞 𝒟) → Type _
isFull {𝒞 = 𝒞} {𝒟 = 𝒟} F = ∀ {A B} → isSurjection (F.₁ {A = A} {B = B})
  where module F = Functor F

isFaithful : (F : Functor 𝒞 𝒟) → Type _
isFaithful {𝒞 = 𝒞} F = ∀ {A B} (f g : 𝒞.Hom A B) → F.₁ f ≡ F.₁ g → f ≡ g
  where
    module F = Functor F
    module 𝒞 = Category.Category 𝒞

FullFunctor : Category o h → Category o′ h′ → Type (o ⊔ h ⊔ o′ ⊔ h′)
FullFunctor 𝒞 𝒟 = Σ (Functor 𝒞 𝒟) isFull

FaithfulFunctor : Category o h → Category o′ h′ → Type (o ⊔ h ⊔ o′ ⊔ h′)
FaithfulFunctor 𝒞 𝒟 = Σ (Functor 𝒞 𝒟) isFaithful
