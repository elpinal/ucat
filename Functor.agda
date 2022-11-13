module Functor where

open import Cubical.Core.Everything
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

open import HLevelUtil

open import Category

record Functor {o h} (𝒞 : Category o h) {o′ h′} (𝒟 : Category o′ h′) : Type (ℓ-max o (ℓ-max h (ℓ-max o′ h′))) where
  private
    module 𝒞 = Category.Category 𝒞
    module 𝒟 = Category.Category 𝒟

  field
    F₀ : 𝒞.Ob → 𝒟.Ob
    F₁ : ∀ {A B : 𝒞.Ob} → 𝒞 [ A , B ] → 𝒟 [ F₀ A , F₀ B ]
    identity : ∀ {A : 𝒞.Ob} → F₁ (𝒞.id {A}) ≡ 𝒟.id
    compose : ∀ {A B C : 𝒞.Ob} {f : 𝒞 [ A , B ]} {g : 𝒞 [ B , C ]} → F₁ (𝒞 [ g ∘ f ]) ≡ 𝒟 [ F₁ g ∘ F₁ f ]

  ₀ = F₀
  ₁ = F₁

module _ {o h} (𝒞 : Category o h) {o′ h′} (𝒟 : Category o′ h′) where
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
