module Displayed.Functor where

open import Cubical.Core.Everything
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Transport
open import Cubical.Foundations.Path

open import Category
open import Functor
open import Displayed

-- Copied from the standard library.
levelOfTerm : ∀ {a} {A : Type a} → A → Level
levelOfTerm {a} _ = a

infixr 8 _⊔_

_⊔_ : Level → Level → Level
_⊔_ = ℓ-max

module UtilComm where
  substCommSlice′ : ∀ {ℓ ℓ′ ℓ″} {A : Type ℓ}
                   → (B : A → Type ℓ′)
                   → (C : A → Type ℓ″)
                   → (F : ∀ i → B i → C i)
                   → {x y : A} (p : x ≡ y) (u : B x)
                   → subst C p (F x u) ≡ F y (subst B p u)
  substCommSlice′ B C F p Bx i =
    transport-fillerExt⁻ (cong C p) i (F _ (transport-fillerExt (cong B p) i Bx))


module _ {o h} {ℂ : Category o h} {o′ h′} {𝔻 : Category o′ h′}
  {ℓ m} {𝒞 : Displayed ℂ ℓ m} {ℓ′ m′} {𝒟 : Displayed 𝔻 ℓ′ m′} where
  private
    module ℂ = Category.Category ℂ
    module 𝔻 = Category.Category 𝔻
    module 𝒞 = Displayed.Displayed 𝒞
    module 𝒟 = Displayed.Displayed 𝒟

  record DisplayedFunctor (Base : Functor ℂ 𝔻) : Type (levelOfTerm ℂ ⊔ levelOfTerm 𝔻 ⊔ levelOfTerm 𝒞 ⊔ levelOfTerm 𝒟) where
    private
      module Base = Functor.Functor Base

    field
      F₀ : ∀ {A : ℂ.Ob} → 𝒞.Ob A → 𝒟.Ob (Base.₀ A)
      F₁ : ∀ {A B} {f : ℂ [ A , B ]} {X Y} → 𝒞.Hom f X Y → 𝒟.Hom (Base.₁ f) (F₀ X) (F₀ Y)
      identity : ∀ {A : ℂ.Ob} {X : 𝒞.Ob A} → PathP (λ i → 𝒟.Hom (Base.identity i) (F₀ X) (F₀ X)) (F₁ 𝒞.id) 𝒟.id
      compose : ∀ {A B C : ℂ.Ob} {X : 𝒞.Ob A} {f : ℂ [ A , B ]} {g : ℂ [ B , C ]}
        {Y : 𝒞.Ob B} {Z : 𝒞.Ob C} {f′ : 𝒞.Hom f X Y} {g′ : 𝒞.Hom g Y Z}
        → PathP (λ i → 𝒟.Hom (Base.compose {f = f} {g = g} i) (F₀ X) (F₀ Z)) (F₁ (g′ 𝒞.∘ f′)) (F₁ g′ 𝒟.∘ F₁ f′)

    ₀ = F₀
    ₁ = F₁

  ∫F : ∀ {Base : Functor ℂ 𝔻} → DisplayedFunctor Base → Functor (∫ 𝒞) (∫ 𝒟)
  ∫F {Base} F = record
    { F₀ = λ where (A , X) → Base.₀ A , F.₀ X
    ; F₁ = λ where (f , f′) → Base.₁ f , F.₁ f′
    ; identity = λ i → Base.identity i , F.identity i
    ; compose = λ where {f = f , f′} {g = g , g′} i → Base.compose {f = f} {g = g} i , F.compose {f′ = f′} {g′ = g′} i
    }
    where
      module Base = Functor.Functor Base
      module F = DisplayedFunctor F

  fibreFunctor : ∀ {Base : Functor ℂ 𝔻} (F : DisplayedFunctor Base) (A : ℂ.Ob) → Functor (fibreCategory 𝒞 A) (fibreCategory 𝒟 (Functor.₀ Base A))
  fibreFunctor {Base} F A = record
    { F₀ = F.₀
    ; F₁ = F₁
    ; identity = fromPathP F.identity
    ; compose = compose
    }
    where
      module Base = Functor.Functor Base
      module F = DisplayedFunctor F

      F₁ : ∀ {X Y} → 𝒞.Hom ℂ.id X Y → 𝒟.Hom _ (F.₀ X) (F.₀ Y)
      F₁ {X} {Y} f = subst (λ x → 𝒟.Hom x (F.₀ X) (F.₀ Y)) Base.identity (F.₁ f)

      compose : ∀ {X Y Z} {f : 𝒞.Hom ℂ.id X Y} {g : 𝒞.Hom ℂ.id Y Z}
        → F₁ (fibreCategory 𝒞 A [ g ∘ f ])
        ≡ fibreCategory 𝒟 (Base.₀ A) [ F₁ g ∘ F₁ f ]
      compose {X} {Y} {Z} {f} {g} =
          F₁ (fibreCategory 𝒞 A [ g ∘ f ])
        ≡⟨ refl ⟩
          F₁ (subst (λ x → 𝒞.Hom x _ _) ℂ.identˡ (g 𝒞.∘ f))
        ≡⟨ refl ⟩
          subst (λ x → 𝒟.Hom x (F.₀ X) (F.₀ Z)) Base.identity (F.₁ (subst (λ x → 𝒞.Hom x _ _) ℂ.identˡ (g 𝒞.∘ f)))
        ≡⟨ cong (subst (λ x → 𝒟.Hom x (F.₀ X) (F.₀ Z)) Base.identity) (sym b) ⟩
          subst (λ x → 𝒟.Hom x (F.₀ X) (F.₀ Z)) Base.identity (subst (λ x → 𝒟.Hom (Base.₁ x) (F.₀ X) (F.₀ Z)) ℂ.identˡ (F.₁ (g 𝒞.∘ f)))
        ≡⟨ sym (substComposite (λ x → 𝒟.Hom x (F.₀ X) (F.₀ Z)) _ _ _) ⟩
          subst (λ x → 𝒟.Hom x (F.₀ X) (F.₀ Z)) (cong Base.₁ ℂ.identˡ ∙ Base.identity) (F.₁ (g 𝒞.∘ f))
        ≡⟨ cong
             (subst (λ x → 𝒟.Hom x (F.₀ X) (F.₀ Z))
              (cong Base.₁ ℂ.identˡ ∙ Base.identity))
             (transport (PathP≡Path⁻ ((λ i → 𝒟.Hom (Base.compose i) (F.₀ X) (F.₀ Z))) _ _) F.compose) ⟩
          subst (λ x → 𝒟.Hom x (F.₀ X) (F.₀ Z)) (cong Base.₁ ℂ.identˡ ∙ Base.identity)
            (subst (λ x → 𝒟.Hom x (F.₀ X) (F.₀ Z)) (sym Base.compose) (F.₁ g 𝒟.∘ F.₁ f))
        ≡⟨ sym (substComposite (λ x → 𝒟.Hom x (F.₀ X) (F.₀ Z)) _ _ _) ⟩
          subst (λ x → 𝒟.Hom x (F.₀ X) (F.₀ Z)) (sym Base.compose ∙ (cong Base.₁ ℂ.identˡ ∙ Base.identity)) (F.₁ g 𝒟.∘ F.₁ f)
        ≡⟨ cong
             (λ w → subst (λ x → 𝒟.Hom x (F.₀ X) (F.₀ Z)) w (F.₁ g 𝒟.∘ F.₁ f)) (𝔻.isSetHom _ _ _ _) ⟩
          subst (λ x → 𝒟.Hom x (F.₀ X) (F.₀ Z)) (cong₂ 𝔻._∘_ Base.identity Base.identity ∙ 𝔻.identˡ) (F.₁ g 𝒟.∘ F.₁ f)
        ≡⟨ substComposite (λ x → 𝒟.Hom x (F.₀ X) (F.₀ Z)) _ _ _ ⟩
          subst (λ x → 𝒟.Hom x _ _) 𝔻.identˡ (subst (λ x → 𝒟.Hom x (F.₀ X) (F.₀ Z)) (cong₂ 𝔻._∘_ Base.identity Base.identity) (F.₁ g 𝒟.∘ F.₁ f))
        ≡⟨ sym (cong (subst (λ x → 𝒟.Hom x _ _) 𝔻.identˡ) (hoist-subst 𝒟 _ _)) ⟩
          subst (λ x → 𝒟.Hom x _ _) 𝔻.identˡ (F₁ g 𝒟.∘ F₁ f)
        ≡⟨ refl ⟩
          fibreCategory 𝒟 (Base.₀ A) [ F₁ g ∘ F₁ f ]
        ∎
        where
          a : ∀ {l k : ℂ [ A , A ]} (p : l ≡ k) (u : 𝒞.Hom l X Z)
            → subst (λ x → 𝒟.Hom (Base.₁ x) (F.₀ X) (F.₀ Z)) p (F.₁ u) ≡ F.₁ (subst (λ x → 𝒞.Hom x X Z) p u)
          a = UtilComm.substCommSlice′
                (λ x → 𝒞.Hom x X Z)
                (λ x → 𝒟.Hom (Base.₁ x) (F.₀ X) (F.₀ Z))
                (λ x y → F.₁ y)

          b : subst (λ x → 𝒟.Hom (Base.₁ x) (F.₀ X) (F.₀ Z)) ℂ.identˡ (F.₁ (g 𝒞.∘ f)) ≡ F.₁ (subst (λ x → 𝒞.Hom x X Z) ℂ.identˡ (g 𝒞.∘ f))
          b = a (ℂ.identˡ {f = ℂ.id}) (g 𝒞.∘ f)
