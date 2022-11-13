module Displayed.Reindex where

open import Cubical.Core.Everything
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Transport
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Path

open import Category
open import Functor
open import Displayed
open import Displayed.Functor

module _ {o h} {𝒞 : Category o h} {o′ h′} (𝒟 : Displayed 𝒞 o′ h′) where
  private
    module 𝒞 = Category.Category 𝒞
    module 𝒟 = Displayed.Displayed 𝒟

  reindex : ∀ {ℓ m} {𝒞′ : Category ℓ m} (F : Functor 𝒞′ 𝒞) → Displayed 𝒞′ o′ h′
  reindex {𝒞′ = 𝒞′} F = record
                { Ob = λ A′ → 𝒟.Ob (F.₀ A′)
                ; Hom = λ f X Y → 𝒟.Hom (F.₁ f) X Y
                ; isSetHom = 𝒟.isSetHom
                ; id = id
                ; _∘_ = _∘_
                ; identˡ = identˡ
                ; identʳ = identʳ
                ; assoc = assoc
                }
    where
      module F = Functor.Functor F
      module 𝒞′ = Category.Category 𝒞′

      id : ∀ {A : 𝒞′.Ob} {X : 𝒟.Ob (F.₀ A)} → 𝒟.Hom (F.₁ 𝒞′.id) X X
      id = subst (λ x → 𝒟.Hom x _ _) (sym F.identity) 𝒟.id

      _∘_ : ∀ {A B C} {f : 𝒞′ [ A , B ]} {g : 𝒞′ [ B , C ]} {X Y Z}
        → 𝒟.Hom (F.₁ g) Y Z
        → 𝒟.Hom (F.₁ f) X Y
        → 𝒟.Hom (F.₁ (𝒞′ [ g ∘ f ])) X Z
      _∘_ = λ g f → subst (λ x → 𝒟.Hom x _ _) (sym F.compose) (g 𝒟.∘ f)

      identˡ : ∀ {A B : 𝒞′.Ob} {f : 𝒞′ [ A , B ]}
        {X : 𝒟.Ob (F.₀ A)} {Y : 𝒟.Ob (F.₀ B)}
        {f′ : 𝒟.Hom (F.₁ f) X Y}
        → PathP (λ i → 𝒟.Hom (F.₁ (𝒞′.identˡ {f = f} i)) X Y) (id ∘ f′) f′
      identˡ {f = f} {X = X} {Y = Y} {f′ = f′} = transport⁻ (PathP≡Path⁻ (λ i → 𝒟.Hom (F.₁ (𝒞′.identˡ i)) X Y) _ _) p
        where
          p : id ∘ f′ ≡ subst (λ x → 𝒟.Hom (F.₁ x) X Y) (sym 𝒞′.identˡ) f′
          p =
              id ∘ f′
            ≡⟨ refl ⟩
              subst (λ x → 𝒟.Hom x _ _) (sym F.compose) (id 𝒟.∘ f′)
            ≡⟨ refl ⟩
              subst (λ x → 𝒟.Hom x _ _) (sym F.compose) (subst (λ x → 𝒟.Hom x _ _) (sym F.identity) 𝒟.id 𝒟.∘ f′)
            ≡⟨ cong (subst (λ x → 𝒟.Hom x _ _) (sym F.compose)) (hoist-substˡ 𝒟 _) ⟩
              subst (λ x → 𝒟.Hom x _ _) (sym F.compose) (subst (λ x → 𝒟.Hom x _ _) (cong (𝒞._∘ F.₁ f) (sym F.identity)) (𝒟.id 𝒟.∘ f′))
            ≡⟨ sym (substComposite (λ x → 𝒟.Hom x _ _) _ _ _) ⟩
              subst (λ x → 𝒟.Hom x _ _) (cong (𝒞._∘ F.₁ f) (sym F.identity) ∙ sym F.compose) (𝒟.id 𝒟.∘ f′)
            ≡⟨ cong
                 (subst (λ x → 𝒟.Hom x _ _)
                  (cong (𝒞._∘ F.₁ f) (sym F.identity) ∙ sym F.compose))
                 (transport (PathP≡Path⁻ (λ i → 𝒟.Hom (𝒞.identˡ i) _ _) _ _) 𝒟.identˡ) ⟩
              subst (λ x → 𝒟.Hom x _ _) (cong (𝒞._∘ F.₁ f) (sym F.identity) ∙ sym F.compose) (subst (λ x → 𝒟.Hom x _ _) (sym 𝒞.identˡ) f′)
            ≡⟨ sym (substComposite (λ x → 𝒟.Hom x _ _) _ _ _) ⟩
              subst (λ x → 𝒟.Hom x _ _) (sym 𝒞.identˡ ∙ (cong (𝒞._∘ F.₁ f) (sym F.identity) ∙ sym F.compose)) f′
            ≡⟨ cong (λ w → subst (λ x → 𝒟.Hom x _ _) w f′) (𝒞.isSetHom _ _ _ _) ⟩
              subst (λ x → 𝒟.Hom (F.₁ x) X Y) (sym 𝒞′.identˡ) f′
            ∎

      identʳ : ∀ {A B : 𝒞′.Ob} {f : 𝒞′ [ A , B ]}
        {X : 𝒟.Ob (F.₀ A)} {Y : 𝒟.Ob (F.₀ B)}
        {f′ : 𝒟.Hom (F.₁ f) X Y}
        → PathP (λ i → 𝒟.Hom (F.₁ (𝒞′.identʳ {f = f} i)) X Y) (f′ ∘ id) f′
      identʳ {f = f} {X = X} {Y = Y} {f′ = f′} = transport⁻ (PathP≡Path⁻ (λ i → 𝒟.Hom (F.₁ (𝒞′.identʳ i)) X Y) _ _) p
        where
          p : f′ ∘ id ≡ subst (λ x → 𝒟.Hom (F.₁ x) X Y) (sym 𝒞′.identʳ) f′
          p =
              subst (λ x → 𝒟.Hom x _ _) (sym F.compose) (f′ 𝒟.∘ subst (λ x → 𝒟.Hom x _ _) (sym F.identity) 𝒟.id)
            ≡⟨ cong (subst (λ x → 𝒟.Hom x _ _) (sym F.compose)) (hoist-substʳ 𝒟 _) ⟩
              subst (λ x → 𝒟.Hom x _ _) (sym F.compose) (subst (λ x → 𝒟.Hom x _ _) (cong (F.₁ f 𝒞.∘_) (sym F.identity)) (f′ 𝒟.∘ 𝒟.id))
            ≡⟨ sym (substComposite (λ x → 𝒟.Hom x _ _) _ _ _) ⟩
              subst (λ x → 𝒟.Hom x _ _) (cong (F.₁ f 𝒞.∘_) (sym F.identity) ∙ sym F.compose) (f′ 𝒟.∘ 𝒟.id)
            ≡⟨ cong
                 (subst (λ x → 𝒟.Hom x _ _)
                  (cong (F.₁ f 𝒞.∘_) (sym F.identity) ∙ sym F.compose))
                 (transport (PathP≡Path⁻ (λ i → 𝒟.Hom (𝒞.identʳ i) _ _) _ _) 𝒟.identʳ) ⟩
              subst (λ x → 𝒟.Hom x _ _) (cong (F.₁ f 𝒞.∘_) (sym F.identity) ∙ sym F.compose) (subst (λ x → 𝒟.Hom x _ _) (sym 𝒞.identʳ) f′)
            ≡⟨ sym (substComposite (λ x → 𝒟.Hom x _ _) _ _ _) ⟩
              subst (λ x → 𝒟.Hom x _ _) (sym 𝒞.identʳ ∙ (cong (F.₁ f 𝒞.∘_) (sym F.identity) ∙ sym F.compose)) f′
            ≡⟨ cong (λ w → subst (λ x → 𝒟.Hom x _ _) w f′) (𝒞.isSetHom _ _ _ _) ⟩
              subst (λ x → 𝒟.Hom (F.₁ x) X Y) (sym 𝒞′.identʳ) f′
            ∎

      assoc : ∀ {A B C D : 𝒞′.Ob}
        {f : 𝒞′ [ A , B ]} {g : 𝒞′ [ B , C ]} {h : 𝒞′ [ C , D ]}
        {X : 𝒟.Ob (F.₀ A)} {Y : 𝒟.Ob (F.₀ B)} {Z : 𝒟.Ob (F.₀ C)} {W : 𝒟.Ob (F.₀ D)}
        {f′ : 𝒟.Hom (F.₁ f) X Y} {g′ : 𝒟.Hom (F.₁ g) Y Z} {h′ : 𝒟.Hom (F.₁ h) Z W}
        → PathP (λ i → 𝒟.Hom (F.₁ (𝒞′.assoc {f = f} {g = g} {h = h} i)) X W) ((h′ ∘ g′) ∘ f′) (h′ ∘ (g′ ∘ f′))
      assoc {f = f} {g = g} {h = h} {X = X} {Y = Y} {W = W} {f′ = f′} {g′ = g′} {h′ = h′} = toPathP (sym p)
        where
          p : h′ ∘ (g′ ∘ f′) ≡ subst (λ x → 𝒟.Hom (F.₁ x) X W) 𝒞′.assoc ((h′ ∘ g′) ∘ f′)
          p =
              h′ ∘ (g′ ∘ f′)
            ≡⟨ refl ⟩
              subst (λ x → 𝒟.Hom x _ _) (sym F.compose) (h′ 𝒟.∘ subst (λ x → 𝒟.Hom x _ _) (sym F.compose) (g′ 𝒟.∘ f′))
            ≡⟨ cong (subst (λ x → 𝒟.Hom x _ _) (sym F.compose)) (hoist-substʳ 𝒟 _) ⟩
              subst (λ x → 𝒟.Hom x _ _) (sym F.compose) (subst (λ x → 𝒟.Hom x _ _) (cong (F.₁ h 𝒞.∘_) (sym F.compose)) (h′ 𝒟.∘ (g′ 𝒟.∘ f′)))
            ≡⟨ sym (substComposite (λ x → 𝒟.Hom x _ _) _ _ _) ⟩
              subst (λ x → 𝒟.Hom x _ _) (cong (F.₁ h 𝒞.∘_) (sym F.compose) ∙ sym F.compose) (h′ 𝒟.∘ (g′ 𝒟.∘ f′))
            ≡⟨ cong
                 (subst (λ x → 𝒟.Hom x _ _)
                  (cong (F.₁ h 𝒞.∘_) (sym F.compose) ∙ sym F.compose))
                 (sym (fromPathP 𝒟.assoc)) ⟩
              subst (λ x → 𝒟.Hom x _ _) (cong (F.₁ h 𝒞.∘_) (sym F.compose) ∙ sym F.compose)
                (subst (λ x → 𝒟.Hom x _ _) 𝒞.assoc ((h′ 𝒟.∘ g′) 𝒟.∘ f′))
            ≡⟨ sym (substComposite (λ x → 𝒟.Hom x _ _) _ _ _) ⟩
              subst (λ x → 𝒟.Hom x _ _) (𝒞.assoc ∙ (cong (F.₁ h 𝒞.∘_) (sym F.compose) ∙ sym F.compose)) ((h′ 𝒟.∘ g′) 𝒟.∘ f′)
            ≡⟨ cong (λ w → subst (λ x → 𝒟.Hom x _ _) w ((h′ 𝒟.∘ g′) 𝒟.∘ f′)) (𝒞.isSetHom _ _ _ _) ⟩
              subst (λ x → 𝒟.Hom x X W) (cong (𝒞._∘ F.₁ f) (sym F.compose) ∙ (sym F.compose ∙ cong F.₁ 𝒞′.assoc)) (((h′ 𝒟.∘ g′) 𝒟.∘ f′))
            ≡⟨ substComposite (λ x → 𝒟.Hom x X W) _ _ _ ⟩
              subst (λ x → 𝒟.Hom x X W) (sym F.compose ∙ cong F.₁ 𝒞′.assoc) (subst (λ x → 𝒟.Hom x _ _) (cong (𝒞._∘ F.₁ f) (sym F.compose)) ((h′ 𝒟.∘ g′) 𝒟.∘ f′))
            ≡⟨ cong
                 (subst (λ x → 𝒟.Hom x X W) (sym F.compose ∙ cong F.₁ 𝒞′.assoc)) (sym (hoist-substˡ 𝒟 _)) ⟩
              subst (λ x → 𝒟.Hom x X W) (sym F.compose ∙ cong F.₁ 𝒞′.assoc) (subst (λ x → 𝒟.Hom x _ _) (sym F.compose) (h′ 𝒟.∘ g′) 𝒟.∘ f′)
            ≡⟨ substComposite (λ x → 𝒟.Hom x X W) _ _ _ ⟩
              subst (λ x → 𝒟.Hom (F.₁ x) X W) 𝒞′.assoc (subst (λ x → 𝒟.Hom x _ _) (sym F.compose) ((subst (λ x → 𝒟.Hom x _ _) (sym F.compose) (h′ 𝒟.∘ g′)) 𝒟.∘ f′))
            ≡⟨ refl ⟩
              subst (λ x → 𝒟.Hom (F.₁ x) X W) 𝒞′.assoc ((h′ ∘ g′) ∘ f′)
            ∎

  reindexProj : ∀ {ℓ m} {𝒞′ : Category ℓ m} (F : Functor 𝒞′ 𝒞)
    → DisplayedFunctor F (reindex F) 𝒟
  reindexProj F = record
    { F₀ = λ A → A
    ; F₁ = λ f → f
    ; identity = toPathP (transportTransport⁻ (λ i → 𝒟.Hom (F.identity i) _ _) _)
    ; compose = toPathP (transportTransport⁻ (λ i → 𝒟.Hom (F.compose i) _ _) _)
    }
    where module F = Functor.Functor F
