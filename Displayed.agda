module Displayed where

open import Cubical.Core.Everything
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Transport
open import Cubical.Foundations.Equiv

open import Category
open import Functor

record Displayed {o h} (𝒞 : Category o h) o′ h′ : Type (ℓ-suc (ℓ-max o (ℓ-max h (ℓ-max o′ h′)))) where
  private module 𝒞 = Category.Category 𝒞

  field
    Ob : 𝒞.Ob → Type o′
    Hom : ∀ {A B : 𝒞.Ob} (f : 𝒞.Hom A B) (X : Ob A) (Y : Ob B) → Type h′
    isSetHom : ∀ {A B : 𝒞.Ob} {f : 𝒞.Hom A B} {X : Ob A} {Y : Ob B} → isSet (Hom f X Y)

    id : ∀ {A : 𝒞.Ob} {X : Ob A} → Hom 𝒞.id X X
    _∘_ : ∀ {A B C : 𝒞.Ob} {f : 𝒞.Hom A B} {g : 𝒞.Hom B C} {X : Ob A} {Y : Ob B} {Z : Ob C}
      → Hom g Y Z → Hom f X Y → Hom (𝒞 [ g ∘ f ]) X Z

    identˡ : ∀ {A B : 𝒞.Ob} {f : 𝒞.Hom A B} {X : Ob A} {Y : Ob B} {f′ : Hom f X Y}
      → PathP (λ i → Hom (𝒞.identˡ {f = f} i) X Y) (id ∘ f′) f′
    identʳ : ∀ {A B : 𝒞.Ob} {f : 𝒞.Hom A B} {X : Ob A} {Y : Ob B} {f′ : Hom f X Y}
      → PathP (λ i → Hom (𝒞.identʳ {f = f} i) X Y) (f′ ∘ id) f′
    assoc : ∀ {A B C D : 𝒞.Ob} {f : 𝒞.Hom A B} {g : 𝒞.Hom B C} {h : 𝒞.Hom C D}
      {X : Ob A} {Y : Ob B} {Z : Ob C} {W : Ob D} {f′ : Hom f X Y} {g′ : Hom g Y Z} {h′ : Hom h Z W}
      → PathP (λ i → Hom (𝒞.assoc {f = f} {g = g} {h = h} i) X W) ((h′ ∘ g′) ∘ f′) (h′ ∘ (g′ ∘ f′))

-- Total category
∫ : ∀ {o h} {𝒞 : Category o h} {o′ h′} → Displayed 𝒞 o′ h′ → Category (ℓ-max o o′) (ℓ-max h h′)
∫ {𝒞 = 𝒞} 𝒟 = record
        { Ob = Σ 𝒞.Ob 𝒟.Ob
        ; Hom = λ where (A , X) (B , Y) → Σ[ f ∈ 𝒞.Hom A B ] 𝒟.Hom f X Y
        ; isSetHom = isSetΣ 𝒞.isSetHom λ f → 𝒟.isSetHom {f = f}
        ; id = 𝒞.id , 𝒟.id
        ; _∘_ = λ where (g , g′) (f , f′) → (𝒞 [ g ∘ f ]) , (g′ 𝒟.∘ f′)
        ; identˡ = λ where {f = f , f′} i → 𝒞.identˡ {f = f} i , 𝒟.identˡ {f′ = f′} i
        ; identʳ = λ where {f = f , f′} i → 𝒞.identʳ {f = f} i , 𝒟.identʳ {f′ = f′} i
        ; assoc = λ where {f = f , f′} {g = g , g′} {h = h , h′} i → 𝒞.assoc {f = f} {g = g} {h = h} i , 𝒟.assoc {f′ = f′} {g′ = g′} {h′ = h′} i
        }
  where
    module 𝒞 = Category.Category 𝒞
    module 𝒟 = Displayed 𝒟

module _ {o h} {𝒞 : Category o h} {o′ h′} (𝒟 : Displayed 𝒞 o′ h′) where
  private
    module 𝒞 = Category.Category 𝒞
    module 𝒟 = Displayed 𝒟

  Forget : Functor (∫ 𝒟) 𝒞
  Forget = record
    { F₀ = fst
    ; F₁ = fst
    ; identity = refl
    ; compose = refl
    }

  record isDispIso {A B} {f : 𝒞.Hom A B} (is-iso : isIso 𝒞 f) {X Y} (f′ : 𝒟.Hom f X Y) : Type h′ where
    private module is-iso = isIso is-iso
    field
      inv : 𝒟.Hom is-iso.inv Y X
      isoˡ : PathP (λ i → 𝒟.Hom (is-iso.isoˡ i) Y Y) (f′ 𝒟.∘ inv) 𝒟.id
      isoʳ : PathP (λ i → 𝒟.Hom (is-iso.isoʳ i) X X) (inv 𝒟.∘ f′) 𝒟.id

  isDispIsoId : ∀ {A} {X} → isDispIso (isIsoId 𝒞 {A}) (𝒟.id {A} {X})
  isDispIsoId = record { inv = 𝒟.id ; isoˡ = 𝒟.identˡ ; isoʳ = 𝒟.identʳ }

  record DispIso {A B} (iso : Iso 𝒞 A B) X Y : Type h′ where
    private module iso = Iso iso
    field
      f′ : 𝒟.Hom iso.f X Y
      is-disp-iso : isDispIso iso.is-iso f′

  dispIsoId : ∀ {A} {X} → DispIso (isoId 𝒞 {A}) X X
  dispIsoId = record { f′ = 𝒟.id ; is-disp-iso = isDispIsoId }

  helper : ∀ {A B C} {f : 𝒞.Hom A B} {g h : 𝒞.Hom B C} {X Y Z} {f′ : 𝒟.Hom f X Y} {g′ : 𝒟.Hom g Y Z}
    → (p : g ≡ h)
    → subst (λ x → 𝒟.Hom x Y Z) p g′ 𝒟.∘ f′ ≡ subst (λ x → 𝒟.Hom x X Z) (cong (𝒞._∘ f) p) (g′ 𝒟.∘ f′)
  helper {f = f} {g = g} {X = X} {Y = Y} {Z = Z} {f′ = f′} {g′ = g′} = J P base
    where
      P : ∀ h₁ → g ≡ h₁ → Type h′
      P h₁ g≡h₁ = subst (λ x → 𝒟.Hom x Y Z) g≡h₁ g′ 𝒟.∘ f′ ≡ subst (λ x → 𝒟.Hom x X Z) (cong (𝒞._∘ f) g≡h₁) (g′ 𝒟.∘ f′)

      base : P g refl
      base =
          subst (λ x → 𝒟.Hom x Y Z) refl g′ 𝒟.∘ f′
        ≡⟨ cong (𝒟._∘ f′) (transportRefl g′) ⟩
          g′ 𝒟.∘ f′
        ≡⟨ sym (transportRefl _) ⟩
          subst (λ x → 𝒟.Hom x X Z) (cong (𝒞._∘ f) refl) (g′ 𝒟.∘ f′)
        ∎

  helper2 : ∀ {A B C} {f h : 𝒞.Hom A B} {g : 𝒞.Hom B C} {X Y Z} {f′ : 𝒟.Hom f X Y} {g′ : 𝒟.Hom g Y Z}
    → (p : f ≡ h)
    → g′ 𝒟.∘ subst (λ x → 𝒟.Hom x X Y) p f′ ≡ subst (λ x → 𝒟.Hom x X Z) (cong (g 𝒞.∘_) p) (g′ 𝒟.∘ f′)
  helper2 {f = f} {g = g} {X = X} {Y = Y} {Z = Z} {f′ = f′} {g′ = g′} = J P base
    where
      P : ∀ h₁ → f ≡ h₁ → Type h′
      P h₁ f≡h₁ = g′ 𝒟.∘ subst (λ x → 𝒟.Hom x X Y) f≡h₁ f′ ≡ subst (λ x → 𝒟.Hom x X Z) (cong (g 𝒞.∘_) f≡h₁) (g′ 𝒟.∘ f′)

      base : P f refl
      base =
          g′ 𝒟.∘ subst (λ x → 𝒟.Hom x X Y) refl f′
        ≡⟨ cong (g′ 𝒟.∘_) (transportRefl f′) ⟩
          g′ 𝒟.∘ f′
        ≡⟨ sym (transportRefl _) ⟩
          subst (λ x → 𝒟.Hom x X Z) (cong (𝒞._∘ f) refl) (g′ 𝒟.∘ f′)
        ∎

  fibreCategory : 𝒞.Ob → Category o′ h′
  fibreCategory A = record
                      { Ob = 𝒟.Ob A
                      ; Hom = 𝒟.Hom 𝒞.id
                      ; isSetHom = 𝒟.isSetHom
                      ; id = 𝒟.id
                      ; _∘_ = λ g′ f′ → subst (λ x → 𝒟.Hom x _ _) 𝒞.identˡ (g′ 𝒟.∘ f′)
                      ; identˡ = fromPathP 𝒟.identˡ
                      ; identʳ = subst (λ x → subst (λ y → 𝒟.Hom y _ _) x _ ≡ _) (𝒞.ident-unique 𝒞.identʳ) (fromPathP 𝒟.identʳ)
                      ; assoc = λ where {A = X} {B = Y} {C = Z} {D = W} {f = f′} {g = g′} {h = h′} →
                                              let a = fromPathP (𝒟.assoc {f′ = f′} {g′ = g′} {h′ = h′}) in
                                              let b : transport (λ i → 𝒟.Hom (𝒞.id 𝒞.∘ (𝒞.identˡ {f = 𝒞.id}) i) X W) (transport (λ i → 𝒟.Hom (𝒞.assoc {f = 𝒞.id} {g = 𝒞.id} {h = 𝒞.id} i) X W) ((h′ 𝒟.∘ g′) 𝒟.∘ f′))
                                                      ≡ transport (λ i → 𝒟.Hom (𝒞.id 𝒞.∘ (𝒞.identˡ {f = 𝒞.id}) i) X W) (h′ 𝒟.∘ (g′ 𝒟.∘ f′))
                                                  b i = transport (λ i → 𝒟.Hom (𝒞.id 𝒞.∘ (𝒞.identˡ {f = 𝒞.id}) i) X W) (a i)
                                                  c : subst (λ x → 𝒟.Hom x X W) ((𝒞.assoc {f = 𝒞.id} {g = 𝒞.id} {h = 𝒞.id}) ∙ (λ i → 𝒞.id 𝒞.∘ (𝒞.identˡ {f = 𝒞.id}) i)) ((h′ 𝒟.∘ g′) 𝒟.∘ f′)
                                                      ≡ transport (λ i → 𝒟.Hom (𝒞.id 𝒞.∘ (𝒞.identˡ {f = 𝒞.id}) i) X W) (h′ 𝒟.∘ (g′ 𝒟.∘ f′))
                                                  c = substComposite (λ x → 𝒟.Hom x X W) (λ i → 𝒞.assoc {f = 𝒞.id} {g = 𝒞.id} {h = 𝒞.id} i) (λ i → 𝒞.id 𝒞.∘ (𝒞.identˡ {f = 𝒞.id}) i) ((h′ 𝒟.∘ g′) 𝒟.∘ f′) ∙ b
                                                  d : ((𝒞.assoc {A = A} {f = 𝒞.id} {g = 𝒞.id} {h = 𝒞.id}) ∙ (λ i → 𝒞.id 𝒞.∘ (𝒞.identˡ {f = 𝒞.id}) i)) ≡ cong (𝒞._∘ 𝒞.id) 𝒞.identˡ
                                                  d = 𝒞.isSetHom _ _ _ _
                                                  c′ : subst (λ x → 𝒟.Hom x X W) (cong (𝒞._∘ 𝒞.id) 𝒞.identˡ) ((h′ 𝒟.∘ g′) 𝒟.∘ f′)
                                                      ≡ transport (λ i → 𝒟.Hom (𝒞.id 𝒞.∘ (𝒞.identˡ {f = 𝒞.id}) i) X W) (h′ 𝒟.∘ (g′ 𝒟.∘ f′))
                                                  c′ = subst (λ y → subst (λ x → 𝒟.Hom x X W) y ((h′ 𝒟.∘ g′) 𝒟.∘ f′) ≡ transport (λ i → 𝒟.Hom (𝒞.id 𝒞.∘ (𝒞.identˡ {f = 𝒞.id}) i) X W) (h′ 𝒟.∘ (g′ 𝒟.∘ f′))) d c
                                              in
                                                subst (λ x → 𝒟.Hom x X W) 𝒞.identˡ (subst (λ x → 𝒟.Hom x Y W) 𝒞.identˡ (h′ 𝒟.∘ g′) 𝒟.∘ f′)
                                              ≡⟨ cong (subst (λ x → 𝒟.Hom x X W) 𝒞.identˡ) (helper 𝒞.identˡ) ⟩
                                                subst (λ x → 𝒟.Hom x X W) 𝒞.identˡ (subst (λ x → 𝒟.Hom x X W) (cong (𝒞._∘ 𝒞.id) 𝒞.identˡ) ((h′ 𝒟.∘ g′) 𝒟.∘ f′))
                                              ≡⟨ cong (λ y → subst (λ x → 𝒟.Hom x X W) 𝒞.identˡ y) c′ ⟩
                                                subst (λ x → 𝒟.Hom x X W) 𝒞.identˡ (subst (λ x → 𝒟.Hom x X W) (cong (𝒞.id 𝒞.∘_) 𝒞.identˡ) (h′ 𝒟.∘ (g′ 𝒟.∘ f′)))
                                              ≡⟨ cong (subst (λ x → 𝒟.Hom x X W) 𝒞.identˡ) (sym (helper2 𝒞.identˡ)) ⟩
                                                subst (λ x → 𝒟.Hom x X W) 𝒞.identˡ (h′ 𝒟.∘ subst (λ x → 𝒟.Hom x X Z) 𝒞.identˡ (g′ 𝒟.∘ f′))
                                              ∎
                      }

  substHomCod : ∀ {A B C : 𝒞.Ob} (f : 𝒞.Hom A B) (p : B ≡ C) {X : 𝒟.Ob A} {Y : 𝒟.Ob C}
    → 𝒟.Hom f X (subst 𝒟.Ob (sym p) Y) ≡ 𝒟.Hom (subst (𝒞.Hom A) p f) X Y
  substHomCod {A} {B} {C} f p {X} {Y} = J P base p
    where
      P : ∀ C₁ → B ≡ C₁ → Type (ℓ-max o′ (ℓ-suc h′))
      P C₁ p₁ = ∀ {Y₁ : 𝒟.Ob C₁} → 𝒟.Hom f X (subst 𝒟.Ob (sym p₁) Y₁) ≡ 𝒟.Hom (subst (𝒞.Hom A) p₁ f) X Y₁

      base : P B refl
      base {Y₁} =
          𝒟.Hom f X (subst 𝒟.Ob (λ i → B) Y₁)
        ≡⟨ cong (𝒟.Hom f X) (transportRefl Y₁) ⟩
          𝒟.Hom f X Y₁
        ≡⟨ sym (cong (λ x → 𝒟.Hom x X Y₁) (transportRefl f)) ⟩
          𝒟.Hom (subst (𝒞.Hom A) refl f) X Y₁
        ∎

  module M {A B : 𝒞.Ob} (p : A ≡ B) {X Y} (p′ : PathP (λ i → 𝒟.Ob (p i)) X Y) where
    P₀ : ∀ B₁ → (p₁ : A ≡ B₁) → Type h′
    P₀ B₁ p₁ = DispIso (idToIso 𝒞 p₁) X (subst 𝒟.Ob p₁ X)

    base₀ : DispIso (idToIso 𝒞 refl) X (subst 𝒟.Ob refl X)
    base₀ = subst (DispIso (idToIso 𝒞 refl) X) (sym (transportRefl X)) (transport (λ i → DispIso (transportRefl (isoId 𝒞) (~ i)) X X) dispIsoId)

    P₁ : ∀ Y₁ → (p′₁ : subst 𝒟.Ob p X ≡ Y₁) → Type h′
    P₁ Y₁ _ = DispIso (idToIso 𝒞 p) X Y₁

    base₁ : DispIso (idToIso 𝒞 p) X (subst 𝒟.Ob p X)
    base₁ = J P₀ base₀ p

    idToDispIso : DispIso (idToIso 𝒞 p) X Y
    idToDispIso = J P₁ base₁ (fromPathP p′)

  open M using (idToDispIso) public

  isUnivDisplayed : Type (ℓ-max (ℓ-max o o′) h′)
  isUnivDisplayed = ∀ {A B : 𝒞.Ob} (p : A ≡ B) {X : 𝒟.Ob A} {Y : 𝒟.Ob B} → isEquiv (λ (p′ : PathP (λ i → 𝒟.Ob (p i)) X Y) → idToDispIso p p′)

  isPropIsUnivDisplayed : isProp isUnivDisplayed
  isPropIsUnivDisplayed = isPropImplicitΠ2 λ A B → isPropΠ λ p → isPropImplicitΠ2 (λ X Y → isPropIsEquiv (idToDispIso p))
