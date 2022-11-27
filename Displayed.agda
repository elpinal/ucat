module Displayed where

open import Cubical.Core.Everything
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Transport
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Path
open import Cubical.Foundations.GroupoidLaws using (cong-∙; lCancel; rUnit; lUnit)

open import Category
open import Functor

module PathPConv {ℓ} {A : I → Type ℓ} {x : A i0} {y : A i1} where
  toFrom : (p : PathP A x y) → toPathP (fromPathP p) ≡ p
  toFrom p = retEq (PathP≃Path A x y) p

  fromTo : (p : transport (λ i → A i) x ≡ y) → fromPathP {A = A} (toPathP p) ≡ p
  fromTo p = secEq (PathP≃Path A x y) p

module CongUtil where
  cong₂-∙∙ : ∀ {ℓ₁ ℓ₂ ℓ₃} {A : Type ℓ₁} {w x y z : A} {B : Type ℓ₂} {w′ x′ y′ z′ : B} {C : Type ℓ₃} (f : A → B → C)
    (p : w ≡ x) (q : x ≡ y) (r : y ≡ z)
    (p′ : w′ ≡ x′) (q′ : x′ ≡ y′) (r′ : y′ ≡ z′)
    → cong₂ f (p ∙∙ q ∙∙ r) (p′ ∙∙ q′ ∙∙ r′) ≡ (cong₂ f p p′) ∙∙ (cong₂ f q q′) ∙∙ (cong₂ f r r′)
  cong₂-∙∙ f p q r p′ q′ r′ j i = hcomp (λ k → λ where
    (j = i0) → f (doubleCompPath-filler p q r k i) (doubleCompPath-filler p′ q′ r′ k i)
    (i = i0) → f (p (~ k)) (p′ (~ k))
    (i = i1) → f (r k) (r′ k)) (f (q i) (q′ i))

  cong₂-∙ : ∀ {ℓ₁ ℓ₂ ℓ₃} {A : Type ℓ₁} {x y z : A} {B : Type ℓ₂} {x′ y′ z′ : B} {C : Type ℓ₃} (f : A → B → C)
    (p : x ≡ y) (q : y ≡ z)
    (p′ : x′ ≡ y′) (q′ : y′ ≡ z′)
    → cong₂ f (p ∙ q) (p′ ∙ q′) ≡ (cong₂ f p p′) ∙ (cong₂ f q q′)
  cong₂-∙ f p q p′ q′ = cong₂-∙∙ f refl p q refl p′ q′

module Util {ℓ} {A : Type ℓ} {x : A} where
  sq : Square (sym (transportRefl x)) (toPathP refl) refl refl
  sq = doubleCompPath-filler refl (sym (transportRefl x)) refl

  toPathPRefl : toPathP (λ _ → transport refl x) ≡ sym (transportRefl x)
  toPathPRefl = sym sq

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

  isFaithfulForget : (∀ {A B} (f : 𝒞.Hom A B) X Y → isProp (𝒟.Hom f X Y)) → isFaithful Forget
  isFaithfulForget isPropHom {A = A , X} {B = B , Y} (f , f′) (g , g′) f≡g i = f≡g i , p i
    where
      p : PathP (λ i → 𝒟.Hom (f≡g i) X Y) f′ g′
      p = toPathP (isPropHom g X Y _ g′)

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

    inv = isDispIso.inv is-disp-iso

  VertIso : ∀ {A} (X : 𝒟.Ob A) (Y : 𝒟.Ob A) → Type h′
  VertIso X Y = DispIso (isoId 𝒞) X Y

  dispIsoId : ∀ {A} {X} → DispIso (isoId 𝒞 {A}) X X
  dispIsoId = record { f′ = 𝒟.id ; is-disp-iso = isDispIsoId }

  hoist-substˡ : ∀ {A B C} {f : 𝒞.Hom A B} {g h : 𝒞.Hom B C} {X Y Z} {f′ : 𝒟.Hom f X Y} {g′ : 𝒟.Hom g Y Z}
    → (p : g ≡ h)
    → subst (λ x → 𝒟.Hom x Y Z) p g′ 𝒟.∘ f′ ≡ subst (λ x → 𝒟.Hom x X Z) (cong (𝒞._∘ f) p) (g′ 𝒟.∘ f′)
  hoist-substˡ {f = f} {g = g} {X = X} {Y = Y} {Z = Z} {f′ = f′} {g′ = g′} = J P base
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

  hoist-substʳ : ∀ {A B C} {f h : 𝒞.Hom A B} {g : 𝒞.Hom B C} {X Y Z} {f′ : 𝒟.Hom f X Y} {g′ : 𝒟.Hom g Y Z}
    → (p : f ≡ h)
    → g′ 𝒟.∘ subst (λ x → 𝒟.Hom x X Y) p f′ ≡ subst (λ x → 𝒟.Hom x X Z) (cong (g 𝒞.∘_) p) (g′ 𝒟.∘ f′)
  hoist-substʳ {f = f} {g = g} {X = X} {Y = Y} {Z = Z} {f′ = f′} {g′ = g′} = J P base
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

  hoist-subst : ∀ {A B C} {f h : 𝒞.Hom A B} {g i : 𝒞.Hom B C} {X Y Z} {f′ : 𝒟.Hom f X Y} {g′ : 𝒟.Hom g Y Z}
    → (p : f ≡ h)
    → (q : g ≡ i)
    → subst (λ x → 𝒟.Hom x Y Z) q g′ 𝒟.∘ subst (λ x → 𝒟.Hom x X Y) p f′ ≡ subst (λ x → 𝒟.Hom x X Z) (cong₂ 𝒞._∘_ q p) (g′ 𝒟.∘ f′)
  hoist-subst {f = f} {g = g} {X = X} {Y = Y} {Z = Z} {f′ = f′} {g′ = g′} p q =
      subst (λ x → 𝒟.Hom x Y Z) q g′ 𝒟.∘ subst (λ x → 𝒟.Hom x X Y) p f′
    ≡⟨ hoist-substˡ _ ⟩
      subst (λ x → 𝒟.Hom x X Z) (cong (𝒞._∘ _) q) (g′ 𝒟.∘ subst (λ x → 𝒟.Hom x X Y) p f′)
    ≡⟨ cong (subst (λ x → 𝒟.Hom x X Z) (cong (𝒞._∘ _) q)) (hoist-substʳ _) ⟩
      subst (λ x → 𝒟.Hom x X Z) (cong (𝒞._∘ _) q) (subst (λ x → 𝒟.Hom x X Z) (cong (g 𝒞.∘_) p) (g′ 𝒟.∘ f′))
    ≡⟨ sym (substComposite (λ x → 𝒟.Hom x X Z) _ _ _) ⟩
      subst (λ x → 𝒟.Hom x X Z) (cong (g 𝒞.∘_) p ∙ cong (𝒞._∘ _) q) (g′ 𝒟.∘ f′)
    ≡⟨ cong (λ w → subst (λ x → 𝒟.Hom x X Z) w (g′ 𝒟.∘ f′)) (𝒞.isSetHom _ _ _ _) ⟩
      subst (λ x → 𝒟.Hom x X Z) (cong₂ 𝒞._∘_ q p) (g′ 𝒟.∘ f′)
    ∎

  hoist-subst-Obʳ : ∀ {A B C} {f : 𝒞.Hom A B} {g : 𝒞.Hom B C} {X X′ Y Z} {f′ : 𝒟.Hom f X Y} {g′ : 𝒟.Hom g Y Z}
    → (p : X ≡ X′)
    → g′ 𝒟.∘ subst (λ x → 𝒟.Hom f x Y) p f′ ≡ subst (λ x → 𝒟.Hom (𝒞 [ g ∘ f ]) x Z) p (g′ 𝒟.∘ f′)
  hoist-subst-Obʳ {A} {B} {C} {f} {g} {X} {X′} {Y} {Z} {f′} {g′} = J P base
    where
      P : ∀ y (p : X ≡ y) → Type h′
      P y p = g′ 𝒟.∘ subst (λ x → 𝒟.Hom f x Y) p f′ ≡ subst (λ x → 𝒟.Hom (𝒞 [ g ∘ f ]) x Z) p (g′ 𝒟.∘ f′)

      base : g′ 𝒟.∘ subst (λ x → 𝒟.Hom f x Y) refl f′ ≡ subst (λ x → 𝒟.Hom (𝒞 [ g ∘ f ]) x Z) refl (g′ 𝒟.∘ f′)
      base =
          g′ 𝒟.∘ subst (λ x → 𝒟.Hom f x Y) refl f′
        ≡⟨ cong (g′ 𝒟.∘_) (transportRefl _) ⟩
          g′ 𝒟.∘ f′
        ≡⟨ sym (transportRefl _) ⟩
          subst (λ x → 𝒟.Hom (𝒞 [ g ∘ f ]) x Z) refl (g′ 𝒟.∘ f′)
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
                                              ≡⟨ cong (subst (λ x → 𝒟.Hom x X W) 𝒞.identˡ) (hoist-substˡ 𝒞.identˡ) ⟩
                                                subst (λ x → 𝒟.Hom x X W) 𝒞.identˡ (subst (λ x → 𝒟.Hom x X W) (cong (𝒞._∘ 𝒞.id) 𝒞.identˡ) ((h′ 𝒟.∘ g′) 𝒟.∘ f′))
                                              ≡⟨ cong (λ y → subst (λ x → 𝒟.Hom x X W) 𝒞.identˡ y) c′ ⟩
                                                subst (λ x → 𝒟.Hom x X W) 𝒞.identˡ (subst (λ x → 𝒟.Hom x X W) (cong (𝒞.id 𝒞.∘_) 𝒞.identˡ) (h′ 𝒟.∘ (g′ 𝒟.∘ f′)))
                                              ≡⟨ cong (subst (λ x → 𝒟.Hom x X W) 𝒞.identˡ) (sym (hoist-substʳ 𝒞.identˡ)) ⟩
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
    base₀ = subst2 (λ x → DispIso x X) (sym (transportRefl _)) (sym (transportRefl X)) dispIsoId

    P₁ : ∀ Y₁ → (p′₁ : subst 𝒟.Ob p X ≡ Y₁) → Type h′
    P₁ Y₁ _ = DispIso (idToIso 𝒞 p) X Y₁

    base₁ : DispIso (idToIso 𝒞 p) X (subst 𝒟.Ob p X)
    base₁ = J P₀ base₀ p

    idToDispIso : DispIso (idToIso 𝒞 p) X Y
    idToDispIso = J P₁ base₁ (fromPathP p′)

  open M using (idToDispIso) public

  idToVertIso : ∀ {A} {X Y : 𝒟.Ob A} (p′ : X ≡ Y) → VertIso X Y
  idToVertIso {A} {X} {Y} p′ = subst (λ x → DispIso x X Y) (transportRefl _) (idToDispIso refl p′)

  vertIsoTriangle : ∀ {A B} {f : 𝒞 [ A , B ]} {X X′} {Y} {f′ : 𝒟.Hom f X Y} (p : X ≡ X′)
    → subst (λ x → 𝒟.Hom f x Y) p f′ ≡ subst (λ x → 𝒟.Hom x X′ Y) 𝒞.identʳ (f′ 𝒟.∘ DispIso.inv (idToVertIso p))
  vertIsoTriangle {A} {f = f} {X = X} {X′ = X′} {Y = Y} {f′ = f′} p = subst (λ w → subst (λ x → 𝒟.Hom f x Y) w f′ ≡ subst (λ x → 𝒟.Hom x X′ Y) 𝒞.identʳ (f′ 𝒟.∘ DispIso.inv (idToVertIso w))) (PathPConv.toFrom p) (J P base (fromPathP p))
    where
      P : ∀ y (p′ : transport refl X ≡ y) → Type h′
      P y p′ = subst (λ x → 𝒟.Hom f x Y) (toPathP p′) f′ ≡ subst (λ x → 𝒟.Hom x y Y) 𝒞.identʳ (f′ 𝒟.∘ DispIso.inv (idToVertIso (toPathP p′)))

      base : P (transport refl X) refl
      base =
          subst (λ x → 𝒟.Hom f x Y) (toPathP {A = λ _ → 𝒟.Ob A} refl) f′
        ≡⟨ cong (λ w → subst (λ x → 𝒟.Hom f x Y) w f′) Util.toPathPRefl ⟩
          subst (λ x → 𝒟.Hom f x Y) (sym (transportRefl X)) f′
        ≡⟨ cong (λ w → subst (λ x → 𝒟.Hom f x Y) w f′) (lUnit _) ⟩
          subst (λ x → 𝒟.Hom f x Y) (refl ∙ sym (transportRefl X)) f′
        ≡⟨ cong
             (λ x →
                subst2 (λ v w → 𝒟.Hom v w Y) x (refl ∙ sym (transportRefl X)) f′)
             (sym (lCancel _)) ⟩
          subst2 (λ v w → 𝒟.Hom v w Y) (sym (𝒞.identʳ {f = f}) ∙ 𝒞.identʳ {f = f}) (refl ∙ sym (transportRefl X)) f′
        ≡⟨ cong (λ x → transport x f′) (CongUtil.cong₂-∙ (λ v w → 𝒟.Hom v w Y) _ _ _ _) ⟩
          transport ((λ i → 𝒟.Hom (sym (𝒞.identʳ {f = f}) i) X Y) ∙ (λ i → 𝒟.Hom (𝒞.identʳ {f = f} i) (sym (transportRefl X) i) Y)) f′
        ≡⟨ transportComposite ((λ i → 𝒟.Hom (sym (𝒞.identʳ {f = f}) i) X Y)) (λ i → 𝒟.Hom (𝒞.identʳ {f = f} i) (sym (transportRefl X) i) Y) f′ ⟩
          subst2 (λ v w → 𝒟.Hom v w Y) (𝒞.identʳ {f = f}) (sym (transportRefl X)) (subst⁻ (λ x → 𝒟.Hom x X Y) 𝒞.identʳ f′)
        ≡⟨ cong
             (subst2 (λ v w → 𝒟.Hom v w Y) (𝒞.identʳ {f = f})
              (sym (transportRefl X)))
             (sym (transport (PathP≡Path⁻ (λ i → 𝒟.Hom (𝒞.identʳ {f = f} i) X Y) (f′ 𝒟.∘ 𝒟.id) f′) (𝒟.identʳ))) ⟩
          subst2 (λ v w → 𝒟.Hom v w Y) (𝒞.identʳ {f = f}) (sym (transportRefl X)) (f′ 𝒟.∘ 𝒟.id)
        ≡⟨ cong
             (λ x →
                subst2 (λ v w → 𝒟.Hom v w Y) (𝒞.identʳ {f = f}) x (f′ 𝒟.∘ 𝒟.id))
             (rUnit _) ⟩
          subst2 (λ v w → 𝒟.Hom v w Y) (𝒞.identʳ {f = f}) (sym (transportRefl X) ∙ refl) (f′ 𝒟.∘ 𝒟.id)
        ≡⟨ cong
             (λ x →
                subst2 (λ v w → 𝒟.Hom v w Y) x (sym (transportRefl X) ∙ refl)
                (f′ 𝒟.∘ 𝒟.id))
             (lUnit 𝒞.identʳ) ⟩
          subst2 (λ v w → 𝒟.Hom v w Y) (refl ∙ 𝒞.identʳ {f = f}) (sym (transportRefl X) ∙ refl) (f′ 𝒟.∘ 𝒟.id)
        ≡⟨ cong (λ x → transport x (f′ 𝒟.∘ 𝒟.id)) (CongUtil.cong₂-∙ (λ v w → 𝒟.Hom v w Y) _ _ _ _) ⟩
          transport ((λ i → 𝒟.Hom (𝒞 [ f ∘ 𝒞.id ]) (sym (transportRefl X) i) Y) ∙ (λ i → 𝒟.Hom (𝒞.identʳ {f = f} i) (transport refl X) Y)) (f′ 𝒟.∘ 𝒟.id)
        ≡⟨ transportComposite ((λ i → 𝒟.Hom (𝒞 [ f ∘ 𝒞.id ]) (sym (transportRefl X) i) Y)) ((λ i → 𝒟.Hom (𝒞.identʳ {f = f} i) (transport refl X) Y)) (f′ 𝒟.∘ 𝒟.id) ⟩
          subst (λ x → 𝒟.Hom x (transport refl X) Y) 𝒞.identʳ
            (subst (λ x → 𝒟.Hom (𝒞 [ f ∘ 𝒞.id ]) x Y) (sym (transportRefl X)) (f′ 𝒟.∘ 𝒟.id))
        ≡⟨ cong (λ w → subst (λ x → 𝒟.Hom x (transport refl X) Y) 𝒞.identʳ w)
             (sym (hoist-subst-Obʳ (sym (transportRefl _)))) ⟩
          subst (λ x → 𝒟.Hom x (transport refl X) Y) 𝒞.identʳ
            (f′ 𝒟.∘ subst (λ x → 𝒟.Hom 𝒞.id x X) (sym (transportRefl X)) (𝒟.id {A = A} {X = X}))
        ≡⟨ refl ⟩
          subst (λ x → 𝒟.Hom x (transport refl X) Y) 𝒞.identʳ
            (f′ 𝒟.∘ DispIso.inv (subst (λ x → DispIso (isoId 𝒞) X x) (sym (transportRefl X)) dispIsoId))
        ≡⟨ cong
             (λ w →
                subst (λ x → 𝒟.Hom x (transport refl X) Y) 𝒞.identʳ
                (f′ 𝒟.∘
                 DispIso.inv
                 (transport (λ i → DispIso (isoId 𝒞) X (w i)) dispIsoId)))
             (rUnit (sym (transportRefl X))) ⟩
          subst (λ x → 𝒟.Hom x (transport refl X) Y) 𝒞.identʳ
            (f′ 𝒟.∘ DispIso.inv (transport (λ i → DispIso (isoId 𝒞) X ((sym (transportRefl X) ∙ refl) i)) dispIsoId))
        ≡⟨ cong
             (λ w →
                subst (λ x → 𝒟.Hom x (transport refl X) Y) 𝒞.identʳ
                (f′ 𝒟.∘
                 DispIso.inv (transport (λ i → DispIso (w i) X ((sym (transportRefl X) ∙ refl) i)) dispIsoId)))
             (sym (lCancel (transportRefl (isoId 𝒞)))) ⟩
          subst (λ x → 𝒟.Hom x (transport refl X) Y) 𝒞.identʳ
            (f′ 𝒟.∘ DispIso.inv (transport (λ i → DispIso ((sym (transportRefl (isoId 𝒞)) ∙ transportRefl (isoId 𝒞)) i) X ((sym (transportRefl X) ∙ refl) i)) dispIsoId))
        ≡⟨ cong
             (λ w →
                subst (λ x → 𝒟.Hom x (transport refl X) Y) 𝒞.identʳ
                (f′ 𝒟.∘ DispIso.inv (transport w dispIsoId)))
             (CongUtil.cong₂-∙ (λ a → DispIso a X) (sym (transportRefl (isoId 𝒞))) (transportRefl (isoId 𝒞)) (sym (transportRefl X)) refl ) ⟩
          subst (λ x → 𝒟.Hom x (transport refl X) Y) 𝒞.identʳ
            (f′ 𝒟.∘ DispIso.inv (transport ((λ i → DispIso (sym (transportRefl (isoId 𝒞)) i) X (sym (transportRefl X) i)) ∙ (λ i → DispIso (transportRefl (isoId 𝒞) i) X (transport refl X))) dispIsoId))
        ≡⟨ cong
             (λ w →
                subst (λ x → 𝒟.Hom x (transport refl X) Y) 𝒞.identʳ
                (f′ 𝒟.∘ DispIso.inv w))
             (transportComposite ((λ i → DispIso (sym (transportRefl (isoId 𝒞)) i) X (sym (transportRefl X) i))) ((λ i → DispIso (transportRefl (isoId 𝒞) i) X (transport refl X))) dispIsoId) ⟩
          subst (λ x → 𝒟.Hom x (transport refl X) Y) 𝒞.identʳ
            (f′ 𝒟.∘ DispIso.inv (transport (λ i → DispIso (transportRefl (isoId 𝒞) i) X (transport refl X)) (transport (λ i → DispIso (sym (transportRefl (isoId 𝒞)) i) X (sym (transportRefl X) i)) dispIsoId)))
        ≡⟨ refl ⟩
          subst (λ x → 𝒟.Hom x (transport refl X) Y) 𝒞.identʳ
            (f′ 𝒟.∘ DispIso.inv (subst (λ x → DispIso x X (transport refl X)) (transportRefl _) (subst2 (λ x → DispIso x X) (sym (transportRefl _)) (sym (transportRefl X)) dispIsoId)))
        ≡⟨ refl ⟩
          subst (λ x → 𝒟.Hom x (transport refl X) Y) 𝒞.identʳ
            (f′ 𝒟.∘ DispIso.inv (subst (λ x → DispIso x X (transport refl X)) (transportRefl _) (M.base₀ refl (toPathP refl))))
        ≡⟨ cong
             (λ w →
                subst (λ x → 𝒟.Hom x (transport refl X) Y) 𝒞.identʳ
                (f′ 𝒟.∘
                 DispIso.inv
                 (subst (λ x → DispIso x X (transport refl X)) (transportRefl _)
                  w)))
             (sym (JRefl (M.P₀ refl (toPathP refl)) (M.base₀ refl (toPathP refl)))) ⟩
          subst (λ x → 𝒟.Hom x (transport refl X) Y) 𝒞.identʳ
            (f′ 𝒟.∘ DispIso.inv (subst (λ x → DispIso x X (transport refl X)) (transportRefl _) (M.base₁ refl (toPathP refl))))
        ≡⟨ cong
             (λ w →
                subst (λ x → 𝒟.Hom x (transport refl X) Y) 𝒞.identʳ
                (f′ 𝒟.∘
                 DispIso.inv
                 (subst (λ x → DispIso x X (transport refl X)) (transportRefl _)
                  w)))
             (sym (JRefl ((M.P₁ refl (toPathP refl))) ((M.base₁ refl (toPathP refl))))) ⟩
          subst (λ x → 𝒟.Hom x (transport refl X) Y) 𝒞.identʳ
            (f′ 𝒟.∘ DispIso.inv (subst (λ x → DispIso x X (transport refl X)) (transportRefl _) (J (M.P₁ refl (toPathP refl)) (M.base₁ refl (toPathP refl)) refl)))
        ≡⟨ cong
             (λ w →
                subst (λ x → 𝒟.Hom x (transport refl X) Y) 𝒞.identʳ
                (f′ 𝒟.∘
                 DispIso.inv
                 (subst (λ x → DispIso x X (transport refl X)) (transportRefl _)
                  (J (M.P₁ refl (toPathP refl)) (M.base₁ refl (toPathP refl)) w))))
             (sym (PathPConv.fromTo {A = λ _ → 𝒟.Ob A} refl)) ⟩
          subst (λ x → 𝒟.Hom x (transport refl X) Y) 𝒞.identʳ
            (f′ 𝒟.∘ DispIso.inv (subst (λ x → DispIso x X (transport refl X)) (transportRefl _) (J (M.P₁ refl (toPathP refl)) (M.base₁ refl (toPathP refl)) (fromPathP {A = λ _ → 𝒟.Ob A} (toPathP refl)))))
        ≡⟨ refl ⟩
          subst (λ x → 𝒟.Hom x (transport refl X) Y) 𝒞.identʳ
            (f′ 𝒟.∘ DispIso.inv (subst (λ x → DispIso x X (transport refl X)) (transportRefl _) (idToDispIso refl (toPathP refl))))
        ≡⟨ refl ⟩
          subst (λ x → 𝒟.Hom x (transport refl X) Y) 𝒞.identʳ (f′ 𝒟.∘ DispIso.inv (idToVertIso (toPathP refl)))
        ∎

  isUnivDisplayed : Type (ℓ-max (ℓ-max o o′) h′)
  isUnivDisplayed = ∀ {A B : 𝒞.Ob} (p : A ≡ B) {X : 𝒟.Ob A} {Y : 𝒟.Ob B} → isEquiv (λ (p′ : PathP (λ i → 𝒟.Ob (p i)) X Y) → idToDispIso p p′)

  isPropIsUnivDisplayed : isProp isUnivDisplayed
  isPropIsUnivDisplayed = isPropImplicitΠ2 λ A B → isPropΠ λ p → isPropImplicitΠ2 (λ X Y → isPropIsEquiv (idToDispIso p))

  dispIsoToId : isUnivDisplayed
    → ∀ {A B}
    → (p : A ≡ B)
    → ∀ {X Y}
    → DispIso (idToIso 𝒞 p) X Y
    → PathP (λ i → 𝒟.Ob (p i)) X Y
  dispIsoToId u p = invIsEq (u p)

  vertIsoToId : isUnivDisplayed
    → ∀ {A} {X Y : 𝒟.Ob A}
    → VertIso X Y
    → X ≡ Y
  vertIsoToId u {A} {X} {Y} iso = dispIsoToId u refl (subst (λ x → DispIso x X Y) (sym (transportRefl _)) iso)

  idToVertIso∘vertIsoToId≡id : (u : isUnivDisplayed)
    → ∀ {A} {X Y : 𝒟.Ob A} (iso : VertIso X Y)
    → idToVertIso (vertIsoToId u iso) ≡ iso
  idToVertIso∘vertIsoToId≡id u {A} {X} {Y} iso =
      idToVertIso (vertIsoToId u iso)
    ≡⟨ refl ⟩
      idToVertIso (dispIsoToId u refl (subst (λ x → DispIso x X Y) (sym (transportRefl _)) iso))
    ≡⟨ refl ⟩
      subst (λ x → DispIso x X Y) (transportRefl _)
        (idToDispIso refl (dispIsoToId u refl (subst (λ x → DispIso x X Y) (sym (transportRefl _)) iso)))
    ≡⟨ cong (subst (λ x → DispIso x X Y) (transportRefl _)) (p _) ⟩
      subst (λ x → DispIso x X Y) (transportRefl _)
        (subst (λ x → DispIso x X Y) (sym (transportRefl _)) iso)
    ≡⟨ transportTransport⁻ (λ i → DispIso (transportRefl _ i) X Y) iso ⟩
      iso
    ∎
    where
      p : ∀ xx → idToDispIso refl (dispIsoToId u refl xx) ≡ xx
      p = secIsEq (u (λ _ → A) {X = X} {Y = Y})
