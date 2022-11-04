module Fibration where

open import Cubical.Core.Everything
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Transport
open import Cubical.Foundations.HLevels

open import Category
open import Displayed

module _ {o h} {𝒞 : Category o h} {o₁ h₁} (𝒟 : Displayed 𝒞 o₁ h₁) where
  private
    module 𝒞 = Category.Category 𝒞
    module 𝒟 = Displayed.Displayed 𝒟

  record Factorization {A B} {f : 𝒞 [ A , B ]} {X Y} (f′ : 𝒟.Hom f X Y) {C} (g : 𝒞 [ C , A ]) {Z : 𝒟.Ob C} (h′ : 𝒟.Hom (𝒞 [ f ∘ g ]) Z Y) : Type h₁ where
    field
      g′ : 𝒟.Hom g Z X
      factorize : f′ 𝒟.∘ g′ ≡ h′
      unique : ∀ g″ → f′ 𝒟.∘ g″ ≡ h′ → g′ ≡ g″

    unique₂ : ∀ g₁ g₂ → f′ 𝒟.∘ g₁ ≡ h′ → f′ 𝒟.∘ g₂ ≡ h′ → g₁ ≡ g₂
    unique₂ g₁ g₂ p q = sym (unique g₁ p) ∙ unique g₂ q

  record isCartesian {A B} {f : 𝒞 [ A , B ]} {X Y} (f′ : 𝒟.Hom f X Y) : Type (ℓ-max o (ℓ-max h (ℓ-max o₁ h₁))) where
    field
      univ-prop : ∀ {C} (g : 𝒞 [ C , A ]) {Z : 𝒟.Ob C} (h′ : 𝒟.Hom (𝒞 [ f ∘ g ]) Z Y) → Factorization f′ g h′

  record cartesianLift {A B} (f : 𝒞 [ A , B ]) (Y : 𝒟.Ob B) : Type (ℓ-max o (ℓ-max h (ℓ-max o₁ h₁))) where
    field
      X : 𝒟.Ob A
      f′ : 𝒟.Hom f X Y
      is-cartesian : isCartesian f′

  record Cleaving : Type (ℓ-max o (ℓ-max h (ℓ-max o₁ h₁))) where
    field
      cartesian-lift : ∀ {A B} (f : 𝒞 [ A , B ]) (Y : 𝒟.Ob B) → cartesianLift f Y

  isPropFactorization : ∀ {A B} {f : 𝒞 [ A , B ]}
    {X Y} {f′ : 𝒟.Hom f X Y}
    {C} {g : 𝒞 [ C , A ]}
    {Z} {h′ : 𝒟.Hom (𝒞 [ f ∘ g ]) Z Y}
    → isProp (Factorization f′ g h′)
  isPropFactorization {f′ = f′} {h′ = h′} F G i = record
    { g′ = F.unique G.g′ G.factorize i
    ; factorize = p i
    ; unique = λ g″ x → q g″ x i
    }
    where
      module F = Factorization F
      module G = Factorization G

      p : PathP (λ i → f′ 𝒟.∘ F.unique G.g′ G.factorize i ≡ h′) F.factorize G.factorize
      p = toPathP (𝒟.isSetHom _ _ _ _)

      q : ∀ g″ x → PathP (λ i → F.unique G.g′ G.factorize i ≡ g″) (F.unique g″ x) (G.unique g″ x)
      q g″ x = toPathP (𝒟.isSetHom _ _ _ _)

  isPropIsCartesian : ∀ {A B} {f : 𝒞 [ A , B ]}
    {X Y} {f′ : 𝒟.Hom f X Y}
    → isProp (isCartesian f′)
  isPropIsCartesian x y i .isCartesian.univ-prop =
    isPropΠ (λ g → isPropImplicitΠ λ Z → isPropΠ λ h′ → isPropFactorization)
      (isCartesian.univ-prop x)
      (isCartesian.univ-prop y)
      i

  module CartesianLiftUnique {A B} (f : 𝒞 [ A , B ]) (Y : 𝒟.Ob B) (L : cartesianLift f Y) (L′ : cartesianLift f Y) where
    private
      module L = cartesianLift L
      module L′ = cartesianLift L′

    c : Factorization L.f′ 𝒞.id (subst (λ x → 𝒟.Hom x _ _) (sym 𝒞.identʳ) L′.f′)
    c = isCartesian.univ-prop L.is-cartesian 𝒞.id (subst (λ x → 𝒟.Hom x _ _) (sym 𝒞.identʳ) L′.f′)

    k : 𝒟.Hom 𝒞.id L′.X L.X
    k = Factorization.g′ c


    c′ : Factorization L′.f′ 𝒞.id (subst (λ x → 𝒟.Hom x _ _) (sym 𝒞.identʳ) L.f′)
    c′ = isCartesian.univ-prop L′.is-cartesian 𝒞.id (subst (λ x → 𝒟.Hom x _ _) (sym 𝒞.identʳ) L.f′)

    k′ : 𝒟.Hom 𝒞.id L.X L′.X
    k′ = Factorization.g′ c′


    t1 : L.f′ 𝒟.∘ k ≡ transport (λ i → 𝒟.Hom (𝒞.identʳ {f = f} (~ i)) L′.X Y) L′.f′
    t1 = Factorization.factorize c

    t2 : L′.f′ 𝒟.∘ k′ ≡ transport (λ i → 𝒟.Hom (𝒞.identʳ {f = f} (~ i)) L.X Y) L.f′
    t2 = Factorization.factorize c′


    u : (L′.f′ 𝒟.∘ subst (λ x → 𝒟.Hom x L′.X L′.X) 𝒞.identˡ (k′ 𝒟.∘ k))
      ≡ subst (λ x → 𝒟.Hom x L′.X Y) (sym 𝒞.identʳ) L′.f′
    u =
        (L′.f′ 𝒟.∘ subst (λ x → 𝒟.Hom x L′.X L′.X) 𝒞.identˡ (k′ 𝒟.∘ k))
      ≡⟨ hoist-substʳ 𝒟 𝒞.identˡ ⟩
        subst (λ x → 𝒟.Hom x L′.X Y) (cong (f 𝒞.∘_) 𝒞.identˡ) (L′.f′ 𝒟.∘ (k′ 𝒟.∘ k))
      ≡⟨ cong (subst (λ x → 𝒟.Hom x L′.X Y) (cong (f 𝒞.∘_) 𝒞.identˡ)) (sym (fromPathP 𝒟.assoc)) ⟩
        subst (λ x → 𝒟.Hom x L′.X Y) (cong (f 𝒞.∘_) 𝒞.identˡ) (subst (λ x → 𝒟.Hom x L′.X Y) 𝒞.assoc ((L′.f′ 𝒟.∘ k′) 𝒟.∘ k))
      ≡⟨ sym (substComposite (λ x → 𝒟.Hom x L′.X Y) _ _ _ ) ⟩
        subst (λ x → 𝒟.Hom x L′.X Y) (𝒞.assoc ∙ cong (f 𝒞.∘_) 𝒞.identˡ) ((L′.f′ 𝒟.∘ k′) 𝒟.∘ k)
      ≡⟨ cong
           (λ y →
              subst (λ x → 𝒟.Hom x L′.X Y) (𝒞.assoc ∙ cong (f 𝒞.∘_) 𝒞.identˡ)
              (y 𝒟.∘ k))
           t2 ⟩
        subst (λ x → 𝒟.Hom x L′.X Y) (𝒞.assoc ∙ cong (f 𝒞.∘_) 𝒞.identˡ) ((subst (λ x → 𝒟.Hom x L.X Y) (sym 𝒞.identʳ) L.f′) 𝒟.∘ k)
      ≡⟨ cong
           (subst (λ x → 𝒟.Hom x L′.X Y) (𝒞.assoc ∙ cong (f 𝒞.∘_) 𝒞.identˡ)) (hoist-substˡ 𝒟 _) ⟩
        subst (λ x → 𝒟.Hom x L′.X Y) (𝒞.assoc ∙ cong (f 𝒞.∘_) 𝒞.identˡ) (subst (λ x → 𝒟.Hom x L′.X Y) (cong (𝒞._∘ 𝒞.id) (sym 𝒞.identʳ)) (L.f′ 𝒟.∘ k))
      ≡⟨ sym (substComposite (λ x → 𝒟.Hom x L′.X Y) _ _ _) ⟩
        subst (λ x → 𝒟.Hom x L′.X Y) ((cong (𝒞._∘ 𝒞.id) (sym 𝒞.identʳ)) ∙ (𝒞.assoc ∙ cong (f 𝒞.∘_) 𝒞.identˡ)) (L.f′ 𝒟.∘ k)
      ≡⟨ cong (λ y → subst (λ x → 𝒟.Hom x L′.X Y) y (L.f′ 𝒟.∘ k)) (𝒞.isSetHom _ _ _ _) ⟩
        subst (λ x → 𝒟.Hom x L′.X Y) refl (L.f′ 𝒟.∘ k)
      ≡⟨ transportRefl _ ⟩
        L.f′ 𝒟.∘ k
      ≡⟨ t1 ⟩
        subst (λ x → 𝒟.Hom x L′.X Y) (sym 𝒞.identʳ) L′.f′
      ∎

    v : (L.f′ 𝒟.∘ subst (λ x → 𝒟.Hom x L.X L.X) 𝒞.identʳ (k 𝒟.∘ k′))
      ≡ subst (λ x → 𝒟.Hom x L.X Y) (sym 𝒞.identʳ) L.f′
    v =
        (L.f′ 𝒟.∘ subst (λ x → 𝒟.Hom x L.X L.X) 𝒞.identʳ (k 𝒟.∘ k′))
      ≡⟨ hoist-substʳ 𝒟 𝒞.identʳ ⟩
        subst (λ x → 𝒟.Hom x L.X Y) (cong (f 𝒞.∘_) 𝒞.identʳ) (L.f′ 𝒟.∘ (k 𝒟.∘ k′))
      ≡⟨ cong (subst (λ x → 𝒟.Hom x L.X Y) (cong (f 𝒞.∘_) 𝒞.identʳ)) (sym (fromPathP 𝒟.assoc)) ⟩
        subst (λ x → 𝒟.Hom x L.X Y) (cong (f 𝒞.∘_) 𝒞.identʳ) (subst (λ x → 𝒟.Hom x L.X Y) 𝒞.assoc ((L.f′ 𝒟.∘ k) 𝒟.∘ k′))
      ≡⟨ sym (substComposite (λ x → 𝒟.Hom x L.X Y) _ _ _) ⟩
        subst (λ x → 𝒟.Hom x L.X Y) (𝒞.assoc ∙ cong (f 𝒞.∘_) 𝒞.identʳ) ((L.f′ 𝒟.∘ k) 𝒟.∘ k′)
      ≡⟨ cong
           (λ y →
              subst (λ x → 𝒟.Hom x L.X Y) (𝒞.assoc ∙ cong (f 𝒞.∘_) 𝒞.identʳ)
              (y 𝒟.∘ k′))
           t1 ⟩
        subst (λ x → 𝒟.Hom x L.X Y) (𝒞.assoc ∙ cong (f 𝒞.∘_) 𝒞.identʳ) ((subst (λ x → 𝒟.Hom x L′.X Y) (sym 𝒞.identʳ) L′.f′) 𝒟.∘ k′)
      ≡⟨ cong
           (subst (λ x → 𝒟.Hom x L.X Y) (𝒞.assoc ∙ cong (f 𝒞.∘_) 𝒞.identʳ)) (hoist-substˡ 𝒟 (sym 𝒞.identʳ)) ⟩
        subst (λ x → 𝒟.Hom x L.X Y) (𝒞.assoc ∙ cong (f 𝒞.∘_) 𝒞.identʳ) (subst (λ x → 𝒟.Hom x L.X Y) (cong (𝒞._∘ 𝒞.id) (sym 𝒞.identʳ)) (L′.f′ 𝒟.∘ k′))
      ≡⟨ sym (substComposite (λ x → 𝒟.Hom x L.X Y) _ _ _) ⟩
        subst (λ x → 𝒟.Hom x L.X Y) ((cong (𝒞._∘ 𝒞.id) (sym 𝒞.identʳ)) ∙ (𝒞.assoc ∙ cong (f 𝒞.∘_) 𝒞.identʳ)) (L′.f′ 𝒟.∘ k′)
      ≡⟨ cong (λ y → subst (λ x → 𝒟.Hom x L.X Y) y (L′.f′ 𝒟.∘ k′)) (𝒞.isSetHom _ _ _ _) ⟩
        subst (λ x → 𝒟.Hom x L.X Y) refl (L′.f′ 𝒟.∘ k′)
      ≡⟨ transportRefl _ ⟩
        L′.f′ 𝒟.∘ k′
      ≡⟨ t2 ⟩
        subst (λ x → 𝒟.Hom x L.X Y) (sym 𝒞.identʳ) L.f′
      ∎


    cc : Factorization L′.f′ 𝒞.id (subst (λ x → 𝒟.Hom x _ _) (sym 𝒞.identʳ) L′.f′)
    cc = isCartesian.univ-prop L′.is-cartesian 𝒞.id (subst (λ x → 𝒟.Hom x _ _) (sym 𝒞.identʳ) L′.f′)

    p : subst (λ x → 𝒟.Hom x L′.X L′.X) (isIso.isoˡ (Iso.is-iso (isoId 𝒞))) (k′ 𝒟.∘ k) ≡ 𝒟.id
    p = Factorization.unique₂ cc (subst (λ x → 𝒟.Hom x L′.X L′.X) (isIso.isoˡ (Iso.is-iso (isoId 𝒞))) (k′ 𝒟.∘ k)) 𝒟.id
      u
      (sym (fromPathP (symP (𝒟.identʳ))))

    cc′ : Factorization L.f′ 𝒞.id (subst (λ x → 𝒟.Hom x _ _) (sym 𝒞.identʳ) L.f′)
    cc′ = isCartesian.univ-prop L.is-cartesian 𝒞.id (subst (λ x → 𝒟.Hom x _ _) (sym 𝒞.identʳ) L.f′)

    q : subst (λ x → 𝒟.Hom x L.X L.X) (isIso.isoʳ (Iso.is-iso (isoId 𝒞))) (k 𝒟.∘ k′) ≡ 𝒟.id
    q = Factorization.unique₂ cc′ (subst (λ x → 𝒟.Hom x L.X L.X) (isIso.isoʳ (Iso.is-iso (isoId 𝒞))) (k 𝒟.∘ k′)) 𝒟.id
      v
      (sym (fromPathP (symP (𝒟.identʳ))))

    cartesianLiftDomainVertIso : VertIso 𝒟 L.X L′.X
    cartesianLiftDomainVertIso = record { f′ = k′ ; is-disp-iso = record { inv = k ; isoˡ = toPathP p ; isoʳ = toPathP q } }

    cartesianLiftDomainUnique : isUnivDisplayed 𝒟 → L.X ≡ L′.X
    cartesianLiftDomainUnique u = vertIsoToId 𝒟 u cartesianLiftDomainVertIso

    triangle1 : PathP (λ i → 𝒟.Hom (𝒞.identʳ {f = f} i) L.X Y) (L′.f′ 𝒟.∘ k′) L.f′
    triangle1 = symP {A = (λ i → 𝒟.Hom (𝒞.identʳ {f = f} (~ i)) L.X Y)} (toPathP (sym t2))

    triangle2 : PathP (λ i → 𝒟.Hom (𝒞.identʳ {f = f} i) L′.X Y) (L.f′ 𝒟.∘ k) L′.f′
    triangle2 = symP {A = (λ i → 𝒟.Hom (𝒞.identʳ {f = f} (~ i)) L′.X Y)} (toPathP (sym t1))

    f′-unique : (u : isUnivDisplayed 𝒟) → PathP (λ i → 𝒟.Hom f (cartesianLiftDomainUnique u i) Y) L.f′ L′.f′
    f′-unique u = toPathP r
      where
        t : subst (λ x → 𝒟.Hom f x Y) (cartesianLiftDomainUnique u) L.f′
          ≡ subst (λ x → 𝒟.Hom x L′.X Y) 𝒞.identʳ (L.f′ 𝒟.∘ DispIso.inv (idToVertIso 𝒟 (cartesianLiftDomainUnique u)))
        t = vertIsoTriangle 𝒟 {f′ = L.f′} (cartesianLiftDomainUnique u)

        s : DispIso.inv (idToVertIso 𝒟 (cartesianLiftDomainUnique u)) ≡ k
        s =
            DispIso.inv (idToVertIso 𝒟 (vertIsoToId 𝒟 u cartesianLiftDomainVertIso))
          ≡⟨ cong DispIso.inv (idToVertIso∘vertIsoToId≡id 𝒟 u _) ⟩
            DispIso.inv cartesianLiftDomainVertIso
          ≡⟨ refl ⟩
            k
          ∎

        e : subst (λ x → 𝒟.Hom x L′.X Y) 𝒞.identʳ (L.f′ 𝒟.∘ DispIso.inv (idToVertIso 𝒟 (cartesianLiftDomainUnique u)))
          ≡ subst (λ x → 𝒟.Hom x L′.X Y) 𝒞.identʳ (L.f′ 𝒟.∘ k)
        e = cong (subst (λ x → 𝒟.Hom x L′.X Y) 𝒞.identʳ) (cong (L.f′ 𝒟.∘_) s)

        r : subst (λ x → 𝒟.Hom f x Y) (cartesianLiftDomainUnique u) L.f′ ≡ L′.f′
        r = t ∙∙ e ∙∙ fromPathP triangle2

    cartesianLiftUnique : isUnivDisplayed 𝒟 → L ≡ L′
    cartesianLiftUnique u i = record
      { X = cartesianLiftDomainUnique u i
      ; f′ = f′-unique u i
      ; is-cartesian = ic i
      }
      where
        ic : PathP (λ i → isCartesian (f′-unique u i)) L.is-cartesian L′.is-cartesian
        ic = toPathP (isPropIsCartesian _ _)

  open CartesianLiftUnique using (cartesianLiftDomainVertIso; cartesianLiftDomainUnique; cartesianLiftUnique) public

  isPropCartesianLift : isUnivDisplayed 𝒟 → ∀ {A B} (f : 𝒞 [ A , B ]) (Y : 𝒟.Ob B) → isProp (cartesianLift f Y)
  isPropCartesianLift u f Y L L′ = cartesianLiftUnique f Y L L′ u

  isPropCleaving : isUnivDisplayed 𝒟 → isProp Cleaving
  isPropCleaving u x y i .Cleaving.cartesian-lift f Y =
    isPropCartesianLift u f Y (x.cartesian-lift f Y) (y.cartesian-lift f Y) i
    where
      module x = Cleaving x
      module y = Cleaving y

record Fibration {o h} (𝒞 : Category.Category o h) o′ h′ : Type (ℓ-suc (ℓ-max o (ℓ-max h (ℓ-max o′ h′)))) where
  field
    𝒟 : Displayed 𝒞 o′ h′
    cleaving : Cleaving 𝒟
