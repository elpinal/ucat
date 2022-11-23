module Category where

open import Cubical.Core.Everything
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.Transport
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism using (isoToPath)
open import Cubical.Reflection.RecordEquiv
open import Cubical.Data.Sigma

record Category o h : Type (ℓ-suc (ℓ-max o h)) where
  field
    Ob : Type o
    Hom : ∀ (A B : Ob) → Type h
    isSetHom : ∀ {A B : Ob} → isSet (Hom A B)

    id : ∀ {A : Ob} → Hom A A
    _∘_ : ∀ {A B C : Ob} → Hom B C → Hom A B → Hom A C

    identˡ : ∀ {A B : Ob} {f : Hom A B} → id ∘ f ≡ f
    identʳ : ∀ {A B : Ob} {f : Hom A B} → f ∘ id ≡ f
    assoc : ∀ {A B C D : Ob} {f : Hom A B} {g : Hom B C} {h : Hom C D} → (h ∘ g) ∘ f ≡ h ∘ (g ∘ f)

  ident-unique : ∀ {A : Ob} → (p : id {A = A} ∘ id ≡ id) → p ≡ identˡ
  ident-unique p = isSetHom _ _ p _

_[_,_] : ∀ {o h} (𝒞 : Category o h) → Category.Ob 𝒞 → Category.Ob 𝒞 → Type h
𝒞 [ A , B ] = Category.Hom 𝒞 A B

_[_∘_] : ∀ {o h} (𝒞 : Category o h) {A B C : Category.Ob 𝒞} → 𝒞 [ B , C ] → 𝒞 [ A , B ] → 𝒞 [ A , C ]
𝒞 [ g ∘ f ] = Category._∘_ 𝒞 g f

module _ {o h} (𝒞 : Category o h) where
  open Category 𝒞

  -- TODO: Swap isoˡ and isoʳ.
  record isIso {A B : Ob} (f : Hom A B) : Type h where
    field
      inv : Hom B A
      isoˡ : f ∘ inv ≡ id
      isoʳ : inv ∘ f ≡ id

  isIsoId : ∀ {A} → isIso (id {A})
  isIsoId = record { inv = id ; isoˡ = identˡ ; isoʳ = identʳ }

  isPropIsIso : ∀ {A B} (f : Hom A B) → isProp (isIso f)
  isPropIsIso f x y i = record { inv = p i ; isoˡ = q i ; isoʳ = r i}
    where
      module x = isIso x
      module y = isIso y

      p : x.inv ≡ y.inv
      p =
          x.inv
        ≡⟨ sym identˡ ⟩
          id ∘ x.inv
        ≡⟨ cong (_∘ x.inv) (sym y.isoʳ) ⟩
          (y.inv ∘ f) ∘ x.inv
        ≡⟨ assoc ⟩
          y.inv ∘ (f ∘ x.inv)
        ≡⟨ cong (y.inv ∘_) x.isoˡ ⟩
          y.inv ∘ id
        ≡⟨ identʳ ⟩
          y.inv
        ∎

      q : PathP (λ i → f ∘ p i ≡ id) x.isoˡ y.isoˡ
      q = toPathP (isSetHom _ _ _ _)

      r : PathP (λ i → p i ∘ f ≡ id) x.isoʳ y.isoʳ
      r = toPathP (isSetHom _ _ _ _)

  record Iso (A B : Ob) : Type h where
    field
      f : Hom A B
      is-iso : isIso f

    inv = isIso.inv is-iso

  unquoteDecl IsoIsoΣ = declareRecordIsoΣ IsoIsoΣ (quote Iso)

  isoId : ∀ {A} → Iso A A
  isoId = record { f = id ; is-iso = isIsoId }

  isSetIso : ∀ A B → isSet (Iso A B)
  isSetIso A B = subst isSet (sym (isoToPath IsoIsoΣ)) (isSetΣSndProp isSetHom isPropIsIso)

  PathIso : ∀ {A B} (x y : Iso A B)
    → Iso.f x ≡ Iso.f y
    → x ≡ y
  PathIso {A} {B} x y p i = record
    { f = p i
    ; is-iso = isProp→PathP (λ i → isPropIsIso (p i)) (Iso.is-iso x) (Iso.is-iso y) i
    }

  idToIso : ∀ {A B} → A ≡ B → Iso A B
  idToIso {A} p = subst (Iso A) p isoId

{-
  isUnivCategory : Type (ℓ-max o h)
  isUnivCategory = ∀ {A : Ob} → isContr (Σ[ B ∈ Ob ] Iso A B)

  -- Being univalent is a mere proposition.
  isPropIsUnivCategory : isProp isUnivCategory
  isPropIsUnivCategory x y i = isPropIsContr x y i
-}

  isUnivCategory : Type (ℓ-max o h)
  isUnivCategory = ∀ {A B : Ob} → isEquiv (idToIso {A} {B})

  -- Being univalent is a mere proposition.
  isPropIsUnivCategory : isProp isUnivCategory
  isPropIsUnivCategory = isPropImplicitΠ2 (λ A B → isPropIsEquiv idToIso)

  isoToId : isUnivCategory → ∀ {A B} → Iso A B → A ≡ B
  isoToId u = invIsEq u

  lemmaIdToIso : ∀ {A A′ B B′ : Ob} → (p : A ≡ A′) → (q : B ≡ B′) → (f : Hom A B)
    → transport (λ i → Hom (p i) (q i)) f ≡ Iso.f (idToIso q) ∘ (f ∘ Iso.inv (idToIso p))
  lemmaIdToIso {A = A} {B = B} p q f = J P base q
    where
      Q : ∀ y (r : A ≡ y) → Type h
      Q y r = transport (λ i → Hom (r i) B) f ≡ Iso.f (idToIso refl) ∘ (f ∘ Iso.inv (idToIso r))

      base′ : transport refl f ≡ Iso.f (idToIso refl) ∘ (f ∘ Iso.inv (idToIso refl))
      base′ =
          transport refl f
        ≡⟨ transportRefl _ ⟩
          f
        ≡⟨ sym identʳ ⟩
          f ∘ id
        ≡⟨ cong (f ∘_) (sym (transportRefl _)) ⟩
          f ∘ transport refl id
        ≡⟨ sym identˡ ⟩
          id ∘ (f ∘ transport refl id)
        ≡⟨ cong (λ w → w ∘ (f ∘ transport refl id)) (sym (transportRefl _)) ⟩
          transport refl id ∘ (f ∘ transport refl id)
        ≡⟨ refl ⟩
          Iso.f (idToIso refl) ∘ (f ∘ Iso.inv (idToIso refl))
        ∎

      P : ∀ y (r : B ≡ y) → Type h
      P y r = transport (λ i → Hom (p i) (r i)) f ≡ Iso.f (idToIso r) ∘ (f ∘ Iso.inv (idToIso p))

      base : P B refl
      base = J Q base′ p

record UnivCategory o h : Type (ℓ-suc (ℓ-max o h)) where
  field
    𝒞 : Category o h
    is-univ-category : isUnivCategory 𝒞
