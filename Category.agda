module Category where

open import Cubical.Core.Everything
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.Transport
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels
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

isSetisProp⇒isSetΣ : ∀ {ℓ} {A : Type ℓ} {ℓ′} {B : A → Type ℓ′}
  → isSet A → (∀ a → isProp (B a)) → isSet (Σ A B)
isSetisProp⇒isSetΣ isSetA isPropB u v p q = p≡q
  where
    H : (u ≡ v) ≃ (u .fst ≡ v .fst)
    H = cong fst , isEmbeddingFstΣProp isPropB

    h : cong fst p ≡ cong fst q
    h = isSetA (fst u) (fst v) (cong fst p) (cong fst q)

    x : isContr (fiber (cong fst) (cong fst p))
    x = H .snd .equiv-proof (cong fst p)

    r : u ≡ v
    r = x .fst .fst

    y : cong fst r ≡ cong fst p
    y = x .fst .snd

    z : ∀ (fib : fiber (cong fst) (cong fst p)) → (r , y) ≡ fib
    z = x .snd

    z1 : Path (fiber (cong fst) (cong fst p)) (r , y) (p , refl)
    z1 = z (p , refl)

    z2 : Path (fiber (cong fst) (cong fst p)) (r , y) (q , sym h)
    z2 = z (q , sym h)

    z3 : Path (fiber (cong fst) (cong fst p)) (p , refl) (q , sym h)
    z3 = sym z1 ∙ z2

    p≡q : p ≡ q
    p≡q = cong fst z3

module _ {o h} (𝒞 : Category o h) where
  open Category 𝒞

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

  isoId : ∀ {A} → Iso A A
  isoId = record { f = id ; is-iso = isIsoId }

  helper3 : ∀ {A B} → Iso A B ≡ (Σ[ f ∈ Hom A B ] isIso f)
  helper3 = ua ((λ x → (Iso.f x) , Iso.is-iso x) , record { equiv-proof = λ y → (record { f = fst y ; is-iso = snd y } , refl) , λ where (z , e) i → record { f = fst (e (~ i)) ; is-iso = snd (e (~ i)) } , λ j → fst (e (~ i ∨ j)) , snd (e (~ i ∨ j)) })

  isSetIso : ∀ A B → isSet (Iso A B)
  isSetIso A B  = subst isSet (sym helper3) (isSetisProp⇒isSetΣ isSetHom isPropIsIso)

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

record UnivCategory o h : Type (ℓ-suc (ℓ-max o h)) where
  field
    𝒞 : Category o h
    is-univ-category : isUnivCategory 𝒞
