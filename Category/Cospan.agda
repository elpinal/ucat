module Category.Cospan where

open import Cubical.Core.Everything
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Transport
open import Cubical.Relation.Nullary
open import Cubical.Data.Unit
open import Cubical.Data.Empty using (⊥) renaming (rec to ⊥-rec)

open import Category

private
  variable ℓ : Level

data cospanOb : Type ℓ-zero where
  X Y apex : cospanOb

rec : ∀ {A : Type ℓ} → A → A → A → cospanOb → A
rec x y a X = x
rec x y a Y = y
rec x y a apex = a

discreteCospanOb : Discrete cospanOb
discreteCospanOb X X = yes refl
discreteCospanOb X Y = no (λ p → subst (rec Unit ⊥ Unit) p tt)
discreteCospanOb X apex = no (λ p → subst (rec Unit Unit ⊥) p tt)
discreteCospanOb Y X = no (λ p → subst (rec ⊥ Unit Unit) p tt)
discreteCospanOb Y Y = yes refl
discreteCospanOb Y apex = no (λ p → subst (rec Unit Unit ⊥) p tt)
discreteCospanOb apex X = no (λ p → subst (rec ⊥ Unit Unit) p tt)
discreteCospanOb apex Y = no (λ p → subst (rec Unit ⊥ Unit) p tt)
discreteCospanOb apex apex = yes refl

isSetCospanOb : isSet cospanOb
isSetCospanOb = Discrete→isSet discreteCospanOb

data cospanHom : cospanOb → cospanOb → Type ℓ-zero where
  X→apex : cospanHom X apex
  Y→apex : cospanHom Y apex
  id : {A B : cospanOb} → (p : A ≡ B) → cospanHom A B

discreteCospanHom : ∀ {A B} → Discrete (cospanHom A B)
discreteCospanHom X→apex X→apex = yes refl
discreteCospanHom X→apex (id p) = ⊥-rec (subst (rec Unit Unit ⊥) p tt)
discreteCospanHom Y→apex Y→apex = yes refl
discreteCospanHom Y→apex (id p) = ⊥-rec (subst (rec Unit Unit ⊥) p tt)
discreteCospanHom (id p) X→apex = ⊥-rec (subst (rec Unit Unit ⊥) p tt)
discreteCospanHom (id p) Y→apex = ⊥-rec (subst (rec Unit Unit ⊥) p tt)
discreteCospanHom (id p) (id q) = yes (λ i → id (isSetCospanOb _ _ p q i))

isSetCospanHom : ∀ {A B} → isSet (cospanHom A B)
isSetCospanHom = Discrete→isSet discreteCospanHom

composeCospanHom : ∀ {A B C} → cospanHom B C → cospanHom A B → cospanHom A C
composeCospanHom X→apex (id p) = subst⁻ (λ x → cospanHom x apex) p X→apex
composeCospanHom Y→apex (id p) = subst⁻ (λ x → cospanHom x apex) p Y→apex
composeCospanHom (id p) f = subst (cospanHom _) p f

identʳ-composeCospanHom : ∀ {A B} (f : cospanHom A B)
  → composeCospanHom f (id refl) ≡ f
identʳ-composeCospanHom X→apex = transportRefl _
identʳ-composeCospanHom Y→apex = transportRefl _
identʳ-composeCospanHom {A = A} (id p) = J P (transportRefl _) p
  where
    P : ∀ C (q : A ≡ C) → Type ℓ-zero
    P C q = subst (cospanHom A) q (id refl) ≡ id q

assoc-composeCospanHom : ∀ {A B C D} (f : cospanHom A B) g (h : cospanHom C D)
  → composeCospanHom (composeCospanHom h g) f
  ≡ composeCospanHom h (composeCospanHom g f)
assoc-composeCospanHom {A} {B} f (id p) X→apex = J P base (sym p) f
  where
    P : ∀ y (q : X ≡ y) → Type ℓ-zero
    P y q = ∀ (f : cospanHom A y) → composeCospanHom (subst⁻ (λ x → cospanHom x apex) (sym q) X→apex) f
              ≡ composeCospanHom X→apex (subst (cospanHom A) (sym q) f)
    base : P X refl
    base f =
        composeCospanHom (subst (λ x → cospanHom x apex) refl X→apex) f
      ≡⟨ cong (λ w → composeCospanHom w f) (transportRefl X→apex) ⟩
        composeCospanHom X→apex f
      ≡⟨ sym (cong (composeCospanHom X→apex) (transportRefl f)) ⟩
        composeCospanHom X→apex (subst (cospanHom A) refl f)
      ∎
assoc-composeCospanHom {A} {B} f (id p) Y→apex = J P base (sym p) f
  where
    P : ∀ y (q : Y ≡ y) → Type ℓ-zero
    P y q = ∀ (f : cospanHom A y) → composeCospanHom (subst⁻ (λ x → cospanHom x apex) (sym q) Y→apex) f
              ≡ composeCospanHom Y→apex (subst (cospanHom A) (sym q) f)
    base : P Y refl
    base f =
        composeCospanHom (subst (λ x → cospanHom x apex) refl Y→apex) f
      ≡⟨ cong (λ w → composeCospanHom w f) (transportRefl Y→apex) ⟩
        composeCospanHom Y→apex f
      ≡⟨ sym (cong (composeCospanHom Y→apex) (transportRefl f)) ⟩
        composeCospanHom Y→apex (subst (cospanHom A) refl f)
      ∎
{-# CATCHALL #-}
assoc-composeCospanHom {C = C} f g (id p) = J P base p
  where
    P : ∀ y (q : C ≡ y) → Type ℓ-zero
    P y q = composeCospanHom (composeCospanHom (id q) g) f
            ≡ composeCospanHom (id q) (composeCospanHom g f)
    base : P C refl
    base =
        composeCospanHom (composeCospanHom (id refl) g) f
      ≡⟨ cong (λ w → composeCospanHom w f) (transportRefl g) ⟩
        composeCospanHom g f
      ≡⟨ sym (transportRefl (composeCospanHom g f)) ⟩
        composeCospanHom (id refl) (composeCospanHom g f)
      ∎

Cospan : Category ℓ-zero ℓ-zero
Cospan = record
           { Ob = cospanOb
           ; Hom = cospanHom
           ; isSetHom = isSetCospanHom
           ; id = id refl
           ; _∘_ = composeCospanHom
           ; identˡ = transportRefl _
           ; identʳ = identʳ-composeCospanHom _
           ; ident² = transportRefl _
           ; assoc = λ { {f = f} {h = h} → assoc-composeCospanHom f _ h }
           }
