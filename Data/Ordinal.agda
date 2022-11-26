module Data.Ordinal where

open import Cubical.Core.Everything
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Structure
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Univalence
open import Cubical.HITs.PropositionalTruncation
open import Cubical.Relation.Nullary using (¬_)
open import Cubical.Reflection.RecordEquiv
open import Cubical.Data.Sigma
open import Cubical.Data.Empty as ⊥
open import Cubical.Data.Sum
open import Cubical.Data.Nat
import Cubical.Data.Nat.Order as Nat

module Misc where
  private
    variable
      ℓ ℓ′ ℓ″ : Level

  Power : Type ℓ → ∀ ℓ₁ → Type (ℓ-max ℓ (ℓ-suc ℓ₁))
  Power A ℓ₁ = A → hProp ℓ₁

  Image : ∀ {A : hSet ℓ} {B : hSet ℓ′} → (P : Power (typ A) ℓ″) → ((a : typ A) → typ (P a) → typ B) → ∀ (y : typ B) → Type (ℓ-max ℓ (ℓ-max ℓ′ ℓ″))
  Image {A = A , _} {B = B , _} P f y = ∥ (Σ[ x ∈ A ] Σ[ Px ∈ typ (P x) ] (f x Px ≡ y)) ∥

module _ {ℓ} (A : Type ℓ) (isSetA : isSet A) {ℓ′} (_<_ : A → A → Type ℓ′) (isProp< : ∀ a b → isProp (a < b)) where
  data isAcc (a : A) : Type (ℓ-max ℓ ℓ′) where
    acc< : (∀ b → b < a → isAcc b) → isAcc a

  isPropIsAcc : ∀ a → isProp (isAcc a)
  isPropIsAcc a (acc< h₁) (acc< h₂) = cong acc< p
    where
      k₁ : ∀ b (l : b < a) (t : isAcc b) → h₁ b l ≡ t
      k₁ b l = isPropIsAcc b (h₁ b l)

      p : h₁ ≡ h₂
      p = funExt λ b → funExt λ l → k₁ b l (h₂ b l)

  indIsAcc : ∀ {ℓ₁} (P : (a : A) → isAcc a → Type ℓ₁)
    → (f : ∀ a (h : ∀ b → b < a → isAcc b) → (∀ b → (l : b < a) → P b (h b l)) → P a (acc< h))
    → ∀ a (c : isAcc a)
    → P a c
  indIsAcc P f a (acc< h) = f a h λ b l → indIsAcc P f b (h b l)

  simpleInd : ∀ {ℓ₁} (P : A → Type ℓ₁)
    → (f : ∀ a → (∀ b → b < a → isAcc b × P b) → P a)
    → ∀ a (c : isAcc a)
    → P a
  simpleInd {ℓ₁} P f a c = indIsAcc Q g a c
    where
      Q : (a : A) → isAcc a → Type ℓ₁
      Q a _ = P a

      g : ∀ a (h : ∀ b → b < a → isAcc b) → (∀ b → (l : b < a) → P b) → P a
      g a h k = f a λ b l → h b l , k b l

  isWellFounded : Type (ℓ-max ℓ ℓ′)
  isWellFounded = ∀ a → isAcc a

  isPropIsWellFounded : isProp isWellFounded
  isPropIsWellFounded = isPropΠ isPropIsAcc

  wfInd : isWellFounded → ∀ {ℓ₁} (P : A → Type ℓ₁) → (∀ a → (∀ b → (b < a) → P b) → P a) → ∀ a → P a
  wfInd wf P f a = k a (wf a)
    where
      k : ∀ a → (c : isAcc a) → P a
      k = simpleInd P λ a₁ x → f a₁ (λ b l → x b l .snd)

  open Misc

  defByWF : isWellFounded → ∀ {ℓ₁} (B : Type ℓ₁) → isSet B → (g : ∀ {ℓ₂} → Power B ℓ₂ → B) → A → B
  defByWF wf B isSetB g = λ a → f′ a (wf a)
    where
      P : ∀ a → Power A ℓ′
      P a a′ = a′ < a , isProp< _ _

      f′ : ∀ a (s : isAcc a) → B
      f′ a (acc< s) = g λ b → Image {A = A , isSetA} {B = B , isSetB} (P a) (λ a′ l → f′ a′ (s a′ l)) b , isPropPropTrunc

  record isExtensional : Type (ℓ-max ℓ (ℓ-suc ℓ′)) where
    field
      wf : isWellFounded
      ext : ∀ a b → (∀ c → c < a ≡ c < b) → a ≡ b

  unquoteDecl isExtensionalIsoΣ = declareRecordIsoΣ isExtensionalIsoΣ (quote isExtensional)

  isPropIsExtensional : isProp isExtensional
  isPropIsExtensional = subst isProp (sym (isoToPath isExtensionalIsoΣ)) (isPropΣ isPropIsWellFounded λ _ → isPropΠ3 λ _ _ _ → isSetA _ _)

record ExtRel {ℓ} (A : Type ℓ) (isSetA : isSet A) ℓ′ : Type (ℓ-max ℓ (ℓ-suc ℓ′)) where
  field
    _<_ : A → A → Type ℓ′
    isProp< : ∀ a b → isProp (a < b)
    is-extensional : isExtensional A isSetA _<_ isProp<

record Ordinal ℓ ℓ′ : Type (ℓ-suc (ℓ-max ℓ ℓ′)) where
  field
    A : Type ℓ
    isSetA : isSet A
    ext-rel : ExtRel A isSetA ℓ′
  open ExtRel ext-rel public

  field
    transitive : ∀ a b c → a < b → b < c → a < c

ω : Ordinal ℓ-zero ℓ-zero
ω = record
  { A = ℕ
  ; isSetA = isSetℕ
  ; ext-rel = record
    { _<_ = Nat._<_
    ; isProp< = λ _ _ → Nat.m≤n-isProp
    ; is-extensional = record { wf = ℕwf ; ext = ℕext }
    }
  ; transitive = λ _ _ _ → Nat.<-trans
  }
  where
    ℕext : (a b : ℕ) → ((c : ℕ) → (c Nat.< a) ≡ (c Nat.< b)) → a ≡ b
    ℕext zero zero f = refl
    ℕext zero (suc b) f = ⊥.rec (subst ¬_ (f 0) Nat.¬-<-zero (Nat.suc-≤-suc Nat.zero-≤))
    ℕext (suc a) zero f = ⊥.rec (subst ¬_ (sym (f 0)) Nat.¬-<-zero (Nat.suc-≤-suc Nat.zero-≤))
    ℕext (suc a) (suc b) f = cong suc
      ( ℕext a b λ c → hPropExt Nat.m≤n-isProp Nat.m≤n-isProp
          (λ x → Nat.pred-≤-pred (transport (f (suc c)) (Nat.suc-≤-suc x)))
          (λ x → Nat.pred-≤-pred (transport (sym (f (suc c))) (Nat.suc-≤-suc x)))
      )

    ℕwf : ∀ n → isAcc ℕ isSetℕ Nat._<_ (λ _ _ → Nat.m≤n-isProp) n
    ℕwf zero = acc< λ m l → ⊥.rec (Nat.¬-<-zero l)
    ℕwf (suc n) = acc< u
      where
        isAcc-n : isAcc ℕ isSetℕ Nat._<_ (λ _ _ → Nat.m≤n-isProp) n
        isAcc-n = ℕwf n

        u : ∀ m (l : m Nat.< suc n) → isAcc ℕ isSetℕ Nat._<_ (λ _ _ → Nat.m≤n-isProp) m
        u m l with Nat.<-split l | isAcc-n
        ... | inl m<n | acc< t = t m m<n
        ... | inr p | _ = subst (isAcc ℕ isSetℕ Nat._<_ (λ _ _ → Nat.m≤n-isProp)) (sym p) isAcc-n
