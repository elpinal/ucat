open import Category

module Limit.Pullback {o h} (𝒞 : Category o h) where

open import Cubical.Core.Everything
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Equiv
import Cubical.Foundations.Isomorphism as Isomorphism

open import Category.Cospan using (Cospan; X→apex; Y→apex; id; cospanOb; cospanHom)
open import Functor
open import NaturalTransformation
open import Limit Cospan 𝒞

private
  module 𝒞 = Category.Category 𝒞

open 𝒞

record ConeOverCospan (X : Ob) {A B C} (f : Hom A C) (g : Hom B C) : Type h where
  field
    p : Hom X A
    q : Hom X B
    commute : f ∘ p ≡ g ∘ q

toConeOverCospan : ∀ X (F : Functor Cospan 𝒞) → Cone⟨ X , F ⟩ → ConeOverCospan X (Functor.F₁ F X→apex) (Functor.F₁ F Y→apex)
toConeOverCospan X F α = record
  { p = α.component cospanOb.X
  ; q = α.component cospanOb.Y
  ; commute = sym (α.commute cospanOb.X cospanOb.apex) ∙ α.commute cospanOb.Y cospanOb.apex
  }
  where
    module α = NaturalTransformation.NaturalTransformation α

fromConeOverCospan : ∀ X (F : Functor Cospan 𝒞) → ConeOverCospan X (Functor.F₁ F X→apex) (Functor.F₁ F Y→apex) → Cone⟨ X , F ⟩
fromConeOverCospan X F c = record
  { component = component
  ; commute = λ A B → λ where
      {f = X→apex} → identʳ
      {f = Y→apex} → identʳ ∙ c.commute
      {f = id p} → identʳ ∙ J (P A) (base A) p
  }
  where
    module c = ConeOverCospan c
    module F = Functor.Functor F

    component = λ where
      cospanOb.X → c.p
      cospanOb.Y → c.q
      cospanOb.apex → F.₁ X→apex ∘ c.p

    P : ∀ A y (q : A ≡ y) → Type h
    P A y q = component y ≡ F.₁ (cospanHom.id q) ∘ component A

    base : ∀ A → P A A refl
    base A = sym (cong (_∘ component A) F.identity ∙ identˡ)

isEquivToConeOverCospan : ∀ X F → isEquiv (toConeOverCospan X F)
isEquivToConeOverCospan X F = Isomorphism.isoToIsEquiv (Isomorphism.iso (toConeOverCospan X F) (fromConeOverCospan X F) rInv lInv)
  where
    module F = Functor.Functor F

    rInv : ∀ c → toConeOverCospan X F (fromConeOverCospan X F c) ≡ c
    rInv c i = record { p = c.p ; q = c.q ; commute = commute i }
      where
        module c = ConeOverCospan c
        commute : PathP (λ i → F.₁ X→apex ∘ c.p ≡ F.₁ Y→apex ∘ c.q) (ConeOverCospan.commute (toConeOverCospan X F (fromConeOverCospan X F c))) c.commute
        commute = isSetHom (F.₁ X→apex ∘ c.p) (F.₁ Y→apex ∘ c.q) (ConeOverCospan.commute
                                                                (toConeOverCospan X F (fromConeOverCospan X F c))) c.commute
    lInv : ∀ α → fromConeOverCospan X F (toConeOverCospan X F α) ≡ α
    lInv α =
      componentEmbed _ α (funExt (λ where
        cospanOb.X → refl
        cospanOb.Y → refl
        cospanOb.apex → sym (NaturalTransformation.commute α cospanOb.X cospanOb.apex) ∙ identʳ
      ))

fromCospan : ∀ {A B C} (f : Hom A C) (g : Hom B C) → Functor Cospan 𝒞
fromCospan {A} {B} {C} f g = record
  { F₀ = z
  ; F₁ = k
  ; identity = λ {A = A′} → JRefl (λ y q → Hom (z A′) (z y)) 𝒞.id
  ; compose = λ { {f = f} {g = g} → compose g f }
  }
  where
    z = λ where
      cospanOb.X → A
      cospanOb.Y → B
      cospanOb.apex → C

    k : ∀ {x y} → cospanHom x y → Hom (z x) (z y)
    k = λ where
      X→apex → f
      Y→apex → g
      (id p) → J (λ y q → Hom (z _) (z y)) 𝒞.id p

    compose : ∀ {A B C} (g : cospanHom B C) (f : cospanHom A B) → k (Cospan [ g ∘ f ]) ≡ k g ∘ k f
    compose X→apex (id p) =
        J (λ y q → k (Cospan [ X→apex ∘ cospanHom.id (sym q) ]) ≡ f ∘ k (cospanHom.id (sym q))) ((cong (λ w → k w) (transportRefl X→apex) ∙ sym identʳ) ∙ sym (cong (f ∘_) (JRefl (λ y q → Hom (z cospanOb.X) (z y)) 𝒞.id))) (sym p)
    compose Y→apex (id p) = J (λ y q → k (Cospan [ Y→apex ∘ cospanHom.id (sym q) ]) ≡ g ∘ k (cospanHom.id (sym q))) ((cong (λ w → k w) (transportRefl Y→apex) ∙ sym identʳ) ∙ sym (cong (g ∘_) (JRefl (λ y q → Hom (z cospanOb.Y) (z y)) 𝒞.id))) (sym p)
    compose (id p) s = J
                             (λ y q →
                                k (Cospan [ cospanHom.id q ∘ s ]) ≡
                                (𝒞 [ k (cospanHom.id q) ∘ k s ]))
                             (
                               k (Cospan [ cospanHom.id refl ∘ s ])
                             ≡⟨ cong {y = s} k (Category.identˡ Cospan) ⟩
                               k s
                             ≡⟨ sym identˡ ⟩
                               𝒞.id ∘ k s
                             ≡⟨ cong (_∘ k s) (sym (transportRefl 𝒞.id)) ⟩
                               k (cospanHom.id refl) ∘ k s
                             ∎
                             ) p
