module Displayed.FromFunctor where

open import Cubical.Core.Everything
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels
open import Cubical.Data.Sigma

open import Category
open import Functor
open import Displayed

private
  variable
    o h ℓ : Level
    E : Category o h

fromFunctor : ∀ {ℬ : Category o h} → Functor E ℬ → Displayed ℬ _ _
fromFunctor {E = E} {ℬ = ℬ} F = record
                           { Ob = fiber F.₀
                           ; Hom = Hom
                           ; isSetHom = λ { {f = f} {X = X} {Y = Y} → isSetΣSndProp E.isSetHom λ f′ → ℬ.isSetHom (F.₁ f′) (transport (λ i → ℬ [ snd X (~ i) , snd Y (~ i) ]) f) }
                           ; id = λ { {X = X} → id {X = X} }
                           ; _∘_ = λ { {X = X} {Y} {Z} g′ f′ → _∘_ {X = X} {Y} {Z} g′ f′ }
                           ; identˡ = λ { {X = X} {Y} → identˡ {X = X} {Y} }
                           ; identʳ = λ { {X = X} {Y} → identʳ {X = X} {Y} }
                           ; assoc = λ { {X = X} {Y} {Z} {W} → assoc {X = X} {Y} {Z} {W} }
                           }
  where
    module F = Functor.Functor F
    module E = Category.Category E
    module ℬ = Category.Category ℬ

    Hom : ∀ {A B} → ℬ.Hom A B → fiber F.₀ A → fiber F.₀ B → Type _
    Hom f (X , p) (Y , q) = fiber (F.₁ {A = X} {B = Y}) (transport (λ i → ℬ [ p (~ i) , q (~ i) ]) f)

    id : ∀ {A : ℬ.Ob} {X : fiber F.₀ A} → Hom ℬ.id X X
    id {X = X} = E.id , F.identity ∙ sym (isIso.isoˡ (Iso.is-iso (idToIso ℬ (λ i → X .snd (~ i))))) ∙ cong (Iso.f (idToIso ℬ (λ i → X .snd (~ i))) ℬ.∘_) (sym ℬ.identˡ) ∙ sym (lemmaIdToIso ℬ (sym (X .snd)) (sym (X .snd)) ℬ.id)

    _∘_ : ∀ {A B C : ℬ.Ob} {f : ℬ.Hom A B} {g : ℬ.Hom B C}
      {X : fiber F.₀ A} {Y : fiber F.₀ B} {Z : fiber F.₀ C} →
      Hom g Y Z → Hom f X Y → Hom (ℬ [ g ∘ f ]) X Z
    _∘_ {f = f} {g = g} {X = X , p} {Y = Y , q} {Z = Z , r} (g′ , s) (f′ , t) =
      (E [ g′ ∘ f′ ]) , F.compose ∙ cong₂ ℬ._∘_ s t ∙ u
      where
        u : transport (λ i → ℬ [ q (~ i) , r (~ i) ]) g ℬ.∘ transport (λ i → ℬ [ p (~ i) , q (~ i) ]) f
          ≡ transport (λ i → ℬ [ p (~ i) , r (~ i) ]) (ℬ [ g ∘ f ])
        u =
            transport (λ i → ℬ [ q (~ i) , r (~ i) ]) g ℬ.∘ transport (λ i → ℬ [ p (~ i) , q (~ i) ]) f
          ≡⟨ cong (ℬ._∘ transport (λ i → ℬ [ p (~ i) , q (~ i) ]) f) (lemmaIdToIso ℬ (sym q) (sym r) g) ⟩
            (Iso.f (idToIso ℬ (sym r)) ℬ.∘ (g ℬ.∘ Iso.inv (idToIso ℬ (sym q)))) ℬ.∘ transport (λ i → ℬ [ p (~ i) , q (~ i) ]) f
          ≡⟨ cong
               ((Iso.f (idToIso ℬ (sym r)) ℬ.∘
                 (g ℬ.∘ Iso.inv (idToIso ℬ (sym q))))
                ℬ.∘_)
               (lemmaIdToIso ℬ (sym p) (sym q) f) ⟩
            (Iso.f (idToIso ℬ (sym r)) ℬ.∘ (g ℬ.∘ Iso.inv (idToIso ℬ (sym q)))) ℬ.∘ (Iso.f (idToIso ℬ (sym q)) ℬ.∘ (f ℬ.∘ Iso.inv (idToIso ℬ (sym p))))
          ≡⟨ ℬ.assoc ⟩
            Iso.f (idToIso ℬ (sym r)) ℬ.∘ ((g ℬ.∘ Iso.inv (idToIso ℬ (sym q))) ℬ.∘ (Iso.f (idToIso ℬ (sym q)) ℬ.∘ (f ℬ.∘ Iso.inv (idToIso ℬ (sym p)))))
          ≡⟨ cong (Iso.f (idToIso ℬ (sym r)) ℬ.∘_) (assoc-inner ℬ) ⟩
            Iso.f (idToIso ℬ (sym r)) ℬ.∘ ((g ℬ.∘ (Iso.inv (idToIso ℬ (sym q)) ℬ.∘ Iso.f (idToIso ℬ (sym q)))) ℬ.∘ (f ℬ.∘ Iso.inv (idToIso ℬ (sym p))))
          ≡⟨ cong (Iso.f (idToIso ℬ (sym r)) ℬ.∘_) (cong (ℬ._∘ (f ℬ.∘ Iso.inv (idToIso ℬ (λ i → p (~ i))))) ((cong (g ℬ.∘_) (isIso.isoʳ (Iso.is-iso (idToIso ℬ (λ i → q (~ i)))))) ∙ ℬ.identʳ)) ⟩
            Iso.f (idToIso ℬ (sym r)) ℬ.∘ (g ℬ.∘ (f ℬ.∘ Iso.inv (idToIso ℬ (sym p))))
          ≡⟨ sym (cong (Iso.f (idToIso ℬ (sym r)) ℬ.∘_) ℬ.assoc) ⟩
            Iso.f (idToIso ℬ (sym r)) ℬ.∘ ((g ℬ.∘ f) ℬ.∘ Iso.inv (idToIso ℬ (sym p)))
          ≡⟨ sym (lemmaIdToIso ℬ (sym p) (sym r) (g ℬ.∘ f)) ⟩
            transport (λ i → ℬ [ p (~ i) , r (~ i) ]) (ℬ [ g ∘ f ])
          ∎

    identˡ : ∀ {A B : ℬ.Ob} {f : ℬ.Hom A B} {X : fiber F.₀ A}
      {Y : fiber F.₀ B} {f′ : Hom f X Y} →
      PathP (λ i → Hom (ℬ.identˡ {f = f} i) X Y)
      (_∘_ {X = X} {Y = Y} {Z = Y} (id {X = Y}) f′) f′
    identˡ {f = f} {X = X} {Y = Y} {f′ = f′ , p} = ΣPathP (E.identˡ , toPathP (ℬ.isSetHom (F.₁ f′) (transport (λ i → ℬ [ snd X (~ i) , snd Y (~ i) ]) f) _ p))

    identʳ : ∀ {A B : ℬ.Ob} {f : ℬ.Hom A B} {X : fiber F.₀ A}
      {Y : fiber F.₀ B} {f′ : Hom f X Y} →
      PathP (λ i → Hom (ℬ.identʳ {f = f} i) X Y)
      (_∘_ {X = X} {Y = X} {Z = Y} f′ (id {X = X})) f′
    identʳ {f = f} {X = X} {Y = Y} {f′ = f′ , p} = ΣPathP (E.identʳ , (toPathP (ℬ.isSetHom (F.₁ f′) (transport (λ i → ℬ [ snd X (~ i) , snd Y (~ i) ]) f) _ p)))

    assoc : ∀ {A B C D : ℬ.Ob} {f : ℬ.Hom A B} {g : ℬ.Hom B C}
      {h = h₁ : ℬ.Hom C D} {X : fiber F.₀ A} {Y : fiber F.₀ B}
      {Z : fiber F.₀ C} {W : fiber F.₀ D} {f′ : Hom f X Y}
      {g′ : Hom g Y Z} {h′ : Hom h₁ Z W} →
      PathP (λ i → Hom (ℬ.assoc {f = f} {g = g} {h = h₁} i) X W)
      (_∘_ {X = X} {Y = Y} {Z = W} (_∘_ {X = Y} {Y = Z} {Z = W} h′ g′) f′)
      (_∘_ {X = X} {Y = Z} {Z = W} h′ (_∘_ {X = X} {Y = Y} {Z = Z} g′ f′))
    assoc {f = f} {g} {h = h₁} {X = X} {Y} {Z} {W} {f′ = f′ , p} {g′ , q} {h′ , r} =
      ΣPathP (E.assoc , toPathP (ℬ.isSetHom (F.₁ (h′ E.∘ (g′ E.∘ f′))) (transport (λ i → ℬ [ snd X (~ i) , snd W (~ i) ]) (h₁ ℬ.∘ (g ℬ.∘ f))) _ _))
