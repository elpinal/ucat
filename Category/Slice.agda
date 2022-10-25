open import Category

module Category.Slice {o h} (𝒞 : Category o h) where

open import Cubical.Core.Everything
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.Transport
open import Cubical.Data.Sigma

module 𝒞 = Category.Category 𝒞
open 𝒞

module _ (X : Ob) where
  over : Type (ℓ-max o h)
  over = Σ[ A ∈ Ob ] Hom A X

  commTri : over → over → Type h
  commTri (A , f) (B , g) = Σ[ h ∈ Hom A B ] f ≡ g ∘ h

  helper : ∀ (f g : over) (c c′ : commTri f g) → isEquiv (λ (p : c ≡ c′) → cong fst p)
  helper (A , f) (B , g) c c′ = isEmbeddingFstΣProp (λ h → isSetHom f (g ∘ h)) {u = c} {v = c′}

  isSetCommTri : ∀ {x y} → isSet (commTri x y)
  isSetCommTri {A , f} {B , g} (h , c) (h′ , c′) e₁ e₂ = sym (transport⁻Transport p _) ∙∙ q ∙∙ transport⁻Transport p _
    where
      p : ((h , c) ≡ (h′ , c′)) ≡ (h ≡ h′)
      p = ua (_ , helper (A , f) (B , g) (h , c) (h′ , c′))

      pe₁ : h ≡ h′
      pe₁ = transport p e₁

      pe₂ : h ≡ h′
      pe₂ = transport p e₂

      pe₁≡pe₂ : pe₁ ≡ pe₂
      pe₁≡pe₂ = isSetHom h h′ pe₁ pe₂

      q : transport⁻ p pe₁ ≡ transport⁻ p pe₂
      q = cong (transport⁻ p) pe₁≡pe₂

  compose : ∀ {A B C : over} → commTri B C → commTri A B → commTri A C
  compose {A , f} {B , g} {C , i} (h′ , c′) (h , c) = (h′ ∘ h) , (c ∙∙ cong (_∘ h) c′ ∙∙ assoc)

  Over : Category (ℓ-max o h) h
  Over = record
           { Ob = over
           ; Hom = commTri
           ; isSetHom = isSetCommTri
           ; id = id , sym identʳ
           ; _∘_ = compose
           ; identˡ = ΣPathP (identˡ , toPathP (isSetHom _ _ _ _))
           ; identʳ = ΣPathP (identʳ , toPathP (isSetHom _ _ _ _))
           ; assoc = ΣPathP (assoc , toPathP (isSetHom _ _ _ _))
           }
