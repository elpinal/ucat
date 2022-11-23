module Bicategory where

open import Cubical.Core.Everything
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

open import Category

-- Notice that the order of arguments to composition operations is reversed from the paper.
record Bicategory o c d : Type (ℓ-suc (ℓ-max o (ℓ-max c d))) where
  field
    Ob : Type o
    1Cell : ∀ (A B : Ob) → Type c
    2Cell : ∀ {A B} (f g : 1Cell A B) → Type d

    id₁ : ∀ {A : Ob} → 1Cell A A
    _∘₁_ : ∀ {A B C : Ob} → 1Cell B C → 1Cell A B → 1Cell A C

    -- Vertical composition of 2-cells.
    id₂ : ∀ {A B} {f : 1Cell A B} → 2Cell f f
    _·_ : ∀ {A B} {f g h : 1Cell A B} → 2Cell g h → 2Cell f g → 2Cell f h

    -- Beware of the orders of arguments!
    _▹_ : ∀ {A B C} {g h : 1Cell B C} (θ : 2Cell g h) (f : 1Cell A B) → 2Cell (g ∘₁ f) (h ∘₁ f)
    _◃_ : ∀ {A B C} (h : 1Cell B C) {f g : 1Cell A B} (θ : 2Cell f g) → 2Cell (h ∘₁ f) (h ∘₁ g)

    -- Beware of the orders of arguments!
    unitorˡ : ∀ {A B} (f : 1Cell A B) → 2Cell (id₁ ∘₁ f) f
    unitorˡ⁻¹ : ∀ {A B} (f : 1Cell A B) → 2Cell f (id₁ ∘₁ f)
    unitorʳ : ∀ {A B} (f : 1Cell A B) → 2Cell (f ∘₁ id₁) f
    unitorʳ⁻¹ : ∀ {A B} (f : 1Cell A B) → 2Cell f (f ∘₁ id₁)
    associator : ∀ {A B C D} (f : 1Cell A B) (g : 1Cell B C) (h : 1Cell C D)
      → 2Cell ((h ∘₁ g) ∘₁ f) (h ∘₁ (g ∘₁ f))
    associator⁻¹ : ∀ {A B C D} (f : 1Cell A B) (g : 1Cell B C) (h : 1Cell C D)
      → 2Cell (h ∘₁ (g ∘₁ f)) ((h ∘₁ g) ∘₁ f)

    isSet2Cell : ∀ {A B} {f g : 1Cell A B} → isSet (2Cell f g)

    -- Laws.
    ident₂ˡ : ∀ {A B} {f g : 1Cell A B} {θ : 2Cell f g} → id₂ · θ ≡ θ
    ident₂ʳ : ∀ {A B} {f g : 1Cell A B} {θ : 2Cell f g} → θ · id₂ ≡ θ
    assoc₂ : ∀ {A B} {f g h i : 1Cell A B} {θ : 2Cell f g} {γ : 2Cell g h} {τ : 2Cell h i} → (τ · γ) · θ ≡ τ · (γ · θ)

    ▹id : ∀ {A B} {f : 1Cell A B} {g : 1Cell B B} → id₂ {f = g} ▹ f ≡ id₂ {f = g ∘₁ f}
    ▹· : ∀ {A B C} {f : 1Cell A B} {g h i : 1Cell B C} {θ : 2Cell g h} {γ : 2Cell h i} → (γ · θ) ▹ f ≡ (γ ▹ f) · (θ ▹ f)

    ◃id : ∀ {A B} {f : 1Cell A A} {g : 1Cell A B} → g ◃ id₂ {f = f} ≡ id₂ {f = g ∘₁ f}
    ◃· : ∀ {A B C} {f g h : 1Cell A B} {i : 1Cell B C} {θ : 2Cell f g} {γ : 2Cell g h} → i ◃ (γ · θ) ≡ (i ◃ γ) · (i ◃ θ)

    unitorʳ▹ : ∀ {A B} {f g : 1Cell A B} {θ : 2Cell f g} → unitorʳ g · (θ ▹ id₁ {A = A}) ≡ θ · unitorʳ f
    unitorˡ◃ : ∀ {A B} {f g : 1Cell A B} {θ : 2Cell f g} → unitorˡ g · (id₁ {A = B} ◃ θ) ≡ θ · unitorˡ f

    associator·▹▹ : ∀ {A B C D} {f : 1Cell A B} {g : 1Cell B C} {h i : 1Cell C D} {θ : 2Cell h i}
      → associator f g i · ((θ ▹ g) ▹ f) ≡ (θ ▹ (g ∘₁ f)) · associator f g h
    associator·◃▹ : ∀ {A B C D} {f : 1Cell A B} {g h : 1Cell B C} {i : 1Cell C D} {θ : 2Cell g h}
      → associator f h i · ((i ◃ θ) ▹ f) ≡ (i ◃ (θ ▹ f)) · associator f g i
    associator·◃◃ : ∀ {A B C D} {f g : 1Cell A B} {h : 1Cell B C} {i : 1Cell C D} {θ : 2Cell f g}
      → associator g h i · ((i ∘₁ h) ◃ θ) ≡ (i ◃ (h ◃ θ)) · associator f h i

    ▹·◃ : ∀ {A B C} {f g : 1Cell A B} {h i : 1Cell B C} {θ : 2Cell f g} {γ : 2Cell h i}
      → (γ ▹ g) · (h ◃ θ) ≡ (i ◃ θ) · (γ ▹ f)

    unitorˡ-invˡ : ∀ {A B} {f : 1Cell A B}
      → unitorˡ⁻¹ f · unitorˡ f ≡ id₂ {f = id₁ ∘₁ f}
    unitorˡ-invʳ : ∀ {A B} {f : 1Cell A B}
      → unitorˡ f · unitorˡ⁻¹ f ≡ id₂ {f = f}
    unitorʳ-invˡ : ∀ {A B} {f : 1Cell A B}
      → unitorʳ⁻¹ f · unitorʳ f ≡ id₂ {f = f ∘₁ id₁}
    unitorʳ-invʳ : ∀ {A B} {f : 1Cell A B}
      → unitorʳ f · unitorʳ⁻¹ f ≡ id₂ {f = f}

    associator-invˡ : ∀ {A B C D} {f : 1Cell A B} {g : 1Cell B C} {h : 1Cell C D}
      → associator⁻¹ f g h · associator f g h ≡ id₂
    associator-invʳ : ∀ {A B C D} {f : 1Cell A B} {g : 1Cell B C} {h : 1Cell C D}
      → associator f g h · associator⁻¹ f g h ≡ id₂

    ◃·associator : ∀ {A B C} {f : 1Cell A B} {g : 1Cell B C}
      → (g ◃ unitorˡ f) · associator f id₁ g ≡ unitorʳ g ▹ f
    associator·associator : ∀ {A B C D E} {f : 1Cell A B} {g : 1Cell B C} {h : 1Cell C D} {i : 1Cell D E}
      → associator (g ∘₁ f) h i · associator f g (i ∘₁ h) ≡ ((i ◃ associator f g h) · associator f (h ∘₁ g) i) · (associator g h i ▹ f)

  -- Horizontal composition of 2-cells.
  _∘₂_ : ∀ {A B C} {h i : 1Cell B C} {f g : 1Cell A B} → 2Cell f g → 2Cell h i → 2Cell (h ∘₁ f) (i ∘₁ g)
  _∘₂_ {i = i} {f = f} γ θ = iγ · θf
    where
      θf : 2Cell (_ ∘₁ f) (i ∘₁ f)
      θf = θ ▹ f

      iγ : 2Cell (i ∘₁ f) (i ∘₁ _)
      iγ = i ◃ γ

private
  variable o c d : Level

module _ (𝔹 : Bicategory o c d) where
  module 𝔹 = Bicategory 𝔹
  open 𝔹

  HomCat : (A B : Ob) → Category c d
  HomCat A B = record
                 { Ob = 1Cell A B
                 ; Hom = 2Cell
                 ; isSetHom = isSet2Cell
                 ; id = id₂
                 ; _∘_ = _·_
                 ; identˡ = ident₂ˡ
                 ; identʳ = ident₂ʳ
                 ; assoc = assoc₂
                 }

  record isInv {A B} {f g : 1Cell A B} (θ : 2Cell f g) : Type d where
    field
      inv : 2Cell g f
      invˡ : inv · θ ≡ id₂
      invʳ : θ · inv ≡ id₂

  isInvId : ∀ {A B} {f : 1Cell A B} → isInv (id₂ {f = f})
  isInvId = record { inv = id₂ ; invˡ = ident₂ˡ ; invʳ = ident₂ʳ }

  isPropIsInv : ∀ {A B} {f g : 1Cell A B} (θ : 2Cell f g) → isProp (isInv θ)
  isPropIsInv θ x y i = record { inv = p i ; invˡ = q i ; invʳ = r i }
    where
      module x = isInv x
      module y = isInv y

      p : x.inv ≡ y.inv
      p =
          x.inv
        ≡⟨ sym ident₂ˡ ⟩
          id₂ · x.inv
        ≡⟨ cong (_· x.inv) (sym y.invˡ) ⟩
          (y.inv · θ) · x.inv
        ≡⟨ assoc₂ ⟩
          y.inv · (θ · x.inv)
        ≡⟨ cong (y.inv ·_) x.invʳ ⟩
          y.inv · id₂
        ≡⟨ ident₂ʳ ⟩
          y.inv
        ∎

      q : PathP (λ i → p i · θ ≡ id₂) x.invˡ y.invˡ
      q = isSet→isSet' isSet2Cell _ _ _ _

      r : PathP (λ i → θ · p i ≡ id₂) x.invʳ y.invʳ
      r = isSet→isSet' isSet2Cell _ _ _ _

  record Inv2Cell {A B} (f g : 1Cell A B) : Type d where
    field
      θ : 2Cell f g
      is-inv : isInv θ
