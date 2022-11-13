module HLevelUtil where

open import Cubical.Core.Everything
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Data.Nat

private
  variable ℓ ℓ' ℓ'' : Level

isOfHLevelDep2 : HLevel → {A : Type ℓ} (B : A → Type ℓ') (C : (a : A) → B a → Type ℓ'') → Type (ℓ-max ℓ (ℓ-max ℓ' ℓ''))
isOfHLevelDep2 0 {A = A} B C =
  {a : A} {b : B a} → Σ[ c ∈ C a b ] ({a' : A} {b' : B a'} (c' : C a' b') (p : a ≡ a') (q : PathP (λ i → B (p i)) b b') → PathP (λ i → C (p i) (q i)) c c')
isOfHLevelDep2 1 {A = A} B C =
  {a0 a1 : A} {b0 : B a0} {b1 : B a1} (c0 : C a0 b0) (c1 : C a1 b1) (p : a0 ≡ a1) (q : PathP (λ i → B (p i)) b0 b1)
    → PathP (λ i → C (p i) (q i)) c0 c1
isOfHLevelDep2 (suc (suc n)) {A = A} B C =
  {a0 a1 : A} {b0 : B a0} {b1 : B a1} (c0 : C a0 b0) (c1 : C a1 b1)
    → isOfHLevelDep2 (suc n) {A = a0 ≡ a1} (λ p → PathP (λ i → B (p i)) b0 b1) (λ p q → PathP (λ i → C (p i) (q i)) c0 c1)

isOfHLevel→isOfHLevelDep2 : (n : HLevel)
  → {A : Type ℓ} {B : A → Type ℓ'} {C : (a : A) → B a → Type ℓ''} (h : (a : A) → (b : B a) → isOfHLevel n (C a b))
  → isOfHLevelDep2 n {A = A} B C
isOfHLevel→isOfHLevelDep2 0 h {a} {b} =
  h a b .fst , λ c' p q → isProp→PathP (λ i → isContr→isProp (h (p i) (q i))) (h a b .fst) c'
isOfHLevel→isOfHLevelDep2 1 h = λ c0 c1 p q → isProp→PathP (λ i → h (p i) (q i)) c0 c1
isOfHLevel→isOfHLevelDep2 (suc (suc n)) {A = A} {B} {C} h {a0} {a1} {b0} {b1} c0 c1 =
  isOfHLevel→isOfHLevelDep2 (suc n) (λ p q → helper a1 p b1 q c1)
  where
    helper : (a1 : A) (p : a0 ≡ a1) (b1 : B a1) (q : PathP (λ i → B (p i)) b0 b1) (c1 : C a1 b1) →
      isOfHLevel (suc n) (PathP (λ i → C (p i) (q i)) c0 c1)
    helper a1 p b1 q c1 = J P base p b1 q c1
      where
        Q : ∀ b1 (q : b0 ≡ b1) → Type _
        Q b1 q = ∀ (c1 : C a0 b1) → isOfHLevel (suc n) (PathP (λ i → C _ (q i)) c0 c1)

        base′ : Q b0 refl
        base′ = h _ _ _

        P : ∀ a1 (p : a0 ≡ a1) → Type _
        P a1 p = ∀ (b1 : B a1) (q : PathP (λ i → B (p i)) b0 b1) c1 → isOfHLevel (suc n) (PathP (λ i → C (p i) (q i)) c0 c1)

        base : ∀ (b1 : B a0) (q : Path (B _) b0 b1) c1 → isOfHLevel (suc n) (PathP (λ i → C _ (q i)) c0 c1)
        base b1 q c1 = J Q base′ q c1
