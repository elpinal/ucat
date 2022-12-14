module Displayed.Reindex where

open import Cubical.Core.Everything
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Transport
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Path

open import Category
open import Functor
open import Displayed
open import Displayed.Functor

module _ {o h} {π : Category o h} {oβ² hβ²} (π : Displayed π oβ² hβ²) where
  private
    module π = Category.Category π
    module π = Displayed.Displayed π

  reindex : β {β m} {πβ² : Category β m} (F : Functor πβ² π) β Displayed πβ² oβ² hβ²
  reindex {πβ² = πβ²} F = record
                { Ob = Ξ» Aβ² β π.Ob (F.β Aβ²)
                ; Hom = Ξ» f X Y β π.Hom (F.β f) X Y
                ; isSetHom = π.isSetHom
                ; id = id
                ; _β_ = _β_
                ; identΛ‘ = identΛ‘
                ; identΚ³ = identΚ³
                ; assoc = assoc
                }
    where
      module F = Functor.Functor F
      module πβ² = Category.Category πβ²

      id : β {A : πβ².Ob} {X : π.Ob (F.β A)} β π.Hom (F.β πβ².id) X X
      id = subst (Ξ» x β π.Hom x _ _) (sym F.identity) π.id

      _β_ : β {A B C} {f : πβ² [ A , B ]} {g : πβ² [ B , C ]} {X Y Z}
        β π.Hom (F.β g) Y Z
        β π.Hom (F.β f) X Y
        β π.Hom (F.β (πβ² [ g β f ])) X Z
      _β_ = Ξ» g f β subst (Ξ» x β π.Hom x _ _) (sym F.compose) (g π.β f)

      identΛ‘ : β {A B : πβ².Ob} {f : πβ² [ A , B ]}
        {X : π.Ob (F.β A)} {Y : π.Ob (F.β B)}
        {fβ² : π.Hom (F.β f) X Y}
        β PathP (Ξ» i β π.Hom (F.β (πβ².identΛ‘ {f = f} i)) X Y) (id β fβ²) fβ²
      identΛ‘ {f = f} {X = X} {Y = Y} {fβ² = fβ²} = transportβ» (PathPβ‘Pathβ» (Ξ» i β π.Hom (F.β (πβ².identΛ‘ i)) X Y) _ _) p
        where
          p : id β fβ² β‘ subst (Ξ» x β π.Hom (F.β x) X Y) (sym πβ².identΛ‘) fβ²
          p =
              id β fβ²
            β‘β¨ refl β©
              subst (Ξ» x β π.Hom x _ _) (sym F.compose) (id π.β fβ²)
            β‘β¨ refl β©
              subst (Ξ» x β π.Hom x _ _) (sym F.compose) (subst (Ξ» x β π.Hom x _ _) (sym F.identity) π.id π.β fβ²)
            β‘β¨ cong (subst (Ξ» x β π.Hom x _ _) (sym F.compose)) (hoist-substΛ‘ π _) β©
              subst (Ξ» x β π.Hom x _ _) (sym F.compose) (subst (Ξ» x β π.Hom x _ _) (cong (π._β F.β f) (sym F.identity)) (π.id π.β fβ²))
            β‘β¨ sym (substComposite (Ξ» x β π.Hom x _ _) _ _ _) β©
              subst (Ξ» x β π.Hom x _ _) (cong (π._β F.β f) (sym F.identity) β sym F.compose) (π.id π.β fβ²)
            β‘β¨ cong
                 (subst (Ξ» x β π.Hom x _ _)
                  (cong (π._β F.β f) (sym F.identity) β sym F.compose))
                 (transport (PathPβ‘Pathβ» (Ξ» i β π.Hom (π.identΛ‘ i) _ _) _ _) π.identΛ‘) β©
              subst (Ξ» x β π.Hom x _ _) (cong (π._β F.β f) (sym F.identity) β sym F.compose) (subst (Ξ» x β π.Hom x _ _) (sym π.identΛ‘) fβ²)
            β‘β¨ sym (substComposite (Ξ» x β π.Hom x _ _) _ _ _) β©
              subst (Ξ» x β π.Hom x _ _) (sym π.identΛ‘ β (cong (π._β F.β f) (sym F.identity) β sym F.compose)) fβ²
            β‘β¨ cong (Ξ» w β subst (Ξ» x β π.Hom x _ _) w fβ²) (π.isSetHom _ _ _ _) β©
              subst (Ξ» x β π.Hom (F.β x) X Y) (sym πβ².identΛ‘) fβ²
            β

      identΚ³ : β {A B : πβ².Ob} {f : πβ² [ A , B ]}
        {X : π.Ob (F.β A)} {Y : π.Ob (F.β B)}
        {fβ² : π.Hom (F.β f) X Y}
        β PathP (Ξ» i β π.Hom (F.β (πβ².identΚ³ {f = f} i)) X Y) (fβ² β id) fβ²
      identΚ³ {f = f} {X = X} {Y = Y} {fβ² = fβ²} = transportβ» (PathPβ‘Pathβ» (Ξ» i β π.Hom (F.β (πβ².identΚ³ i)) X Y) _ _) p
        where
          p : fβ² β id β‘ subst (Ξ» x β π.Hom (F.β x) X Y) (sym πβ².identΚ³) fβ²
          p =
              subst (Ξ» x β π.Hom x _ _) (sym F.compose) (fβ² π.β subst (Ξ» x β π.Hom x _ _) (sym F.identity) π.id)
            β‘β¨ cong (subst (Ξ» x β π.Hom x _ _) (sym F.compose)) (hoist-substΚ³ π _) β©
              subst (Ξ» x β π.Hom x _ _) (sym F.compose) (subst (Ξ» x β π.Hom x _ _) (cong (F.β f π.β_) (sym F.identity)) (fβ² π.β π.id))
            β‘β¨ sym (substComposite (Ξ» x β π.Hom x _ _) _ _ _) β©
              subst (Ξ» x β π.Hom x _ _) (cong (F.β f π.β_) (sym F.identity) β sym F.compose) (fβ² π.β π.id)
            β‘β¨ cong
                 (subst (Ξ» x β π.Hom x _ _)
                  (cong (F.β f π.β_) (sym F.identity) β sym F.compose))
                 (transport (PathPβ‘Pathβ» (Ξ» i β π.Hom (π.identΚ³ i) _ _) _ _) π.identΚ³) β©
              subst (Ξ» x β π.Hom x _ _) (cong (F.β f π.β_) (sym F.identity) β sym F.compose) (subst (Ξ» x β π.Hom x _ _) (sym π.identΚ³) fβ²)
            β‘β¨ sym (substComposite (Ξ» x β π.Hom x _ _) _ _ _) β©
              subst (Ξ» x β π.Hom x _ _) (sym π.identΚ³ β (cong (F.β f π.β_) (sym F.identity) β sym F.compose)) fβ²
            β‘β¨ cong (Ξ» w β subst (Ξ» x β π.Hom x _ _) w fβ²) (π.isSetHom _ _ _ _) β©
              subst (Ξ» x β π.Hom (F.β x) X Y) (sym πβ².identΚ³) fβ²
            β

      assoc : β {A B C D : πβ².Ob}
        {f : πβ² [ A , B ]} {g : πβ² [ B , C ]} {h : πβ² [ C , D ]}
        {X : π.Ob (F.β A)} {Y : π.Ob (F.β B)} {Z : π.Ob (F.β C)} {W : π.Ob (F.β D)}
        {fβ² : π.Hom (F.β f) X Y} {gβ² : π.Hom (F.β g) Y Z} {hβ² : π.Hom (F.β h) Z W}
        β PathP (Ξ» i β π.Hom (F.β (πβ².assoc {f = f} {g = g} {h = h} i)) X W) ((hβ² β gβ²) β fβ²) (hβ² β (gβ² β fβ²))
      assoc {f = f} {g = g} {h = h} {X = X} {Y = Y} {W = W} {fβ² = fβ²} {gβ² = gβ²} {hβ² = hβ²} = toPathP (sym p)
        where
          p : hβ² β (gβ² β fβ²) β‘ subst (Ξ» x β π.Hom (F.β x) X W) πβ².assoc ((hβ² β gβ²) β fβ²)
          p =
              hβ² β (gβ² β fβ²)
            β‘β¨ refl β©
              subst (Ξ» x β π.Hom x _ _) (sym F.compose) (hβ² π.β subst (Ξ» x β π.Hom x _ _) (sym F.compose) (gβ² π.β fβ²))
            β‘β¨ cong (subst (Ξ» x β π.Hom x _ _) (sym F.compose)) (hoist-substΚ³ π _) β©
              subst (Ξ» x β π.Hom x _ _) (sym F.compose) (subst (Ξ» x β π.Hom x _ _) (cong (F.β h π.β_) (sym F.compose)) (hβ² π.β (gβ² π.β fβ²)))
            β‘β¨ sym (substComposite (Ξ» x β π.Hom x _ _) _ _ _) β©
              subst (Ξ» x β π.Hom x _ _) (cong (F.β h π.β_) (sym F.compose) β sym F.compose) (hβ² π.β (gβ² π.β fβ²))
            β‘β¨ cong
                 (subst (Ξ» x β π.Hom x _ _)
                  (cong (F.β h π.β_) (sym F.compose) β sym F.compose))
                 (sym (fromPathP π.assoc)) β©
              subst (Ξ» x β π.Hom x _ _) (cong (F.β h π.β_) (sym F.compose) β sym F.compose)
                (subst (Ξ» x β π.Hom x _ _) π.assoc ((hβ² π.β gβ²) π.β fβ²))
            β‘β¨ sym (substComposite (Ξ» x β π.Hom x _ _) _ _ _) β©
              subst (Ξ» x β π.Hom x _ _) (π.assoc β (cong (F.β h π.β_) (sym F.compose) β sym F.compose)) ((hβ² π.β gβ²) π.β fβ²)
            β‘β¨ cong (Ξ» w β subst (Ξ» x β π.Hom x _ _) w ((hβ² π.β gβ²) π.β fβ²)) (π.isSetHom _ _ _ _) β©
              subst (Ξ» x β π.Hom x X W) (cong (π._β F.β f) (sym F.compose) β (sym F.compose β cong F.β πβ².assoc)) (((hβ² π.β gβ²) π.β fβ²))
            β‘β¨ substComposite (Ξ» x β π.Hom x X W) _ _ _ β©
              subst (Ξ» x β π.Hom x X W) (sym F.compose β cong F.β πβ².assoc) (subst (Ξ» x β π.Hom x _ _) (cong (π._β F.β f) (sym F.compose)) ((hβ² π.β gβ²) π.β fβ²))
            β‘β¨ cong
                 (subst (Ξ» x β π.Hom x X W) (sym F.compose β cong F.β πβ².assoc)) (sym (hoist-substΛ‘ π _)) β©
              subst (Ξ» x β π.Hom x X W) (sym F.compose β cong F.β πβ².assoc) (subst (Ξ» x β π.Hom x _ _) (sym F.compose) (hβ² π.β gβ²) π.β fβ²)
            β‘β¨ substComposite (Ξ» x β π.Hom x X W) _ _ _ β©
              subst (Ξ» x β π.Hom (F.β x) X W) πβ².assoc (subst (Ξ» x β π.Hom x _ _) (sym F.compose) ((subst (Ξ» x β π.Hom x _ _) (sym F.compose) (hβ² π.β gβ²)) π.β fβ²))
            β‘β¨ refl β©
              subst (Ξ» x β π.Hom (F.β x) X W) πβ².assoc ((hβ² β gβ²) β fβ²)
            β

  reindexProj : β {β m} {πβ² : Category β m} (F : Functor πβ² π)
    β DisplayedFunctor F (reindex F) π
  reindexProj F = record
    { Fβ = Ξ» A β A
    ; Fβ = Ξ» f β f
    ; identity = toPathP (transportTransportβ» (Ξ» i β π.Hom (F.identity i) _ _) _)
    ; compose = toPathP (transportTransportβ» (Ξ» i β π.Hom (F.compose i) _ _) _)
    }
    where module F = Functor.Functor F
