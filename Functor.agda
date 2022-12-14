module Functor where

open import Cubical.Core.Everything
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

open import HLevelUtil

open import Category

record Functor {o h} (π : Category o h) {oβ² hβ²} (π : Category oβ² hβ²) : Type (β-max o (β-max h (β-max oβ² hβ²))) where
  private
    module π = Category.Category π
    module π = Category.Category π

  field
    Fβ : π.Ob β π.Ob
    Fβ : β {A B : π.Ob} β π [ A , B ] β π [ Fβ A , Fβ B ]
    identity : β {A : π.Ob} β Fβ (π.id {A}) β‘ π.id
    compose : β {A B C : π.Ob} {f : π [ A , B ]} {g : π [ B , C ]} β Fβ (π [ g β f ]) β‘ π [ Fβ g β Fβ f ]

  β = Fβ
  β = Fβ

module _ {o h} {π : Category o h} where
  idFunctor : Functor π π
  idFunctor = record { Fβ = Ξ» A β A ; Fβ = Ξ» f β f ; identity = refl ; compose = refl }

module _ {o h oβ² hβ² oβ³ hβ³} {π : Category o h} {π : Category oβ² hβ²} {β° : Category oβ³ hβ³} where
  _βF_ : Functor π β° β Functor π π β Functor π β°
  G βF F = record
    { Fβ = Ξ» A β G.β (F.β A)
    ; Fβ = Ξ» f β G.β (F.β f)
    ; identity = cong G.β F.identity β G.identity
    ; compose = cong G.β F.compose β G.compose
    }
    where
      module F = Functor F
      module G = Functor G

module _ {o h oβ² hβ²} {π : Category o h} {π : Category oβ² hβ²} where
  private
    module π = Category.Category π

  -- Even if the codomain category is not univalent, unicity and
  -- associativity laws hold up to *path*, not just natural
  -- isomorphism.

  identFΛ‘ : (F : Functor π π) β idFunctor βF F β‘ F
  identFΛ‘ F i = record
    { Fβ = F.β
    ; Fβ = F.β
    ; identity = π.isSetHom _ _ (F.identity β refl) F.identity i
    ; compose = π.isSetHom _ _ (F.compose β refl) F.compose i
    }
    where
      module F = Functor F

  identFΚ³ : (F : Functor π π) β F βF idFunctor β‘ F
  identFΚ³ F i = record
    { Fβ = F.β
    ; Fβ = F.β
    ; identity = π.isSetHom _ _ (refl β F.identity) F.identity i
    ; compose = π.isSetHom _ _ (refl β F.compose) F.compose i
    }
    where
      module F = Functor F

module _ {o h oβ² hβ² oβ³ hβ³ oβ΄ hβ΄} {π : Category o h} {π : Category oβ² hβ²} {β° : Category oβ³ hβ³} {β± : Category oβ΄ hβ΄} where
  private
    module β± = Category.Category β±

  assocFΚ³ : (F : Functor π π) (G : Functor π β°) (H : Functor β° β±) β (H βF G) βF F β‘ H βF (G βF F)
  assocFΚ³ F G H i = record
    { Fβ = Ξ» A β H.β (G.β (F.β A))
    ; Fβ = Ξ» f β H.β (G.β (F.β f))
    ; identity = β±.isSetHom _ _ (cong (Ξ» f β H.β (G.β f)) F.identity β (cong H.β G.identity β H.identity)) (cong H.β (cong G.β F.identity β G.identity) β H.identity) i
    ; compose = β±.isSetHom _ _ (cong (Ξ» f β H.β (G.β f)) F.compose β (cong H.β G.compose β H.compose)) (cong H.β (cong G.β F.compose β G.compose) β H.compose) i
    }
    where
      module F = Functor F
      module G = Functor G
      module H = Functor H

module _ {o h} (π : Category o h) {oβ² hβ²} (π : Category oβ² hβ²) where
  private
    module π = Category.Category π
    module π = Category.Category π

    helper : β {A}
      β isOfHLevelDep2 2 {A = π.Ob β π.Ob} (Ξ» Fβ β β {A B : π.Ob} β π [ A , B ] β π [ Fβ A , Fβ B ])
        (Ξ» Fβ Fβ β Fβ (π.id {A}) β‘ π.id)
    helper = isOfHLevelβisOfHLevelDep2 2 {B = Ξ» Fβ β β {A B} β π [ A , B ] β π [ Fβ A , Fβ B ]} Ξ» Fβ Fβ β isOfHLevelSuc 1 (π.isSetHom _ _)

    helperβ² : β {A B C} {f : π [ A , B ]} {g : π [ B , C ]}
      β isOfHLevelDep2 2 {A = π.Ob β π.Ob} (Ξ» Fβ β β {A B : π.Ob} β π [ A , B ] β π [ Fβ A , Fβ B ])
        (Ξ» Fβ Fβ β Fβ (π [ g β f ]) β‘ π [ Fβ g β Fβ f ])
    helperβ² = isOfHLevelβisOfHLevelDep2 2 {B = Ξ» Fβ β β {A B} β π [ A , B ] β π [ Fβ A , Fβ B ]} Ξ» Fβ Fβ β isOfHLevelSuc 1 (π.isSetHom _ _)

  FunctorPath : β (F G : Functor π π)
    β (p q : F β‘ G)
    β cong Functor.β p β‘ cong Functor.β q
    β p β‘ q
  FunctorPath F G p q r i j = record
    { Fβ = r i j
    ; Fβ = Ξ» f β Fβ f i j
    ; identity = identity i j
    ; compose = compose i j
    }
    where
      module F = Functor F
      module G = Functor G

      Fβ : β {A B} (f : π [ A , B ])
        β PathP (Ξ» i β PathP (Ξ» j β π [ r i j A , r i j B ]) (F.β f) (G.β f)) (Ξ» k β Functor.β (p k) f) (Ξ» k β Functor.β (q k) f)
      Fβ f = isSetβSquareP (Ξ» i j β π.isSetHom) (Ξ» k β Functor.β (p k) f) (Ξ» k β Functor.β (q k) f) (Ξ» iβ β F.β f) Ξ» iβ β G.β f

      identity : β {A} β PathP (Ξ» i β PathP (Ξ» j β Path (π [ r i j A , r i j A ]) (Fβ (π.id {A}) i j) π.id) F.identity G.identity) (Ξ» k β Functor.identity (p k)) (Ξ» k β Functor.identity (q k))
      identity = helper F.identity G.identity (Ξ» k β Functor.identity (p k)) (Ξ» k β Functor.identity (q k)) r Ξ» i j f β Fβ f i j

      compose : β {A B C} {f : π [ A , B ]} {g : π [ B , C ]}
        β PathP (Ξ» i β PathP (Ξ» j β Path (π [ r i j A , r i j C ]) (Fβ (π [ g β f ]) i j) (π [ Fβ g i j β Fβ f i j ])) F.compose G.compose) (Ξ» k β Functor.compose (p k)) (Ξ» k β Functor.compose (q k))
      compose = helperβ² F.compose G.compose (Ξ» k β Functor.compose (p k)) (Ξ» k β Functor.compose (q k)) r Ξ» i j f β Fβ f i j

private
  variable
    o h : Level
    π π : Category o h

isFaithful : (F : Functor π π) β Type _
isFaithful {π = π} F = β {A B} (f g : π.Hom A B) β F.β f β‘ F.β g β f β‘ g
  where
    module F = Functor F
    module π = Category.Category π
