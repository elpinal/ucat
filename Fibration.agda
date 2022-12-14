module Fibration where

open import Cubical.Core.Everything
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Transport
open import Cubical.Foundations.HLevels

open import Category
open import Displayed

module _ {o h} {ð : Category o h} {oâ hâ} (ð : Displayed ð oâ hâ) where
  private
    module ð = Category.Category ð
    module ð = Displayed.Displayed ð

  record Factorization {A B} {f : ð [ A , B ]} {X Y} (fâ² : ð.Hom f X Y) {C} (g : ð [ C , A ]) {Z : ð.Ob C} (hâ² : ð.Hom (ð [ f â g ]) Z Y) : Type hâ where
    field
      gâ² : ð.Hom g Z X
      factorize : fâ² ð.â gâ² â¡ hâ²
      unique : â gâ³ â fâ² ð.â gâ³ â¡ hâ² â gâ² â¡ gâ³

    uniqueâ : â gâ gâ â fâ² ð.â gâ â¡ hâ² â fâ² ð.â gâ â¡ hâ² â gâ â¡ gâ
    uniqueâ gâ gâ p q = sym (unique gâ p) â unique gâ q

  record isCartesian {A B} {f : ð [ A , B ]} {X Y} (fâ² : ð.Hom f X Y) : Type (â-max o (â-max h (â-max oâ hâ))) where
    field
      univ-prop : â {C} (g : ð [ C , A ]) {Z : ð.Ob C} (hâ² : ð.Hom (ð [ f â g ]) Z Y) â Factorization fâ² g hâ²

  record cartesianLift {A B} (f : ð [ A , B ]) (Y : ð.Ob B) : Type (â-max o (â-max h (â-max oâ hâ))) where
    field
      X : ð.Ob A
      fâ² : ð.Hom f X Y
      is-cartesian : isCartesian fâ²

  record Cleaving : Type (â-max o (â-max h (â-max oâ hâ))) where
    field
      cartesian-lift : â {A B} (f : ð [ A , B ]) (Y : ð.Ob B) â cartesianLift f Y

  isPropFactorization : â {A B} {f : ð [ A , B ]}
    {X Y} {fâ² : ð.Hom f X Y}
    {C} {g : ð [ C , A ]}
    {Z} {hâ² : ð.Hom (ð [ f â g ]) Z Y}
    â isProp (Factorization fâ² g hâ²)
  isPropFactorization {fâ² = fâ²} {hâ² = hâ²} F G i = record
    { gâ² = F.unique G.gâ² G.factorize i
    ; factorize = p i
    ; unique = Î» gâ³ x â q gâ³ x i
    }
    where
      module F = Factorization F
      module G = Factorization G

      p : PathP (Î» i â fâ² ð.â F.unique G.gâ² G.factorize i â¡ hâ²) F.factorize G.factorize
      p = toPathP (ð.isSetHom _ _ _ _)

      q : â gâ³ x â PathP (Î» i â F.unique G.gâ² G.factorize i â¡ gâ³) (F.unique gâ³ x) (G.unique gâ³ x)
      q gâ³ x = toPathP (ð.isSetHom _ _ _ _)

  isPropIsCartesian : â {A B} {f : ð [ A , B ]}
    {X Y} {fâ² : ð.Hom f X Y}
    â isProp (isCartesian fâ²)
  isPropIsCartesian x y i .isCartesian.univ-prop =
    isPropÎ  (Î» g â isPropImplicitÎ  Î» Z â isPropÎ  Î» hâ² â isPropFactorization)
      (isCartesian.univ-prop x)
      (isCartesian.univ-prop y)
      i

  module CartesianLiftUnique {A B} (f : ð [ A , B ]) (Y : ð.Ob B) (L : cartesianLift f Y) (Lâ² : cartesianLift f Y) where
    private
      module L = cartesianLift L
      module Lâ² = cartesianLift Lâ²

    c : Factorization L.fâ² ð.id (subst (Î» x â ð.Hom x _ _) (sym ð.identÊ³) Lâ².fâ²)
    c = isCartesian.univ-prop L.is-cartesian ð.id (subst (Î» x â ð.Hom x _ _) (sym ð.identÊ³) Lâ².fâ²)

    k : ð.Hom ð.id Lâ².X L.X
    k = Factorization.gâ² c


    câ² : Factorization Lâ².fâ² ð.id (subst (Î» x â ð.Hom x _ _) (sym ð.identÊ³) L.fâ²)
    câ² = isCartesian.univ-prop Lâ².is-cartesian ð.id (subst (Î» x â ð.Hom x _ _) (sym ð.identÊ³) L.fâ²)

    kâ² : ð.Hom ð.id L.X Lâ².X
    kâ² = Factorization.gâ² câ²


    t1 : L.fâ² ð.â k â¡ transport (Î» i â ð.Hom (ð.identÊ³ {f = f} (~ i)) Lâ².X Y) Lâ².fâ²
    t1 = Factorization.factorize c

    t2 : Lâ².fâ² ð.â kâ² â¡ transport (Î» i â ð.Hom (ð.identÊ³ {f = f} (~ i)) L.X Y) L.fâ²
    t2 = Factorization.factorize câ²


    u : (Lâ².fâ² ð.â subst (Î» x â ð.Hom x Lâ².X Lâ².X) ð.identË¡ (kâ² ð.â k))
      â¡ subst (Î» x â ð.Hom x Lâ².X Y) (sym ð.identÊ³) Lâ².fâ²
    u =
        (Lâ².fâ² ð.â subst (Î» x â ð.Hom x Lâ².X Lâ².X) ð.identË¡ (kâ² ð.â k))
      â¡â¨ hoist-substÊ³ ð ð.identË¡ â©
        subst (Î» x â ð.Hom x Lâ².X Y) (cong (f ð.â_) ð.identË¡) (Lâ².fâ² ð.â (kâ² ð.â k))
      â¡â¨ cong (subst (Î» x â ð.Hom x Lâ².X Y) (cong (f ð.â_) ð.identË¡)) (sym (fromPathP ð.assoc)) â©
        subst (Î» x â ð.Hom x Lâ².X Y) (cong (f ð.â_) ð.identË¡) (subst (Î» x â ð.Hom x Lâ².X Y) ð.assoc ((Lâ².fâ² ð.â kâ²) ð.â k))
      â¡â¨ sym (substComposite (Î» x â ð.Hom x Lâ².X Y) _ _ _ ) â©
        subst (Î» x â ð.Hom x Lâ².X Y) (ð.assoc â cong (f ð.â_) ð.identË¡) ((Lâ².fâ² ð.â kâ²) ð.â k)
      â¡â¨ cong
           (Î» y â
              subst (Î» x â ð.Hom x Lâ².X Y) (ð.assoc â cong (f ð.â_) ð.identË¡)
              (y ð.â k))
           t2 â©
        subst (Î» x â ð.Hom x Lâ².X Y) (ð.assoc â cong (f ð.â_) ð.identË¡) ((subst (Î» x â ð.Hom x L.X Y) (sym ð.identÊ³) L.fâ²) ð.â k)
      â¡â¨ cong
           (subst (Î» x â ð.Hom x Lâ².X Y) (ð.assoc â cong (f ð.â_) ð.identË¡)) (hoist-substË¡ ð _) â©
        subst (Î» x â ð.Hom x Lâ².X Y) (ð.assoc â cong (f ð.â_) ð.identË¡) (subst (Î» x â ð.Hom x Lâ².X Y) (cong (ð._â ð.id) (sym ð.identÊ³)) (L.fâ² ð.â k))
      â¡â¨ sym (substComposite (Î» x â ð.Hom x Lâ².X Y) _ _ _) â©
        subst (Î» x â ð.Hom x Lâ².X Y) ((cong (ð._â ð.id) (sym ð.identÊ³)) â (ð.assoc â cong (f ð.â_) ð.identË¡)) (L.fâ² ð.â k)
      â¡â¨ cong (Î» y â subst (Î» x â ð.Hom x Lâ².X Y) y (L.fâ² ð.â k)) (ð.isSetHom _ _ _ _) â©
        subst (Î» x â ð.Hom x Lâ².X Y) refl (L.fâ² ð.â k)
      â¡â¨ transportRefl _ â©
        L.fâ² ð.â k
      â¡â¨ t1 â©
        subst (Î» x â ð.Hom x Lâ².X Y) (sym ð.identÊ³) Lâ².fâ²
      â

    v : (L.fâ² ð.â subst (Î» x â ð.Hom x L.X L.X) ð.identÊ³ (k ð.â kâ²))
      â¡ subst (Î» x â ð.Hom x L.X Y) (sym ð.identÊ³) L.fâ²
    v =
        (L.fâ² ð.â subst (Î» x â ð.Hom x L.X L.X) ð.identÊ³ (k ð.â kâ²))
      â¡â¨ hoist-substÊ³ ð ð.identÊ³ â©
        subst (Î» x â ð.Hom x L.X Y) (cong (f ð.â_) ð.identÊ³) (L.fâ² ð.â (k ð.â kâ²))
      â¡â¨ cong (subst (Î» x â ð.Hom x L.X Y) (cong (f ð.â_) ð.identÊ³)) (sym (fromPathP ð.assoc)) â©
        subst (Î» x â ð.Hom x L.X Y) (cong (f ð.â_) ð.identÊ³) (subst (Î» x â ð.Hom x L.X Y) ð.assoc ((L.fâ² ð.â k) ð.â kâ²))
      â¡â¨ sym (substComposite (Î» x â ð.Hom x L.X Y) _ _ _) â©
        subst (Î» x â ð.Hom x L.X Y) (ð.assoc â cong (f ð.â_) ð.identÊ³) ((L.fâ² ð.â k) ð.â kâ²)
      â¡â¨ cong
           (Î» y â
              subst (Î» x â ð.Hom x L.X Y) (ð.assoc â cong (f ð.â_) ð.identÊ³)
              (y ð.â kâ²))
           t1 â©
        subst (Î» x â ð.Hom x L.X Y) (ð.assoc â cong (f ð.â_) ð.identÊ³) ((subst (Î» x â ð.Hom x Lâ².X Y) (sym ð.identÊ³) Lâ².fâ²) ð.â kâ²)
      â¡â¨ cong
           (subst (Î» x â ð.Hom x L.X Y) (ð.assoc â cong (f ð.â_) ð.identÊ³)) (hoist-substË¡ ð (sym ð.identÊ³)) â©
        subst (Î» x â ð.Hom x L.X Y) (ð.assoc â cong (f ð.â_) ð.identÊ³) (subst (Î» x â ð.Hom x L.X Y) (cong (ð._â ð.id) (sym ð.identÊ³)) (Lâ².fâ² ð.â kâ²))
      â¡â¨ sym (substComposite (Î» x â ð.Hom x L.X Y) _ _ _) â©
        subst (Î» x â ð.Hom x L.X Y) ((cong (ð._â ð.id) (sym ð.identÊ³)) â (ð.assoc â cong (f ð.â_) ð.identÊ³)) (Lâ².fâ² ð.â kâ²)
      â¡â¨ cong (Î» y â subst (Î» x â ð.Hom x L.X Y) y (Lâ².fâ² ð.â kâ²)) (ð.isSetHom _ _ _ _) â©
        subst (Î» x â ð.Hom x L.X Y) refl (Lâ².fâ² ð.â kâ²)
      â¡â¨ transportRefl _ â©
        Lâ².fâ² ð.â kâ²
      â¡â¨ t2 â©
        subst (Î» x â ð.Hom x L.X Y) (sym ð.identÊ³) L.fâ²
      â


    cc : Factorization Lâ².fâ² ð.id (subst (Î» x â ð.Hom x _ _) (sym ð.identÊ³) Lâ².fâ²)
    cc = isCartesian.univ-prop Lâ².is-cartesian ð.id (subst (Î» x â ð.Hom x _ _) (sym ð.identÊ³) Lâ².fâ²)

    p : subst (Î» x â ð.Hom x Lâ².X Lâ².X) (isIso.isoË¡ (Iso.is-iso (isoId ð))) (kâ² ð.â k) â¡ ð.id
    p = Factorization.uniqueâ cc (subst (Î» x â ð.Hom x Lâ².X Lâ².X) (isIso.isoË¡ (Iso.is-iso (isoId ð))) (kâ² ð.â k)) ð.id
      u
      (sym (fromPathP (symP (ð.identÊ³))))

    ccâ² : Factorization L.fâ² ð.id (subst (Î» x â ð.Hom x _ _) (sym ð.identÊ³) L.fâ²)
    ccâ² = isCartesian.univ-prop L.is-cartesian ð.id (subst (Î» x â ð.Hom x _ _) (sym ð.identÊ³) L.fâ²)

    q : subst (Î» x â ð.Hom x L.X L.X) (isIso.isoÊ³ (Iso.is-iso (isoId ð))) (k ð.â kâ²) â¡ ð.id
    q = Factorization.uniqueâ ccâ² (subst (Î» x â ð.Hom x L.X L.X) (isIso.isoÊ³ (Iso.is-iso (isoId ð))) (k ð.â kâ²)) ð.id
      v
      (sym (fromPathP (symP (ð.identÊ³))))

    cartesianLiftDomainVertIso : VertIso ð L.X Lâ².X
    cartesianLiftDomainVertIso = record { fâ² = kâ² ; is-disp-iso = record { inv = k ; isoË¡ = toPathP p ; isoÊ³ = toPathP q } }

    cartesianLiftDomainUnique : isUnivDisplayed ð â L.X â¡ Lâ².X
    cartesianLiftDomainUnique u = vertIsoToId ð u cartesianLiftDomainVertIso

    triangle : PathP (Î» i â ð.Hom (ð.identÊ³ {f = f} i) Lâ².X Y) (L.fâ² ð.â k) Lâ².fâ²
    triangle = symP {A = (Î» i â ð.Hom (ð.identÊ³ {f = f} (~ i)) Lâ².X Y)} (toPathP (sym t1))

    fâ²-unique : (u : isUnivDisplayed ð) â PathP (Î» i â ð.Hom f (cartesianLiftDomainUnique u i) Y) L.fâ² Lâ².fâ²
    fâ²-unique u = toPathP r
      where
        t : subst (Î» x â ð.Hom f x Y) (cartesianLiftDomainUnique u) L.fâ²
          â¡ subst (Î» x â ð.Hom x Lâ².X Y) ð.identÊ³ (L.fâ² ð.â DispIso.inv (idToVertIso ð (cartesianLiftDomainUnique u)))
        t = vertIsoTriangle ð {fâ² = L.fâ²} (cartesianLiftDomainUnique u)

        s : DispIso.inv (idToVertIso ð (cartesianLiftDomainUnique u)) â¡ k
        s =
            DispIso.inv (idToVertIso ð (vertIsoToId ð u cartesianLiftDomainVertIso))
          â¡â¨ cong DispIso.inv (idToVertIsoâvertIsoToIdâ¡id ð u _) â©
            DispIso.inv cartesianLiftDomainVertIso
          â¡â¨ refl â©
            k
          â

        e : subst (Î» x â ð.Hom x Lâ².X Y) ð.identÊ³ (L.fâ² ð.â DispIso.inv (idToVertIso ð (cartesianLiftDomainUnique u)))
          â¡ subst (Î» x â ð.Hom x Lâ².X Y) ð.identÊ³ (L.fâ² ð.â k)
        e = cong (subst (Î» x â ð.Hom x Lâ².X Y) ð.identÊ³) (cong (L.fâ² ð.â_) s)

        r : subst (Î» x â ð.Hom f x Y) (cartesianLiftDomainUnique u) L.fâ² â¡ Lâ².fâ²
        r = t ââ e ââ fromPathP triangle

    cartesianLiftUnique : isUnivDisplayed ð â L â¡ Lâ²
    cartesianLiftUnique u i = record
      { X = cartesianLiftDomainUnique u i
      ; fâ² = fâ²-unique u i
      ; is-cartesian = ic i
      }
      where
        ic : PathP (Î» i â isCartesian (fâ²-unique u i)) L.is-cartesian Lâ².is-cartesian
        ic = toPathP (isPropIsCartesian _ _)

  open CartesianLiftUnique using (cartesianLiftDomainVertIso; cartesianLiftDomainUnique; cartesianLiftUnique) public

  isPropCartesianLift : isUnivDisplayed ð â â {A B} (f : ð [ A , B ]) (Y : ð.Ob B) â isProp (cartesianLift f Y)
  isPropCartesianLift u f Y L Lâ² = cartesianLiftUnique f Y L Lâ² u

  isPropCleaving : isUnivDisplayed ð â isProp Cleaving
  isPropCleaving u x y i .Cleaving.cartesian-lift f Y =
    isPropCartesianLift u f Y (x.cartesian-lift f Y) (y.cartesian-lift f Y) i
    where
      module x = Cleaving x
      module y = Cleaving y

record Fibration {o h} (ð : Category.Category o h) oâ² hâ² : Type (â-suc (â-max o (â-max h (â-max oâ² hâ²)))) where
  field
    ð : Displayed ð oâ² hâ²
    cleaving : Cleaving ð
