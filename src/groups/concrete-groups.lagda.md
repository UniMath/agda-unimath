---
title: Formalisation of the Symmetry Book
---

```agda
{-# OPTIONS --without-K --exact-split #-}

module groups.concrete-groups where

open import foundation.1-types using (Id-Set)
open import foundation.connected-types using (is-path-connected)
open import foundation.dependent-pair-types using (Σ; pr1; pr2; pair)
open import foundation.equivalences using (_≃_; map-inv-equiv)
open import foundation.identity-types using (Id; refl)
open import foundation.mere-equality using (mere-eq)
open import foundation.propositional-truncations using
  ( apply-universal-property-trunc-Prop)
open import foundation.propositions using (UU-Prop; type-Prop)
open import foundation.sets using (is-set; UU-Set; is-set-Prop)
open import foundation.subuniverses using (UU-Trunc)
open import foundation.truncated-types using (is-trunc)
open import foundation.truncation-levels using (one-𝕋)
open import foundation.universe-levels using (UU; Level; _⊔_; lsuc)
open import groups.abstract-groups using (Group; type-hom-Group)
open import groups.higher-groups using
  ( ∞-Group; type-∞-Group; classifying-pointed-type-∞-Group;
    classifying-type-∞-Group; shape-∞-Group;
    is-path-connected-classifying-type-∞-Group;
    mere-eq-classifying-type-∞-Group;
    elim-prop-classifying-type-∞-Group;
    unit-∞-Group; mul-∞-Group; assoc-mul-∞-Group;
    left-unit-law-mul-∞-Group; right-unit-law-mul-∞-Group;
    coherence-unit-laws-mul-∞-Group; inv-∞-Group;
    left-inverse-law-mul-∞-Group; right-inverse-law-mul-∞-Group;
    hom-∞-Group; classifying-map-hom-∞-Group;
    preserves-point-classifying-map-hom-∞-Group;
    map-hom-∞-Group; preserves-unit-map-hom-∞-Group;
    preserves-mul-map-hom-∞-Group; preserves-inv-map-hom-∞-Group;
    htpy-hom-∞-Group; extensionality-hom-∞-Group;
    id-hom-∞-Group; comp-hom-∞-Group; assoc-comp-hom-∞-Group;
    left-unit-law-comp-hom-∞-Group; right-unit-law-comp-hom-∞-Group)
open import synthetic-homotopy-theory.pointed-types using (Pointed-Type)

Concrete-Group : (l : Level) → UU (lsuc l)
Concrete-Group l = Σ (∞-Group l) (λ G → is-set (type-∞-Group G))

module _
  {l : Level} (G : Concrete-Group l)
  where

  ∞-group-Concrete-Group : ∞-Group l
  ∞-group-Concrete-Group = pr1 G

  classifying-pointed-type-Concrete-Group : Pointed-Type l
  classifying-pointed-type-Concrete-Group =
    classifying-pointed-type-∞-Group ∞-group-Concrete-Group

  classifying-type-Concrete-Group : UU l
  classifying-type-Concrete-Group =
    classifying-type-∞-Group ∞-group-Concrete-Group

  shape-Concrete-Group : classifying-type-Concrete-Group
  shape-Concrete-Group =
    shape-∞-Group ∞-group-Concrete-Group

  is-path-connected-classifying-type-Concrete-Group :
    is-path-connected classifying-type-Concrete-Group
  is-path-connected-classifying-type-Concrete-Group =
    is-path-connected-classifying-type-∞-Group ∞-group-Concrete-Group

  mere-eq-classifying-type-Concrete-Group :
    (X Y : classifying-type-Concrete-Group) → mere-eq X Y
  mere-eq-classifying-type-Concrete-Group =
    mere-eq-classifying-type-∞-Group ∞-group-Concrete-Group

  elim-prop-classifying-type-Concrete-Group :
    {l2 : Level} (P : classifying-type-Concrete-Group → UU-Prop l2) →
    type-Prop (P shape-Concrete-Group) →
    ((X : classifying-type-Concrete-Group) → type-Prop (P X))
  elim-prop-classifying-type-Concrete-Group =
    elim-prop-classifying-type-∞-Group ∞-group-Concrete-Group

  type-Concrete-Group : UU l
  type-Concrete-Group = type-∞-Group ∞-group-Concrete-Group

  is-set-type-Concrete-Group : is-set type-Concrete-Group
  is-set-type-Concrete-Group = pr2 G

  set-Concrete-Group : UU-Set l
  set-Concrete-Group = pair type-Concrete-Group is-set-type-Concrete-Group

  is-1-type-classifying-type-Concrete-Group :
    is-trunc one-𝕋 classifying-type-Concrete-Group
  is-1-type-classifying-type-Concrete-Group X Y =
    apply-universal-property-trunc-Prop
      ( mere-eq-classifying-type-Concrete-Group shape-Concrete-Group X)
      ( is-set-Prop (Id X Y))
      ( λ { refl →
            apply-universal-property-trunc-Prop
              ( mere-eq-classifying-type-Concrete-Group shape-Concrete-Group Y)
              ( is-set-Prop (Id shape-Concrete-Group Y))
              ( λ { refl → is-set-type-Concrete-Group})})

  classifying-1-type-Concrete-Group : UU-Trunc one-𝕋 l
  classifying-1-type-Concrete-Group =
    pair
      classifying-type-Concrete-Group
      is-1-type-classifying-type-Concrete-Group

  Id-BG-Set :
    (X Y : classifying-type-Concrete-Group) → UU-Set l
  Id-BG-Set X Y = Id-Set classifying-1-type-Concrete-Group X Y

  unit-Concrete-Group : type-Concrete-Group
  unit-Concrete-Group = unit-∞-Group ∞-group-Concrete-Group

  mul-Concrete-Group : (x y : type-Concrete-Group) → type-Concrete-Group
  mul-Concrete-Group = mul-∞-Group ∞-group-Concrete-Group

  assoc-mul-Concrete-Group :
    (x y z : type-Concrete-Group) →
    Id (mul-Concrete-Group (mul-Concrete-Group x y) z)
       (mul-Concrete-Group x (mul-Concrete-Group y z))
  assoc-mul-Concrete-Group = assoc-mul-∞-Group ∞-group-Concrete-Group

  left-unit-law-mul-Concrete-Group :
    (x : type-Concrete-Group) → Id (mul-Concrete-Group unit-Concrete-Group x) x
  left-unit-law-mul-Concrete-Group =
    left-unit-law-mul-∞-Group ∞-group-Concrete-Group

  right-unit-law-mul-Concrete-Group :
    (y : type-Concrete-Group) → Id (mul-Concrete-Group y unit-Concrete-Group) y
  right-unit-law-mul-Concrete-Group =
    right-unit-law-mul-∞-Group ∞-group-Concrete-Group

  coherence-unit-laws-mul-Concrete-Group :
    Id ( left-unit-law-mul-Concrete-Group unit-Concrete-Group)
       ( right-unit-law-mul-Concrete-Group unit-Concrete-Group)
  coherence-unit-laws-mul-Concrete-Group =
    coherence-unit-laws-mul-∞-Group ∞-group-Concrete-Group

  inv-Concrete-Group : type-Concrete-Group → type-Concrete-Group
  inv-Concrete-Group = inv-∞-Group ∞-group-Concrete-Group

  left-inverse-law-mul-Concrete-Group :
    (x : type-Concrete-Group) →
    Id (mul-Concrete-Group (inv-Concrete-Group x) x) unit-Concrete-Group
  left-inverse-law-mul-Concrete-Group =
    left-inverse-law-mul-∞-Group ∞-group-Concrete-Group

  right-inverse-law-mul-Concrete-Group :
    (x : type-Concrete-Group) →
    Id (mul-Concrete-Group x (inv-Concrete-Group x)) unit-Concrete-Group
  right-inverse-law-mul-Concrete-Group =
    right-inverse-law-mul-∞-Group ∞-group-Concrete-Group

  abstract-group-Concrete-Group : Group l
  abstract-group-Concrete-Group =
    pair
      ( pair
        ( set-Concrete-Group)
        ( pair
          mul-Concrete-Group
          assoc-mul-Concrete-Group))
      ( pair
        ( pair
          ( unit-Concrete-Group)
          ( pair
            left-unit-law-mul-Concrete-Group
            right-unit-law-mul-Concrete-Group))
        ( pair
          ( inv-Concrete-Group)
          ( pair
            left-inverse-law-mul-Concrete-Group
            right-inverse-law-mul-Concrete-Group)))

module _
  {l1 l2 : Level} (G : Concrete-Group l1) (H : Concrete-Group l2)
  where

  hom-Concrete-Group : UU (l1 ⊔ l2)
  hom-Concrete-Group =
    hom-∞-Group (∞-group-Concrete-Group G) (∞-group-Concrete-Group H)

{-
  is-set-hom-Concrete-Group : is-set hom-Concrete-Group
  is-set-hom-Concrete-Group = {!!}

  hom-Concrete-Group-Set : UU-Set (l1 ⊔ l2)
  hom-Concrete-Group-Set = pair hom-Concrete-Group is-set-hom-Concrete-Group
-}

  classifying-map-hom-Concrete-Group :
    hom-Concrete-Group →
    classifying-type-Concrete-Group G → classifying-type-Concrete-Group H
  classifying-map-hom-Concrete-Group =
    classifying-map-hom-∞-Group
      ( ∞-group-Concrete-Group G)
      ( ∞-group-Concrete-Group H)

  preserves-point-classifying-map-hom-Concrete-Group :
    (f : hom-Concrete-Group) →
    Id ( classifying-map-hom-Concrete-Group f (shape-Concrete-Group G))
       ( shape-Concrete-Group H)
  preserves-point-classifying-map-hom-Concrete-Group =
    preserves-point-classifying-map-hom-∞-Group
      ( ∞-group-Concrete-Group G)
      ( ∞-group-Concrete-Group H)

  map-hom-Concrete-Group :
    hom-Concrete-Group → type-Concrete-Group G → type-Concrete-Group H
  map-hom-Concrete-Group =
    map-hom-∞-Group
      ( ∞-group-Concrete-Group G)
      ( ∞-group-Concrete-Group H)

  preserves-unit-map-hom-Concrete-Group :
    (f : hom-Concrete-Group) →
    Id ( map-hom-Concrete-Group f (unit-Concrete-Group G))
       ( unit-Concrete-Group H)
  preserves-unit-map-hom-Concrete-Group =
    preserves-unit-map-hom-∞-Group
      ( ∞-group-Concrete-Group G)
      ( ∞-group-Concrete-Group H)

  preserves-mul-map-hom-Concrete-Group :
    (f : hom-Concrete-Group) (x y : type-Concrete-Group G) →
    Id ( map-hom-Concrete-Group f (mul-Concrete-Group G x y))
       ( mul-Concrete-Group H
         ( map-hom-Concrete-Group f x)
         ( map-hom-Concrete-Group f y))
  preserves-mul-map-hom-Concrete-Group =
    preserves-mul-map-hom-∞-Group
      ( ∞-group-Concrete-Group G)
      ( ∞-group-Concrete-Group H)

  preserves-inv-map-hom-Concrete-Group :
    (f : hom-Concrete-Group) (x : type-Concrete-Group G) →
    Id ( map-hom-Concrete-Group f (inv-Concrete-Group G x))
       ( inv-Concrete-Group H (map-hom-Concrete-Group f x))
  preserves-inv-map-hom-Concrete-Group =
    preserves-inv-map-hom-∞-Group
      ( ∞-group-Concrete-Group G)
      ( ∞-group-Concrete-Group H)

  hom-group-hom-Concrete-Group :
    hom-Concrete-Group →
    type-hom-Group
      ( abstract-group-Concrete-Group G)
      ( abstract-group-Concrete-Group H)
  hom-group-hom-Concrete-Group f =
    pair (map-hom-Concrete-Group f) (preserves-mul-map-hom-Concrete-Group f)

-- Homotopies of morphisms of concrete groups

module _
  {l1 l2 : Level} (G : Concrete-Group l1) (H : Concrete-Group l2)
  (f : hom-Concrete-Group G H)
  where

  htpy-hom-Concrete-Group :
    (g : hom-Concrete-Group G H) → UU (l1 ⊔ l2)
  htpy-hom-Concrete-Group =
    htpy-hom-∞-Group
      ( ∞-group-Concrete-Group G)
      ( ∞-group-Concrete-Group H)
      ( f)

  extensionality-hom-Concrete-Group :
    (g : hom-Concrete-Group G H) → Id f g ≃ htpy-hom-Concrete-Group g
  extensionality-hom-Concrete-Group =
    extensionality-hom-∞-Group
      ( ∞-group-Concrete-Group G)
      ( ∞-group-Concrete-Group H)
      ( f)

  eq-htpy-hom-Concrete-Group :
    (g : hom-Concrete-Group G H) → (htpy-hom-Concrete-Group g) → Id f g
  eq-htpy-hom-Concrete-Group g = map-inv-equiv (extensionality-hom-Concrete-Group g)

-- Category structure on concrete groups

id-hom-Concrete-Group : {l : Level} (G : Concrete-Group l) → hom-Concrete-Group G G
id-hom-Concrete-Group G = id-hom-∞-Group ( ∞-group-Concrete-Group G)

comp-hom-Concrete-Group : {l1 l2 l3 : Level}
  (G : Concrete-Group l1) (H : Concrete-Group l2) (K : Concrete-Group l3) →
  hom-Concrete-Group H K → hom-Concrete-Group G H → hom-Concrete-Group G K
comp-hom-Concrete-Group G H K =
  comp-hom-∞-Group
    ( ∞-group-Concrete-Group G)
    ( ∞-group-Concrete-Group H)
    ( ∞-group-Concrete-Group K)

assoc-comp-hom-Concrete-Group : {l1 l2 l3 l4 : Level}
  (G : Concrete-Group l1) (H : Concrete-Group l2)
  (K : Concrete-Group l3) (L : Concrete-Group l4)
  (h : hom-Concrete-Group K L) (g : hom-Concrete-Group H K)
  (f : hom-Concrete-Group G H) →
  htpy-hom-Concrete-Group G L
    ( comp-hom-Concrete-Group G H L (comp-hom-Concrete-Group H K L h g) f)
    ( comp-hom-Concrete-Group G K L h (comp-hom-Concrete-Group G H K g f))
assoc-comp-hom-Concrete-Group G H K L =
  assoc-comp-hom-∞-Group
    ( ∞-group-Concrete-Group G)
    ( ∞-group-Concrete-Group H)
    ( ∞-group-Concrete-Group K)
    ( ∞-group-Concrete-Group L)

module _
  {l1 l2 : Level} (G : Concrete-Group l1) (H : Concrete-Group l2)
  where

  left-unit-law-comp-hom-Concrete-Group :
    (f : hom-Concrete-Group G H) →
    htpy-hom-Concrete-Group G H
      ( comp-hom-Concrete-Group G H H (id-hom-Concrete-Group H) f)
      ( f)
  left-unit-law-comp-hom-Concrete-Group =
    left-unit-law-comp-hom-∞-Group
      ( ∞-group-Concrete-Group G)
      ( ∞-group-Concrete-Group H)

  right-unit-law-comp-hom-Concrete-Group :
    (f : hom-Concrete-Group G H) →
    htpy-hom-Concrete-Group G H
      ( comp-hom-Concrete-Group G G H f (id-hom-Concrete-Group G))
      ( f)
  right-unit-law-comp-hom-Concrete-Group =
    right-unit-law-comp-hom-∞-Group
      ( ∞-group-Concrete-Group G)
      ( ∞-group-Concrete-Group H)

{-
instance
  Concrete-Group-Large-Precat : Large-Precat lsuc (λ l1 l2 → l1 ⊔ l2)
  obj-Large-Precat Concrete-Group-Large-Precat = Concrete-Group
  hom-Large-Precat Concrete-Group-Large-Precat = hom-Concrete-Group-Set
  comp-hom-Large-Precat Concrete-Group-Large-Precat {X = G} {Y = H} {Z = K} =
    comp-hom-Concrete-Group G H K
  id-hom-Large-Precat Concrete-Group-Large-Precat {X = G} = id-hom-Concrete-Group G
  associative-comp-hom-Large-Precat Concrete-Group-Large-Precat {X = G} {Y = H} {Z = K} {W = L} h g f =
    eq-htpy-hom-Concrete-Group G L _ _ (assoc-comp-hom-Concrete-Group G H K L h g f) 
  left-unit-law-comp-hom-Large-Precat Concrete-Group-Large-Precat {X = G} {Y = H} f =
    eq-htpy-hom-Concrete-Group G H _ _ (left-unit-law-comp-hom-Concrete-Group G H f)
  right-unit-law-comp-hom-Large-Precat Concrete-Group-Large-Precat {X = G} {Y = H} f =
    eq-htpy-hom-Concrete-Group G H _ _ (right-unit-law-comp-hom-Concrete-Group G H f)
-}
```
