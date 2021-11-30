---
title: Formalisation of the Symmetry Book
---

```agda
{-# OPTIONS --without-K --exact-split #-}

module groups.concrete-groups where

open import groups.higher-groups public
open import groups.abstract-groups public

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
    hom-Group
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

  refl-htpy-hom-Concrete-Group : htpy-hom-Concrete-Group f
  refl-htpy-hom-Concrete-Group =
    refl-htpy-hom-∞-Group
      ( ∞-group-Concrete-Group G)
      ( ∞-group-Concrete-Group H)
      ( f)

  htpy-eq-hom-Concrete-Group :
    (g : hom-Concrete-Group G H) → Id f g → htpy-hom-Concrete-Group g
  htpy-eq-hom-Concrete-Group =
    htpy-eq-hom-∞-Group
      ( ∞-group-Concrete-Group G)
      ( ∞-group-Concrete-Group H)
      ( f)

  is-contr-total-htpy-hom-Concrete-Group :
    is-contr (Σ (hom-Concrete-Group G H) htpy-hom-Concrete-Group)
  is-contr-total-htpy-hom-Concrete-Group =
    is-contr-total-htpy-hom-∞-Group
      ( ∞-group-Concrete-Group G)
      ( ∞-group-Concrete-Group H)
      ( f)

  is-equiv-htpy-eq-hom-Concrete-Group :
    (g : hom-Concrete-Group G H) → is-equiv (htpy-eq-hom-Concrete-Group g)
  is-equiv-htpy-eq-hom-Concrete-Group =
    is-equiv-htpy-eq-hom-∞-Group
      ( ∞-group-Concrete-Group G)
      ( ∞-group-Concrete-Group H)
      ( f)

  eq-htpy-hom-Concrete-Group :
    (g : hom-Concrete-Group G H) → (htpy-hom-Concrete-Group g) → Id f g
  eq-htpy-hom-Concrete-Group =
    eq-htpy-hom-∞-Group
      ( ∞-group-Concrete-Group G)
      ( ∞-group-Concrete-Group H)
      ( f)

-- Category structure on concrete groups

module _
  {l : Level} (G : Concrete-Group l)
  where
  
  id-hom-Concrete-Group : hom-Concrete-Group G G
  id-hom-Concrete-Group =
    id-hom-∞-Group ( ∞-group-Concrete-Group G)

module _
  {l1 l2 l3 : Level} (G : Concrete-Group l1) (H : Concrete-Group l2)
  (K : Concrete-Group l3)
  where

  comp-hom-Concrete-Group :
    hom-Concrete-Group H K → hom-Concrete-Group G H → hom-Concrete-Group G K
  comp-hom-Concrete-Group =
    comp-hom-∞-Group
      ( ∞-group-Concrete-Group G)
      ( ∞-group-Concrete-Group H)
      ( ∞-group-Concrete-Group K)

module _
  {l1 l2 l3 l4 : Level}
  (G : Concrete-Group l1) (H : Concrete-Group l2) (K : Concrete-Group l3)
  (L : Concrete-Group l4)
  where

  assoc-comp-hom-Concrete-Group :
    (h : hom-Concrete-Group K L) (g : hom-Concrete-Group H K)
    (f : hom-Concrete-Group G H) →
    htpy-hom-Concrete-Group G L
      ( comp-hom-Concrete-Group G H L (comp-hom-Concrete-Group H K L h g) f)
      ( comp-hom-Concrete-Group G K L h (comp-hom-Concrete-Group G H K g f))
  assoc-comp-hom-Concrete-Group =
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

-- Proving proposition of the classifying type of a goup need only to be checked on the shape.

module _
 {ℓ : Level} (G : Concrete-Group ℓ)
 where

 private BG = classifying-type-Concrete-Group G
 private shG = shape-Concrete-Group G

 prop-on-classifying-type-Concrete-Group :
   {ℓ' : Level} (P : BG → UU-Prop ℓ') → (type-Prop (P shG)) → ((z : BG) → type-Prop (P z))
 prop-on-classifying-type-Concrete-Group P proof-P-shG z =
   apply-universal-property-trunc-Prop
     (mere-eq-classifying-type-Concrete-Group G shG z)
     (P z)
     (λ p → tr (λ x → type-Prop (P x)) p proof-P-shG)
```
