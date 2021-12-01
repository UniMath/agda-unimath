---
title: Formalisation of the Symmetry Book
---

```agda
{-# OPTIONS --without-K --exact-split --allow-unsolved-metas #-}

module groups.higher-groups where

open import foundations.pointed-maps public

∞-Group : (l : Level) → UU (lsuc l)
∞-Group l = Σ (Pointed-Type l) (λ X → is-path-connected (type-Pointed-Type X))

module _
  {l : Level} (G : ∞-Group l)
  where

  classifying-pointed-type-∞-Group : Pointed-Type l
  classifying-pointed-type-∞-Group = pr1 G

  classifying-type-∞-Group : UU l
  classifying-type-∞-Group =
    type-Pointed-Type classifying-pointed-type-∞-Group

  shape-∞-Group : classifying-type-∞-Group
  shape-∞-Group =
    pt-Pointed-Type classifying-pointed-type-∞-Group

  is-path-connected-classifying-type-∞-Group :
    is-path-connected classifying-type-∞-Group
  is-path-connected-classifying-type-∞-Group = pr2 G

  mere-eq-classifying-type-∞-Group :
    (X Y : classifying-type-∞-Group) → mere-eq X Y
  mere-eq-classifying-type-∞-Group =
    mere-eq-is-path-connected
      is-path-connected-classifying-type-∞-Group

  elim-prop-classifying-type-∞-Group :
    {l2 : Level} (P : classifying-type-∞-Group → UU-Prop l2) →
    type-Prop (P shape-∞-Group) →
    ((X : classifying-type-∞-Group) → type-Prop (P X))
  elim-prop-classifying-type-∞-Group =
    apply-dependent-universal-property-is-path-connected
      shape-∞-Group
      is-path-connected-classifying-type-∞-Group

  type-∞-Group : UU l
  type-∞-Group = type-Ω classifying-pointed-type-∞-Group

  unit-∞-Group : type-∞-Group
  unit-∞-Group = refl-Ω classifying-pointed-type-∞-Group

  mul-∞-Group : (x y : type-∞-Group) → type-∞-Group
  mul-∞-Group = mul-Ω classifying-pointed-type-∞-Group

  assoc-mul-∞-Group :
    (x y z : type-∞-Group) →
    Id (mul-∞-Group (mul-∞-Group x y) z)
       (mul-∞-Group x (mul-∞-Group y z))
  assoc-mul-∞-Group = associative-mul-Ω classifying-pointed-type-∞-Group

  left-unit-law-mul-∞-Group :
    (x : type-∞-Group) → Id (mul-∞-Group unit-∞-Group x) x
  left-unit-law-mul-∞-Group =
    left-unit-law-mul-Ω classifying-pointed-type-∞-Group

  right-unit-law-mul-∞-Group :
    (y : type-∞-Group) → Id (mul-∞-Group y unit-∞-Group) y
  right-unit-law-mul-∞-Group =
    right-unit-law-mul-Ω classifying-pointed-type-∞-Group

  coherence-unit-laws-mul-∞-Group :
    Id ( left-unit-law-mul-∞-Group unit-∞-Group)
       ( right-unit-law-mul-∞-Group unit-∞-Group)
  coherence-unit-laws-mul-∞-Group = refl

  inv-∞-Group : type-∞-Group → type-∞-Group
  inv-∞-Group = inv-Ω classifying-pointed-type-∞-Group

  left-inverse-law-mul-∞-Group :
    (x : type-∞-Group) → Id (mul-∞-Group (inv-∞-Group x) x) unit-∞-Group
  left-inverse-law-mul-∞-Group =
    left-inverse-law-mul-Ω classifying-pointed-type-∞-Group

  right-inverse-law-mul-∞-Group :
    (x : type-∞-Group) → Id (mul-∞-Group x (inv-∞-Group x)) unit-∞-Group
  right-inverse-law-mul-∞-Group =
    right-inverse-law-mul-Ω classifying-pointed-type-∞-Group

module _
  {l1 l2 : Level} (G : ∞-Group l1) (H : ∞-Group l2)
  where

  hom-∞-Group : UU (l1 ⊔ l2)
  hom-∞-Group =
    classifying-pointed-type-∞-Group G →* classifying-pointed-type-∞-Group H

  classifying-map-hom-∞-Group :
    hom-∞-Group → classifying-type-∞-Group G → classifying-type-∞-Group H
  classifying-map-hom-∞-Group =
    map-pointed-map
      ( classifying-pointed-type-∞-Group G)
      ( classifying-pointed-type-∞-Group H)

  preserves-point-classifying-map-hom-∞-Group :
    (f : hom-∞-Group) →
    Id (classifying-map-hom-∞-Group f (shape-∞-Group G)) (shape-∞-Group H)
  preserves-point-classifying-map-hom-∞-Group =
    preserves-point-map-pointed-map
      ( classifying-pointed-type-∞-Group G)
      ( classifying-pointed-type-∞-Group H)

  map-hom-∞-Group : hom-∞-Group → type-∞-Group G → type-∞-Group H
  map-hom-∞-Group =
    map-Ω
      ( classifying-pointed-type-∞-Group G)
      ( classifying-pointed-type-∞-Group H)

  preserves-unit-map-hom-∞-Group :
    (f : hom-∞-Group) → Id (map-hom-∞-Group f (unit-∞-Group G)) (unit-∞-Group H)
  preserves-unit-map-hom-∞-Group =
    preserves-refl-map-Ω
      ( classifying-pointed-type-∞-Group G)
      ( classifying-pointed-type-∞-Group H)

  preserves-mul-map-hom-∞-Group :
    (f : hom-∞-Group) (x y : type-∞-Group G) →
    Id ( map-hom-∞-Group f (mul-∞-Group G x y))
       ( mul-∞-Group H (map-hom-∞-Group f x) (map-hom-∞-Group f y))
  preserves-mul-map-hom-∞-Group =
    preserves-mul-map-Ω
      ( classifying-pointed-type-∞-Group G)
      ( classifying-pointed-type-∞-Group H)

  preserves-inv-map-hom-∞-Group :
    (f : hom-∞-Group) (x : type-∞-Group G) →
    Id ( map-hom-∞-Group f (inv-∞-Group G x))
       ( inv-∞-Group H (map-hom-∞-Group f x))
  preserves-inv-map-hom-∞-Group =
    preserves-inv-map-Ω
      ( classifying-pointed-type-∞-Group G)
      ( classifying-pointed-type-∞-Group H)

-- Homotopies of morphisms of ∞-groups

module _
  {l1 l2 : Level} (G : ∞-Group l1) (H : ∞-Group l2) (f : hom-∞-Group G H)
  where

  htpy-hom-∞-Group :
    (g : hom-∞-Group G H) → UU (l1 ⊔ l2)
  htpy-hom-∞-Group =
    htpy-pointed-map
      ( classifying-pointed-type-∞-Group G)
      ( classifying-pointed-type-∞-Group H)
      ( f)

  refl-htpy-hom-∞-Group : htpy-hom-∞-Group f
  refl-htpy-hom-∞-Group =
    refl-htpy-pointed-map
      ( classifying-pointed-type-∞-Group G)
      ( classifying-pointed-type-∞-Group H)
      ( f)

  htpy-eq-hom-∞-Group :
    (g : hom-∞-Group G H) → Id f g → htpy-hom-∞-Group g
  htpy-eq-hom-∞-Group =
    htpy-eq-pointed-map
      ( classifying-pointed-type-∞-Group G)
      ( classifying-pointed-type-∞-Group H)
      ( f)

  is-contr-total-htpy-hom-∞-Group :
    is-contr (Σ (hom-∞-Group G H) htpy-hom-∞-Group)
  is-contr-total-htpy-hom-∞-Group =
    is-contr-total-htpy-pointed-map
      ( classifying-pointed-type-∞-Group G)
      ( classifying-pointed-type-∞-Group H)
      ( f)

  is-equiv-htpy-eq-hom-∞-Group :
    (g : hom-∞-Group G H) → is-equiv (htpy-eq-hom-∞-Group g)
  is-equiv-htpy-eq-hom-∞-Group =
    is-equiv-htpy-eq-pointed-map
      ( classifying-pointed-type-∞-Group G)
      ( classifying-pointed-type-∞-Group H)
      ( f)

  eq-htpy-hom-∞-Group :
    (g : hom-∞-Group G H) → (htpy-hom-∞-Group g) → Id f g
  eq-htpy-hom-∞-Group =
    eq-htpy-pointed-map
      ( classifying-pointed-type-∞-Group G)
      ( classifying-pointed-type-∞-Group H)
      ( f)

-- Wild category structure on higher groups

module _
  {l : Level} (G : ∞-Group l)
  where
  
  id-hom-∞-Group : hom-∞-Group G G
  id-hom-∞-Group = id-pointed-map

module _
  {l1 l2 l3 : Level} (G : ∞-Group l1) (H : ∞-Group l2) (K : ∞-Group l3)
  where

  comp-hom-∞-Group :
    hom-∞-Group H K → hom-∞-Group G H → hom-∞-Group G K
  comp-hom-∞-Group =
    comp-pointed-map
      ( classifying-pointed-type-∞-Group G)
      ( classifying-pointed-type-∞-Group H)
      ( classifying-pointed-type-∞-Group K)

module _
  {l1 l2 l3 l4 : Level}
  (G : ∞-Group l1) (H : ∞-Group l2) (K : ∞-Group l3) (L : ∞-Group l4)
  where

  assoc-comp-hom-∞-Group :
    (h : hom-∞-Group K L) (g : hom-∞-Group H K) (f : hom-∞-Group G H) →
    htpy-hom-∞-Group G L
      ( comp-hom-∞-Group G H L (comp-hom-∞-Group H K L h g) f)
      ( comp-hom-∞-Group G K L h (comp-hom-∞-Group G H K g f))
  assoc-comp-hom-∞-Group =
    assoc-comp-pointed-map
      ( classifying-pointed-type-∞-Group G)
      ( classifying-pointed-type-∞-Group H)
      ( classifying-pointed-type-∞-Group K)
      ( classifying-pointed-type-∞-Group L)

module _
  {l1 l2 : Level} (G : ∞-Group l1) (H : ∞-Group l2)
  where

  left-unit-law-comp-hom-∞-Group :
    (f : hom-∞-Group G H) →
    htpy-hom-∞-Group G H (comp-hom-∞-Group G H H (id-hom-∞-Group H) f) f
  left-unit-law-comp-hom-∞-Group =
    left-unit-law-comp-pointed-map
      ( classifying-pointed-type-∞-Group G)
      ( classifying-pointed-type-∞-Group H)

  right-unit-law-comp-hom-∞-Group :
    (f : hom-∞-Group G H) →
    htpy-hom-∞-Group G H (comp-hom-∞-Group G G H f (id-hom-∞-Group G)) f
  right-unit-law-comp-hom-∞-Group =
    right-unit-law-comp-pointed-map
      ( classifying-pointed-type-∞-Group G)
      ( classifying-pointed-type-∞-Group H)
```
