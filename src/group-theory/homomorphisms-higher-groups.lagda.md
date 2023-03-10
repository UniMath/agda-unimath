# Homomorphisms of higher groups

```agda
module group-theory.homomorphisms-higher-groups where
```

<details><summary>Imports</summary>

```agda
open import foundation.equivalences
open import foundation.identity-types
open import foundation.universe-levels

open import group-theory.higher-groups

open import structured-types.pointed-homotopies
open import structured-types.pointed-maps

open import synthetic-homotopy-theory.functoriality-loop-spaces
```

</details>

## Idea

A homomorphism of ∞-groups is a pointed map between their classifying types.

## Definition

```agda
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
    preserves-point-pointed-map
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

  extensionality-hom-∞-Group :
    (g : hom-∞-Group G H) → Id f g ≃ htpy-hom-∞-Group g
  extensionality-hom-∞-Group =
    extensionality-pointed-map
      ( classifying-pointed-type-∞-Group G)
      ( classifying-pointed-type-∞-Group H)
      ( f)

  eq-htpy-hom-∞-Group :
    (g : hom-∞-Group G H) → (htpy-hom-∞-Group g) → Id f g
  eq-htpy-hom-∞-Group g = map-inv-equiv (extensionality-hom-∞-Group g)

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
