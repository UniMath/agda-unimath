# Homomorphisms of concrete groups

```agda
module group-theory.homomorphisms-concrete-groups where
```

<details><summary>Imports</summary>

```agda
open import foundation.0-connected-types
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.identity-types
open import foundation.sets
open import foundation.truncation-levels
open import foundation.universe-levels

open import group-theory.concrete-groups
open import group-theory.homomorphisms-groups

open import higher-group-theory.homomorphisms-higher-groups
```

</details>

```agda
module _
  {l1 l2 : Level} (G : Concrete-Group l1) (H : Concrete-Group l2)
  where

  hom-Concrete-Group : UU (l1 ⊔ l2)
  hom-Concrete-Group =
    hom-∞-Group (∞-group-Concrete-Group G) (∞-group-Concrete-Group H)

  is-set-hom-Concrete-Group : is-set hom-Concrete-Group
  is-set-hom-Concrete-Group =
    is-trunc-map-ev-point-is-connected
      ( zero-𝕋)
      ( shape-Concrete-Group G)
      ( is-0-connected-classifying-type-Concrete-Group G)
      ( is-1-type-classifying-type-Concrete-Group H)
      ( shape-Concrete-Group H)

  hom-set-Concrete-Group : Set (l1 ⊔ l2)
  pr1 hom-set-Concrete-Group = hom-Concrete-Group
  pr2 hom-set-Concrete-Group = is-set-hom-Concrete-Group

  classifying-map-hom-Concrete-Group :
    hom-Concrete-Group →
    classifying-type-Concrete-Group G → classifying-type-Concrete-Group H
  classifying-map-hom-Concrete-Group =
    classifying-map-hom-∞-Group
      ( ∞-group-Concrete-Group G)
      ( ∞-group-Concrete-Group H)

  preserves-point-classifying-map-hom-Concrete-Group :
    (f : hom-Concrete-Group) →
    Id
      ( classifying-map-hom-Concrete-Group f (shape-Concrete-Group G))
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
    Id
      ( map-hom-Concrete-Group f (unit-Concrete-Group G))
      ( unit-Concrete-Group H)
  preserves-unit-map-hom-Concrete-Group =
    preserves-unit-map-hom-∞-Group
      ( ∞-group-Concrete-Group G)
      ( ∞-group-Concrete-Group H)

  preserves-mul-map-hom-Concrete-Group :
    (f : hom-Concrete-Group) {x y : type-Concrete-Group G} →
    Id
      ( map-hom-Concrete-Group f (mul-Concrete-Group G x y))
      ( mul-Concrete-Group H
        ( map-hom-Concrete-Group f x)
        ( map-hom-Concrete-Group f y))
  preserves-mul-map-hom-Concrete-Group =
    preserves-mul-map-hom-∞-Group
      ( ∞-group-Concrete-Group G)
      ( ∞-group-Concrete-Group H)

  preserves-inv-map-hom-Concrete-Group :
    (f : hom-Concrete-Group) (x : type-Concrete-Group G) →
    Id
      ( map-hom-Concrete-Group f (inv-Concrete-Group G x))
      ( inv-Concrete-Group H (map-hom-Concrete-Group f x))
  preserves-inv-map-hom-Concrete-Group =
    preserves-inv-map-hom-∞-Group
      ( ∞-group-Concrete-Group G)
      ( ∞-group-Concrete-Group H)

  hom-group-hom-Concrete-Group :
    hom-Concrete-Group →
    hom-Group
      ( group-Concrete-Group G)
      ( group-Concrete-Group H)
  hom-group-hom-Concrete-Group f =
    pair (map-hom-Concrete-Group f) (preserves-mul-map-hom-Concrete-Group f)
```

### Homotopies of morphisms of concrete groups

```agda
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
  eq-htpy-hom-Concrete-Group g =
    map-inv-equiv (extensionality-hom-Concrete-Group g)
```

```agda
id-hom-Concrete-Group :
  {l : Level} (G : Concrete-Group l) → hom-Concrete-Group G G
id-hom-Concrete-Group G = id-hom-∞-Group ( ∞-group-Concrete-Group G)

comp-hom-Concrete-Group :
  {l1 l2 l3 : Level}
  (G : Concrete-Group l1) (H : Concrete-Group l2) (K : Concrete-Group l3) →
  hom-Concrete-Group H K → hom-Concrete-Group G H → hom-Concrete-Group G K
comp-hom-Concrete-Group G H K =
  comp-hom-∞-Group
    ( ∞-group-Concrete-Group G)
    ( ∞-group-Concrete-Group H)
    ( ∞-group-Concrete-Group K)

associative-comp-hom-Concrete-Group :
  {l1 l2 l3 l4 : Level}
  (G : Concrete-Group l1) (H : Concrete-Group l2)
  (K : Concrete-Group l3) (L : Concrete-Group l4)
  (h : hom-Concrete-Group K L) (g : hom-Concrete-Group H K)
  (f : hom-Concrete-Group G H) →
  htpy-hom-Concrete-Group G L
    ( comp-hom-Concrete-Group G H L (comp-hom-Concrete-Group H K L h g) f)
    ( comp-hom-Concrete-Group G K L h (comp-hom-Concrete-Group G H K g f))
associative-comp-hom-Concrete-Group G H K L =
  associative-comp-hom-∞-Group
    ( ∞-group-Concrete-Group G)
    ( ∞-group-Concrete-Group H)
    ( ∞-group-Concrete-Group K)
    ( ∞-group-Concrete-Group L)

inv-associative-comp-hom-Concrete-Group :
  {l1 l2 l3 l4 : Level}
  (G : Concrete-Group l1) (H : Concrete-Group l2)
  (K : Concrete-Group l3) (L : Concrete-Group l4)
  (h : hom-Concrete-Group K L) (g : hom-Concrete-Group H K)
  (f : hom-Concrete-Group G H) →
  htpy-hom-Concrete-Group G L
    ( comp-hom-Concrete-Group G K L h (comp-hom-Concrete-Group G H K g f))
    ( comp-hom-Concrete-Group G H L (comp-hom-Concrete-Group H K L h g) f)
inv-associative-comp-hom-Concrete-Group G H K L =
  inv-associative-comp-hom-∞-Group
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
```
