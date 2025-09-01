# Isomorphisms of groups

```agda
module group-theory.isomorphisms-groups where
```

<details><summary>Imports</summary>

```agda
open import category-theory.isomorphisms-in-large-precategories

open import foundation.contractible-types
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.function-types
open import foundation.functoriality-dependent-pair-types
open import foundation.homotopies
open import foundation.identity-types
open import foundation.propositions
open import foundation.subtypes
open import foundation.torsorial-type-families
open import foundation.universe-levels

open import group-theory.category-of-semigroups
open import group-theory.equivalences-semigroups
open import group-theory.groups
open import group-theory.homomorphisms-groups
open import group-theory.isomorphisms-semigroups
open import group-theory.precategory-of-groups
```

</details>

## Definitions

### The predicate of being an isomorphism of groups

```agda
module _
  {l1 l2 : Level} (G : Group l1) (H : Group l2) (f : hom-Group G H)
  where

  is-iso-Group : UU (l1 ⊔ l2)
  is-iso-Group =
    is-iso-Semigroup (semigroup-Group G) (semigroup-Group H) f

  is-prop-is-iso-Group : is-prop is-iso-Group
  is-prop-is-iso-Group =
    is-prop-is-iso-Semigroup (semigroup-Group G) (semigroup-Group H) f

  is-iso-prop-Group : Prop (l1 ⊔ l2)
  is-iso-prop-Group =
    is-iso-prop-Semigroup (semigroup-Group G) (semigroup-Group H) f

  hom-inv-is-iso-Group :
    is-iso-Group → hom-Group H G
  hom-inv-is-iso-Group =
    hom-inv-is-iso-Semigroup (semigroup-Group G) (semigroup-Group H) f

  map-inv-is-iso-Group :
    is-iso-Group → type-Group H → type-Group G
  map-inv-is-iso-Group =
    map-inv-is-iso-Semigroup (semigroup-Group G) (semigroup-Group H) f

  is-section-hom-inv-is-iso-Group :
    (U : is-iso-Group) →
    comp-hom-Group H G H f (hom-inv-is-iso-Group U) ＝
    id-hom-Group H
  is-section-hom-inv-is-iso-Group =
    is-section-hom-inv-is-iso-Semigroup
      ( semigroup-Group G)
      ( semigroup-Group H)
      ( f)

  is-section-map-inv-is-iso-Group :
    (U : is-iso-Group) →
    ( map-hom-Group G H f ∘ map-inv-is-iso-Group U) ~ id
  is-section-map-inv-is-iso-Group =
    is-section-map-inv-is-iso-Semigroup
      ( semigroup-Group G)
      ( semigroup-Group H)
      ( f)

  is-retraction-hom-inv-is-iso-Group :
    (U : is-iso-Group) →
    comp-hom-Group G H G (hom-inv-is-iso-Group U) f ＝
    id-hom-Group G
  is-retraction-hom-inv-is-iso-Group =
    is-retraction-hom-inv-is-iso-Semigroup
      ( semigroup-Group G)
      ( semigroup-Group H)
      ( f)

  is-retraction-map-inv-is-iso-Group :
    (U : is-iso-Group) →
    ( map-inv-is-iso-Group U ∘ map-hom-Group G H f) ~ id
  is-retraction-map-inv-is-iso-Group =
    is-retraction-map-inv-is-iso-Semigroup
      ( semigroup-Group G)
      ( semigroup-Group H)
      ( f)
```

### The predicate of being an equivalence of groups

```agda
module _
  {l1 l2 : Level} (G : Group l1) (H : Group l2)
  where

  is-equiv-hom-Group : hom-Group G H → UU (l1 ⊔ l2)
  is-equiv-hom-Group =
    is-equiv-hom-Semigroup (semigroup-Group G) (semigroup-Group H)

  equiv-Group : UU (l1 ⊔ l2)
  equiv-Group = equiv-Semigroup (semigroup-Group G) (semigroup-Group H)
```

### Group isomorphisms

```agda
module _
  {l1 l2 : Level} (G : Group l1) (H : Group l2)
  where

  iso-Group : UU (l1 ⊔ l2)
  iso-Group = iso-Semigroup (semigroup-Group G) (semigroup-Group H)

  hom-iso-Group : iso-Group → hom-Group G H
  hom-iso-Group = hom-iso-Semigroup (semigroup-Group G) (semigroup-Group H)

  map-iso-Group : iso-Group → type-Group G → type-Group H
  map-iso-Group = map-iso-Semigroup (semigroup-Group G) (semigroup-Group H)

  preserves-mul-iso-Group :
    (f : iso-Group) {x y : type-Group G} →
    map-iso-Group f (mul-Group G x y) ＝
    mul-Group H (map-iso-Group f x) (map-iso-Group f y)
  preserves-mul-iso-Group =
    preserves-mul-iso-Semigroup (semigroup-Group G) (semigroup-Group H)

  is-iso-iso-Group :
    (f : iso-Group) → is-iso-Group G H (hom-iso-Group f)
  is-iso-iso-Group =
    is-iso-iso-Semigroup (semigroup-Group G) (semigroup-Group H)

  hom-inv-iso-Group : iso-Group → hom-Group H G
  hom-inv-iso-Group =
    hom-inv-iso-Semigroup (semigroup-Group G) (semigroup-Group H)

  map-inv-iso-Group : iso-Group → type-Group H → type-Group G
  map-inv-iso-Group =
    map-inv-iso-Semigroup (semigroup-Group G) (semigroup-Group H)

  preserves-mul-inv-iso-Group :
    (f : iso-Group) {x y : type-Group H} →
    map-inv-iso-Group f (mul-Group H x y) ＝
    mul-Group G (map-inv-iso-Group f x) (map-inv-iso-Group f y)
  preserves-mul-inv-iso-Group =
    preserves-mul-inv-iso-Semigroup (semigroup-Group G) (semigroup-Group H)

  is-section-hom-inv-iso-Group :
    (f : iso-Group) →
    comp-hom-Group H G H (hom-iso-Group f) (hom-inv-iso-Group f) ＝
    id-hom-Group H
  is-section-hom-inv-iso-Group =
    is-section-hom-inv-iso-Semigroup (semigroup-Group G) (semigroup-Group H)

  is-section-map-inv-iso-Group :
    (f : iso-Group) →
    ( map-iso-Group f ∘ map-inv-iso-Group f) ~ id
  is-section-map-inv-iso-Group =
    is-section-map-inv-iso-Semigroup (semigroup-Group G) (semigroup-Group H)

  is-retraction-hom-inv-iso-Group :
    (f : iso-Group) →
    comp-hom-Group G H G (hom-inv-iso-Group f) (hom-iso-Group f) ＝
    id-hom-Group G
  is-retraction-hom-inv-iso-Group =
    is-retraction-hom-inv-iso-Semigroup
      ( semigroup-Group G)
      ( semigroup-Group H)

  is-retraction-map-inv-iso-Group :
    (f : iso-Group) →
    ( map-inv-iso-Group f ∘ map-iso-Group f) ~ id
  is-retraction-map-inv-iso-Group =
    is-retraction-map-inv-iso-Semigroup
      ( semigroup-Group G)
      ( semigroup-Group H)

  is-iso-is-equiv-hom-Group :
    (f : hom-Group G H) → is-equiv-hom-Group G H f → is-iso-Group G H f
  is-iso-is-equiv-hom-Group =
    is-iso-is-equiv-hom-Semigroup (semigroup-Group G) (semigroup-Group H)

  is-equiv-is-iso-Group :
    (f : hom-Group G H) → is-iso-Group G H f → is-equiv-hom-Group G H f
  is-equiv-is-iso-Group =
    is-equiv-is-iso-Semigroup (semigroup-Group G) (semigroup-Group H)

  equiv-iso-equiv-Group : equiv-Group G H ≃ iso-Group
  equiv-iso-equiv-Group =
    equiv-iso-equiv-Semigroup (semigroup-Group G) (semigroup-Group H)

  iso-equiv-Group : equiv-Group G H → iso-Group
  iso-equiv-Group = map-equiv equiv-iso-equiv-Group
```

### The identity isomorphism

```agda
module _
  {l : Level} (G : Group l)
  where

  id-iso-Group : iso-Group G G
  id-iso-Group = id-iso-Large-Precategory Group-Large-Precategory {X = G}
```

## Properties

### The total space of group isomorphisms from a given group `G` is contractible

```agda
module _
  {l : Level} (G : Group l)
  where

  iso-eq-Group : (H : Group l) → Id G H → iso-Group G H
  iso-eq-Group = iso-eq-Large-Precategory Group-Large-Precategory G

  abstract
    extensionality-Group' : (H : Group l) → (G ＝ H) ≃ iso-Group G H
    extensionality-Group' H =
      ( extensionality-Semigroup (semigroup-Group G) (semigroup-Group H)) ∘e
      ( equiv-ap-inclusion-subtype is-group-prop-Semigroup {s = G} {t = H})

  abstract
    is-torsorial-iso-Group : is-torsorial (λ (H : Group l) → iso-Group G H)
    is-torsorial-iso-Group =
      is-contr-equiv'
        ( Σ (Group l) (Id G))
        ( equiv-tot extensionality-Group')
        ( is-torsorial-Id G)
```

### Group isomorphisms are stable by composition

```agda
module _
  {l1 l2 l3 : Level} (G : Group l1) (H : Group l2) (K : Group l3)
  where

  comp-iso-Group : iso-Group H K → iso-Group G H → iso-Group G K
  comp-iso-Group =
    comp-iso-Large-Precategory Group-Large-Precategory {X = G} {Y = H} {Z = K}
```

### Group isomorphisms are stable by inversion

```agda
module _
  {l1 l2 : Level} (G : Group l1) (H : Group l2)
  where

  inv-iso-Group : iso-Group G H → iso-Group H G
  inv-iso-Group =
    inv-iso-Large-Precategory Group-Large-Precategory {X = G} {Y = H}
```
